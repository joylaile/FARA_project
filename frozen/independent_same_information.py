#!/usr/bin/env python3
"""Independent full-information factorial reference and contract conformance test.

The reference decoder and all statistics use only the standard library and do
not import FARA code. The frozen production checker is imported only in a
separate conformance arm. All mutated cases are offline test fixtures.
"""
from __future__ import annotations

import copy
import argparse
import csv
import hashlib
import importlib.util
import itertools
import json
import math
import re
import shutil
import statistics
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / 'evidence' / 'FARA_phase91_artifact'
PACKAGE = ARCHIVE / 'FARA_phase85_artifact'
OUT = ROOT / 'results'
HZ = 99_990_005.0
KEYS = ('scalar', 'request_only', 'descriptor_only', 'joint')
FLAGS = dict(zip(KEYS, ((0, 0), (1, 0), (0, 1), (1, 1))))
ORDERS = ('scalar>request_only>joint>descriptor_only',
          'request_only>descriptor_only>scalar>joint',
          'descriptor_only>joint>request_only>scalar',
          'joint>scalar>descriptor_only>request_only')
T975 = {4: 3.182446305284263, 7: 2.446911848791681, 8: 2.364624251010299}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def words(path):
    parsed = []
    for line in path.read_text(encoding='utf-8').splitlines():
        m = re.match(r'^\s*(\d+)\s+0x([0-9a-fA-F]+)', line)
        if m:
            if int(m[1]) != len(parsed):
                raise ValueError('WORD_INDEX')
            parsed.append(int(m[2], 16))
    if len(parsed) < 111:
        raise ValueError('SHORT_RECORD')
    return parsed


def u64(w, i):
    return w[i] + (w[i + 1] << 32)


def manifest(package):
    with (package / 'input/campaign_manifest.csv').open(encoding='utf-8-sig', newline='') as f:
        return list(csv.DictReader(f))


def independent_decode(package, with_contract=False):
    """Generic factorial+correctness; optional explicit W/T contract checks.

Both modes receive the same entire directory. Generic checks include ordered
paired inputs, complete four-cell blocks, record/latency hashes, successful
completion, numeric/transport errors, timing closure and Compact consistency.
    The generic arm also checks declared treatment flags, physical implementation
    identity and invariant workload/bytes. The contract extension adds agreement
    between the declared treatments and their directly observed reuse counters.
"""
    rows = manifest(package)
    if len(rows) != 32:
        raise ValueError('DESIGN_SIZE')
    decoded = []
    paired = {}
    for row in rows:
        block, pos, key = int(row['block']), int(row['position']), row['key']
        if key not in KEYS or block not in range(1, 9):
            raise ValueError('DESIGN_LABEL')
        if row['order'] != ORDERS[(block - 1) % 4]:
            raise ValueError('ORDER_LABEL')
        result, latency = (package / 'input' / row[k] for k in ('result_file', 'latency_file'))
        if digest(result) != row['result_sha256'].upper() or digest(latency) != row['latency_sha256'].upper():
            raise ValueError('RECORD_HASH')
        w = words(result)
        n = int(row['samples'])
        if w[:3] != [0x50353242, 0x52AA, 1] or w[4] != n or w[5] != n:
            raise ValueError('COMPLETION')
        if any(w[8:12]):
            raise ValueError('SEMANTIC_TRANSPORT')
        if u64(w, 69) >> 32 != 0x4650524F or u64(w, 71) <= 0:
            raise ValueError('PROFILE')
        total = u64(w, 20)
        buckets = [u64(w, k) for k in (85, 87, 89, 91, 93)]
        residual = total - sum(buckets)
        if residual < 0 or total <= 0:
            raise ValueError('TIMING')
        if 8*u64(w, 107)+16*u64(w, 109) != u64(w, 24):
            raise ValueError('COMPACT')
        record = dict(row, block=block, position=pos, samples=n,
                      total_ms=total/HZ*1000/n, rate=n*HZ/total,
                      buckets_ms=[x/HZ*1000/n for x in buckets+[residual]],
                      tasks=u64(w, 14), h2c=u64(w, 22), c2h=u64(w, 24),
                      one=u64(w, 107), two=u64(w, 109),
                      w_count=u64(w, 101), t_hits=u64(w, 103))
        if key in paired.setdefault(block, {}):
            raise ValueError('DUPLICATE_CELL')
        paired[block][key] = record
        decoded.append(record)
    if sorted(paired) != list(range(1, 9)):
        raise ValueError('BLOCKS')
    for block, cells in paired.items():
        if set(cells) != set(KEYS) or sorted(c['position'] for c in cells.values()) != [1, 2, 3, 4]:
            raise ValueError('INCOMPLETE_BLOCK')
        if len({c['sample_offset'] for c in cells.values()}) != 1 or len({c['samples'] for c in cells.values()}) != 1:
            raise ValueError('PAIRED_INPUT')
    bit_hash = digest(package / 'input/firmware/phase52_vcu108_d64_fixed.bit')
    for cells in paired.values():
        for key, c in cells.items():
            wf, tf = FLAGS[key]
            if (int(c['input_variable_reuse']), int(c['descriptor_template_reuse'])) != (wf, tf):
                raise ValueError('FACTOR_FLAGS')
            if c['bitstream_sha256'].upper() != bit_hash:
                raise ValueError('BITSTREAM')
            if with_contract and (bool(c['w_count']) != bool(wf) or bool(c['t_hits']) != bool(tf)):
                raise ValueError('CONTRACT_FACTOR_COUNTERS')
        for k in ('tasks','h2c','c2h','one','two'):
            if len({c[k] for c in cells.values()}) != 1:
                raise ValueError('WORK_TRAFFIC')
    return decoded, paired


def interval(xs, log=False):
    ys = [math.log(x) for x in xs] if log else list(xs)
    mean = statistics.fmean(ys)
    half = T975[len(ys)]*statistics.stdev(ys)/math.sqrt(len(ys))
    transform = math.exp if log else lambda x: x
    return {'n':len(ys), 'estimate':transform(mean),
            'ci95':[transform(mean-half),transform(mean+half)]}


def contrasts(paired):
    data = {k:[] for k in ('W_S','T_S','WT_S','WT_W','WT_T','interaction',
                           'conditional_T_ms','conditional_req_ms','conditional_prep_ms','additive_interaction_ms')}
    blocks = []
    for b in sorted(paired):
        s,w,t,j = [paired[b][k] for k in KEYS]
        values = {'W_S':s['total_ms']/w['total_ms'], 'T_S':s['total_ms']/t['total_ms'],
                  'WT_S':s['total_ms']/j['total_ms'], 'WT_W':w['total_ms']/j['total_ms'],
                  'WT_T':t['total_ms']/j['total_ms'],
                  'interaction':w['total_ms']*t['total_ms']/(s['total_ms']*j['total_ms']),
                  'conditional_T_ms':w['total_ms']-j['total_ms'],
                  'conditional_req_ms':w['buckets_ms'][0]-j['buckets_ms'][0],
                  'conditional_prep_ms':w['buckets_ms'][1]-j['buckets_ms'][1],
                  'additive_interaction_ms':(w['total_ms']-j['total_ms'])-(s['total_ms']-t['total_ms'])}
        for k,v in values.items(): data[k].append(v)
        blocks.append(dict(block=b, order=s['order'], input_offset=int(s['sample_offset']), **values))
    return {k:interval(v, log=not k.endswith('_ms')) for k,v in data.items()}, blocks


def call_status(fn):
    try:
        fn()
        return 'PASS', ''
    except ValueError as e:
        return 'REJECT', str(e)


def mutate(package, case):
    rows = manifest(package)
    target = rows[0]
    if case == 'clean': return
    if case == 'missing_cell': rows.pop()
    elif case == 'paired_input': target['sample_offset'] = '999'
    elif case == 'result_hash': target['result_sha256'] = '0'*64
    elif case == 'undeclared_factor': target['input_variable_reuse'] = '1'
    elif case == 'bitstream': target['bitstream_sha256'] = '0'*64
    elif case == 'order': target['order'] = 'invalid-order'
    else:
        path = package / 'input' / target['result_file']
        w = words(path)
        if case == 'semantic': w[9] = 1
        elif case == 'completion': w[5] = 2
        elif case == 'work': w[14] += 1
        elif case == 'h2c': w[22] += 128
        elif case == 'w_counter': w[101] = 1
        elif case == 't_counter': w[103] = 1
        else: raise ValueError(case)
        path.write_text(''.join(f'{i:02d} 0x{x:08X}\n' for i,x in enumerate(w)), encoding='utf-8')
        target['result_sha256'] = digest(path)
    with (package/'input/campaign_manifest.csv').open('w',encoding='utf-8',newline='') as f:
        wr=csv.DictWriter(f, fieldnames=list(rows[0])); wr.writeheader(); wr.writerows(rows)


def write_json(name, data):
    (OUT/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')


def main(package=None, output=None):
    global PACKAGE, OUT
    PACKAGE = Path(package or PACKAGE).resolve()
    OUT = Path(output or OUT).resolve()
    if OUT == PACKAGE or OUT.is_relative_to(PACKAGE):
        raise ValueError('OUTPUT_INSIDE_FROZEN_INPUT')
    OUT.mkdir(parents=True, exist_ok=True)
    nominal, paired = independent_decode(PACKAGE)
    nominal_plus, paired_plus = independent_decode(PACKAGE, with_contract=True)
    metrics, blocks = contrasts(paired)
    plus_metrics,_ = contrasts(paired_plus)
    assert metrics == plus_metrics
    spec=importlib.util.spec_from_file_location('frozen_checker_for_conformance_only',PACKAGE/'reproduce.py')
    production=importlib.util.module_from_spec(spec); spec.loader.exec_module(production)
    _, fp = production.decode_and_validate(PACKAGE)
    for b in range(1,9):
        for k in KEYS:
            assert math.isclose(paired[b][k]['total_ms'],fp[b][k]['total_ms_per_image'],abs_tol=1e-9)
    # Independent effect numbers are compared only after their computation.
    expected={'W_S':1.557548366,'T_S':1.000395109,'WT_S':1.578506091,
              'WT_W':1.013455585502615,'interaction':1.013055318}
    for k,v in expected.items(): assert abs(metrics[k]['estimate']-v)<5e-10
    result_rows=[]
    generic_rejections={'missing_cell','paired_input','result_hash','order','semantic','completion',
                        'undeclared_factor','bitstream','work','h2c'}
    cases=['clean','missing_cell','paired_input','result_hash','order','semantic','completion',
           'undeclared_factor','bitstream','work','h2c','w_counter','t_counter']
    for case in cases:
        with tempfile.TemporaryDirectory(prefix='fara92_case_') as td:
            dest=Path(td)/'package'
            shutil.copytree(PACKAGE,dest,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
            mutate(dest,case)
            generic,gr=call_status(lambda:independent_decode(dest))
            explicit,er=call_status(lambda:independent_decode(dest,True))
            fara,fr=call_status(lambda:production.decode_and_validate(dest))
            expected_generic='REJECT' if case in generic_rejections else 'PASS'
            expected_contract='PASS' if case=='clean' else 'REJECT'
            assert generic==expected_generic and explicit==fara==expected_contract,(case,generic,explicit,fara)
            result_rows.append({'case':case,'evidence':'archived' if case=='clean' else 'offline mutation',
                                'generic_full_factorial':generic,'explicit_contract_reference':explicit,
                                'fara':fara,'generic_reason':gr,'reference_reason':er,'fara_reason':fr,
                                'same_input_tree':True,'effect_in_manuscript':case=='clean'})
    write_json('same_information_comparison.json',{
        'status':'PASS','all_arms_receive_same_complete_package':True,
        'independent_decoder_and_statistics':True,'fara_import_used_only_for_conformance':True,
        'record_count':32,'block_count':8,'metrics_identical_with_explicit_contract':True,
        'nominal_selected_cell':'WT','selection_scope':'within archived build only',
        'explicit_reference_fara_agreement':f'{len(cases)}/{len(cases)}',
        'cases':result_rows,'metrics':metrics,
        'generic_common_refusals':10,'extra_treatment_counter_refusals':2,
        'interpretation':'An ordinary full factorial with correctness, pairing, flags, bitstream and work/traffic checks reproduces the effect and WT choice and rejects ten invalid cases. Explicitly adding treatment-counter predicates reproduces all thirteen tested FARA decisions. The contribution is the declared and replayable contract implementation; no unique statistical inference or superiority over a fully specified script is established.'})
    with (OUT/'same_information_cases.csv').open('w',newline='',encoding='utf-8') as f:
        wr=csv.DictWriter(f,fieldnames=list(result_rows[0])); wr.writeheader(); wr.writerows(result_rows)
    with (OUT/'paired_blocks_independent.csv').open('w',newline='',encoding='utf-8') as f:
        wr=csv.DictWriter(f,fieldnames=list(blocks[0])); wr.writeheader(); wr.writerows(blocks)
    loo=[]
    for omitted in range(1,9):
        estimate,_=contrasts({b:c for b,c in paired.items() if b!=omitted})
        loo.append(dict(omitted_block=omitted,**estimate['WT_W']))
    differences=[math.log(b['WT_W']) for b in blocks]
    obs=abs(sum(differences))
    extreme=sum(abs(sum(s*x for s,x in zip(signs,differences)))>=obs-1e-14
                for signs in itertools.product((-1,1),repeat=8))
    order_groups=[]
    for order in ORDERS:
        bs=[b for b in blocks if b['order']==order]
        order_groups.append({'order':order,'blocks':[b['block'] for b in bs],
                             'ratios':[b['WT_W'] for b in bs],
                             'geometric_mean':math.exp(statistics.fmean(math.log(b['WT_W']) for b in bs)),
                             'interpretation':'descriptive two-block group; input slice and order are not separated'})
    write_json('within_build_sensitivity.json',{
        'status':'PASS','analysis_kind':'post_hoc_archived_data_sensitivity',
        'independent_blocks':8,'new_board_data':False,
        'WT_W':metrics['WT_W'],'positive_blocks':sum(b['WT_W']>1 for b in blocks),
        'per_block_ratio_range':[min(b['WT_W'] for b in blocks),max(b['WT_W'] for b in blocks)],
        'leave_one_block_out':loo,'all_loo_lower_ci_above_one':all(x['ci95'][0]>1 for x in loo),
        'exact_sign_flip_two_sided_p':extreme/256,
        'sign_flip_assumption':'symmetric paired log differences under the null; not a preregistered randomization test',
        'order_groups':order_groups,
        'cross_build_W_vs_WT':'NOT_EVALUATED_BY_THIS_ARCHIVE_ONLY_ANALYSIS','cross_restart_W_vs_WT':'NOT_EVALUATED_BY_THIS_ARCHIVE_ONLY_ANALYSIS',
        'deployment_action':'WT_WITHIN_ARCHIVED_BUILD; REVALIDATE_AFTER_REBUILD_OR_RESTART',
        'reason':'Same-build block sensitivity cannot separate descriptor reuse from fixed binary-layout or initialization effects.'})
    # Complete board-derived input/check/output example, with raw provenance.
    c=paired[1]['request_only']; s=paired[1]['scalar']
    example={'record_id':'WT-B01-P2-W','factor':'W','paired_control':'WT-B01-P1-S',
             'raw_result':c['result_file'],'raw_result_sha256':c['result_sha256'],
             'declared_flags':{'W':1,'T':0},'fixed_coordinates':{'D':64,'B_KiB':2048,'g':4,'q':31,'partition':'P_live'},
             'allowed_changes':['builder loop order','repeated coordinate decoding','weight-read reuse','host time'],
             'fixed_observed':{'samples':3,'sample_offset':0,'requests':c['tasks'],'H2C_B':c['h2c'],'C2H_B':c['c2h'],
                               'bitstream_sha256':c['bitstream_sha256']},
             'checks':['completion','zero semantic and transport errors','paired inputs','work/traffic equal',
                       'declared factor flags','bitstream identity','W/T counter agreement'],
             'comparison':'PASS','block_ratio':s['total_ms']/c['total_ms'],
             'eight_block_effect':metrics['W_S'],'mechanism':'NOT_QUERIED',
             'interpretation':'W is the dominant observed factor on this fixed audited path',
             'not_supported':['reference-free production benefit','cross-network transfer','unique Treq sub-operation cause'],
             'human_boundary':'Author specifies intended factor/allowed changes and objective; checker cannot prove honesty or completeness of that declaration.'}
    write_json('complete_W_contract_example.json',example)
    print('PHASE92_SAME_INFORMATION=PASS cases=13 explicit_reference_agreement=13/13')
    print('PHASE92_INDEPENDENT_STATISTICS=PASS records=32 blocks=8')
    print('PHASE92_WITHIN_BUILD_SENSITIVITY=PASS')
    print('HARDWARE_ACQUISITION=NOT_PERFORMED_BY_THIS_OFFLINE_SCRIPT')
    print(json.dumps({'WT_W':metrics['WT_W'],'ratio_range':[min(b['WT_W'] for b in blocks),max(b['WT_W'] for b in blocks)],
                      'loo_lower_min':min(x['ci95'][0] for x in loo),'sign_flip_p':extreme/256}))


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=PACKAGE,
                        help='Frozen phase85 component; read only')
    parser.add_argument('--out', type=Path, default=OUT,
                        help='Generated report directory outside the component')
    args = parser.parse_args()
    main(args.package, args.out)
