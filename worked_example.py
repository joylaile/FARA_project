"""Replay existing MobileNetV2 interface cases; no timers or new board samples.

The engine, Direct, schema and records come from the frozen method component.
This script exposes their previously distributed outputs as one worked example.
The final local-choice rule is the paper's reporting policy, kept outside the
Boolean validator. No claim of unique causal attribution is inferred from PASS.
"""
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def encode(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()

def replay(component, output):
    wrapper = load('frozen_candidate_example', component/'experiment_candidate.py')
    exp = wrapper.experiment
    m = wrapper.modules()
    cases = [c for c in exp.interface_cases() if c['task']=='mobilenet']
    cache = {}
    trace = []
    previous_view = None
    old_checks = {}
    for case in cases:
        spec, rows = case['document']['spec'], case['document']['records']
        plan = m['engine'].compile_contract(spec)
        view = m['engine'].plan_view(plan)
        result = m['engine'].audit(plan, rows, cache)
        direct = m['direct'].explicit_audit(spec, rows, m['direct'].explicit_declaration(spec,m['core']),m['core'])
        expected = m['oracle'].checks(spec, rows)
        simple = [{k:r[k] for k in ('id','passed','dependencies')} for r in result['trace']]
        assert simple == direct['trace'] == expected
        assert result['failures'] == direct['failures']
        effect = m['direct'].effects(spec, rows, m['estimator']) if result['effect_permission'] else None
        diag = m['direct'].diagnostic(result,effect,spec,rows,m['assurance'],True)
        other = m['direct'].diagnostic(direct,effect,spec,rows,m['assurance'],True)
        assert encode(diag)==encode(other), case['id']
        interface, previous_view = exp.consumers(view,rows,simple,previous_view)
        current_checks = {c['id']:c for c in result['trace']}
        changed_keys = sorted(k for k in current_checks.keys() & old_checks.keys()
                              if current_checks[k]['key'] != old_checks[k]['key'])
        local = {'status':'NO_CHOICE_AFTER_REJECT','preferred':None}
        if effect:
            ratio = effect['summary']['WT_W']
            lo, hi = ratio['ci95']
            local = dict(status='PAIRED_LOCAL_CHOICE' if lo>1 or hi<1 else 'UNRESOLVED',
                         preferred='WT' if lo>1 else 'W' if hi<1 else None,
                         ratio=ratio,source='paper-defined reporting rule applied after PASS',
                         scope='Original-build archived within-block W/T comparison; no deployment guarantee.')
        trace.append(dict(id=case['id'],document=case['document'],
            provenance='Existing phase99 interface case; no new hardware record or timing.',
            compiled={k:view[k] for k in ('rows','pairs')},
            revision=interface['impact'],failure_field_mapping=interface['failures'],
            changed_existing_keys=changed_keys,
            evaluated=result['evaluated'],reused=result['reused'],predicates=result['predicates'],
            predicate_trace=result['trace'],diagnostic=diag,
            local_choice=local,mechanism='NO_ATTRIBUTION(coarse-request-bucket)' if effect else 'NOT_EVALUATED_AFTER_REJECT'))
        old_checks=current_checks
    first, strengthened=trace[:2]
    assert first['predicates']==1216 and strengthened['predicates']==1264
    assert len(strengthened['revision']['added'])==48
    new_checks=[r for r in strengthened['predicate_trace'] if r['id'] in strengthened['revision']['added']]
    assert len({r['key'] for r in new_checks})==1
    assert sum(not r['reused'] for r in new_checks)==1
    assert first['diagnostic']['effect']==strengthened['diagnostic']['effect']
    assert first['local_choice']['preferred']==strengthened['local_choice']['preferred']=='WT'
    invalid=next(x for x in trace if x['id'].endswith('06_two_failures'))
    assert invalid['diagnostic']['comparison']=='REJECT' and invalid['diagnostic']['effect'] is None
    assert invalid['local_choice']['preferred'] is None
    assert trace[-1]['diagnostic']['comparison']=='PASS'
    summary=dict(status='PASS',scope='Offline presentation/replay of eight existing interface cases.',
        fresh_performance_measurements=0,new_hardware_samples=0,
        archived_predicates=first['predicates'],role_revised_predicates=strengthened['predicates'],
        generated_pair_equalities=48,distinct_new_evaluations=1,complete_diagnostics_retained=48,
        unchanged_archived_effect=first['diagnostic']['effect']['summary'],
        local_choice=strengthened['local_choice'],invalid_failures=invalid['diagnostic']['failures'],
        cases=[dict(id=x['id'],comparison=x['diagnostic']['comparison'],predicates=x['predicates'],
                    evaluated=x['evaluated'],reused=x['reused'],failures=len(x['diagnostic']['failures'])) for x in trace])
    output.mkdir(parents=True,exist_ok=True)
    (output/'WORKED_TRACE.json').write_bytes(json.dumps(trace,indent=2,ensure_ascii=False,allow_nan=False).encode()+b'\n')
    (output/'WORKED_SUMMARY.json').write_bytes(json.dumps(summary,indent=2,ensure_ascii=False,allow_nan=False).encode()+b'\n')
    print('WORKED_EXAMPLE_PASS',len(trace),'existing cases; 48 added IDs; 1 new truth evaluation')
    return summary

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--component',type=Path,default=ROOT)
    parser.add_argument('--out',type=Path,default=ROOT/'replay_outputs/worked_example')
    args=parser.parse_args()
    replay(args.component.resolve(),args.out.resolve())
