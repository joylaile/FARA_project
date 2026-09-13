"""Fair post-validation interface tasks and complete validation stress tests.

All expanded/modified inputs are software fixtures, not hardware observations.
Timing and tracemalloc run separately. Frozen evaluators are never modified.
"""
from __future__ import annotations
import argparse
import ast
import copy
from datetime import datetime, timezone
import gc
import gzip
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import random
import statistics
import subprocess
import sys
import time
import tracemalloc

ROOT=Path(__file__).resolve().parents[1]
ARMS=('direct_full','fara_projection','fara_no_cache')
ORDERS=list(itertools.permutations(ARMS))
SIZES=(32,128,512,2048)
FRACTIONS=(0,1/32,1/8,1/2,1)
KINDS=('valid_response','error_word')
STAGES=('input_json','declaration','checks','effects','assurance_output')
T5=2.570581835636305

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

def encoded(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()

def sha(data): return hashlib.sha256(data).hexdigest()
def read(path): return json.loads(Path(path).read_text(encoding='utf-8'))
def write(path,value):
    path=Path(path); path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2,ensure_ascii=False,allow_nan=False)+'\n',encoding='utf-8')

def modules():
    core=load('contract_compiler',ROOT/'frozen/contract_compiler.py')
    sys.modules['contract_compiler']=core
    return dict(core=core,engine=load('fara99',ROOT/'frozen/optimized_contract.py'),
                direct=load('direct99',ROOT/'frozen/revision_benchmark.py'),
                assurance=load('assurance99',ROOT/'frozen/assurance.py'),
                estimator=load('estimator99',ROOT/'frozen/independent_same_information.py'),
                oracle=load('oracle99',ROOT/'method/independent_oracle.py'),
                de=load('de99',ROOT/'method/direct_export.py'),
                fe=load('fe99',ROOT/'method/fara_export.py'))

def source_hashes():
    files=sorted([*ROOT.glob('method/*.py'),*ROOT.glob('frozen/*.py'),*ROOT.glob('data/*.json'),ROOT/'EXPERIMENT_PROTOCOL.md'])
    return {p.relative_to(ROOT).as_posix():sha(p.read_bytes()) for p in files}

def normalize(document): return json.loads(encoded(document))

def scaled(n,fraction,kind):
    spec=read(ROOT/'data/mobilenet_spec.json'); archived=read(ROOT/'data/mobilenet_records.json')
    index={(row['block'],row['cell']):row for row in archived}
    spec['blocks']=list(range(1,n//4+1)); spec['task']='software_scaling_mobilenet_WT'
    rows=[]
    for block in spec['blocks']:
        for cell in spec['cells']:
            row=copy.deepcopy(index[(block-1)%8+1,cell])
            row['block']=block; row['sample_offset']=(block-1)*3
            rows.append(row)
    nominal=normalize(dict(spec=spec,records=rows))
    revised=copy.deepcopy(nominal)
    ordering=list(range(n)); random.Random(990017+n).shuffle(ordering)
    selected=ordering[:round(n*fraction)]
    for i in selected:
        row=revised['records'][i]
        if kind=='valid_response':
            delta=100+i
            row['ticks']+=delta; row['buckets'][0]+=delta
            row['milliseconds']=row['ticks']/row['hz']*1000/row['samples']
        else:
            row['errors'][0]=i+1
    return dict(id=f'n{n}_{kind}_changed{len(selected)}',n=n,fraction=fraction,
                kind=kind,changed_rows=len(selected),selected=selected,
                nominal=nominal,revised=revised,
                scope='Deterministic scaled software fixture; no new hardware samples.')

def cases(pilot=False):
    sizes=(32,512) if pilot else SIZES
    fractions=(0,1) if pilot else FRACTIONS
    return [scaled(n,f,k) for n in sizes for k in KINDS for f in fractions]

def effects(spec,rows,estimator):
    """Ten statistics per eight-block cohort, never pseudo-replicated board n."""
    batches=[]
    for start in range(0,len(spec['blocks']),8):
        selected=set(spec['blocks'][start:start+8]); paired={b:{} for b in sorted(selected)}
        for row in rows:
            if row['block'] in selected:
                paired[row['block']][row['cell']]=dict(total_ms=row['milliseconds'],
                    buckets_ms=[x/row['hz']*1000/row['samples'] for x in row['buckets']],
                    order='software workload; not physical acquisition order',sample_offset=row['sample_offset'])
        summary,blocks=estimator.contrasts(paired)
        batches.append(dict(cohort=start//8,summary=summary,paired_blocks=blocks))
    return dict(scope='Software calculation workload; every cohort has eight blocks, not new hardware n.',cohorts=batches)

def complete(arm,document,cache,m):
    """Identical caller-document to serialized diagnostic boundary."""
    ts=[time.perf_counter_ns()]
    parsed=normalize(document); spec,rows=parsed['spec'],parsed['records']; ts.append(time.perf_counter_ns())
    if arm=='direct_full':
        prepared=m['direct'].explicit_declaration(spec,m['core'])
    else:
        prepared=m['engine'].compile_contract(spec)
    ts.append(time.perf_counter_ns())
    if arm=='direct_full':
        result=m['direct'].explicit_audit(spec,rows,prepared,m['core'])
    else:
        result=m['engine'].audit(prepared,rows,cache)
    ts.append(time.perf_counter_ns())
    effect=effects(spec,rows,m['estimator']) if result['effect_permission'] else None
    ts.append(time.perf_counter_ns())
    diagnostic=m['direct'].diagnostic(result,effect,spec,rows,m['assurance'],True)
    blob=encoded(diagnostic); ts.append(time.perf_counter_ns())
    times={name:ts[i+1]-ts[i] for i,name in enumerate(STAGES)}
    times['total']=ts[-1]-ts[0]; assert sum(times[k] for k in STAGES)==times['total']
    return dict(blob=blob,diagnostic=diagnostic,times=times,predicates=result['predicates'],
                evaluated=result['evaluated'],reused=result['reused'],failed=len(result['failures']),
                cache_entries=len(cache) if cache is not None else 0)

def finite_gate(out,pilot=False):
    m=modules(); before=source_hashes(); reports=[]
    semantic_cases=[]
    for count in range(1,5):
        names=[f'F{i}' for i in range(count)]
        treatments=list(itertools.product((0,1),repeat=count))
        choices=[('context',[]),('response',[]),('evidence',[])]+[
            ('controlled',[names[i] for i in range(count) if mask&(1<<i)]) for mask in range(1,1<<count)]
        for role,footprint in choices:
            fields={'block':dict(role='evidence',type='int',causes=[]),'cell':dict(role='evidence',type='str',causes=[]),
                    'payload':dict(role=role,type='int',causes=footprint)}
            fields.update({f:dict(role='controlled',type='int',causes=[f]) for f in names})
            spec=dict(version=1,task='synthetic_permission_truth_table',fields=fields,
                factors={f:[0,1] for f in names},cells={f'c{i}':dict(zip(names,levels)) for i,levels in enumerate(treatments)},
                blocks=[1,2],laws=[dict(id='NONNEGATIVE',expr={'ge':[{'field':'payload'},{'const':0}]})],
                assurance='AUTHOR_DECLARED_NOT_PROVED')
            rows=[]
            for block in (1,2):
                for cell,levels in spec['cells'].items():
                    payload=0 if role=='context' else sum((1<<i)*levels[f] for i,f in enumerate(names) if role!='controlled' or f in footprint)
                    rows.append(dict(block=block,cell=cell,payload=payload,**levels))
            fixture=normalize(dict(spec=spec,rows=rows))
            spec,rows=fixture['spec'],fixture['rows']
            expected=m['oracle'].schema_inventory(spec); expected_checks=m['oracle'].checks(spec,rows)
            plan=m['engine'].compile_contract(spec); view=m['engine'].plan_view(plan)
            assert {k:view[k] for k in ('rows','pairs')}==expected
            actual=m['engine'].audit(plan,rows,None)
            assert [{k:r[k] for k in ('id','passed','dependencies')} for r in actual['trace']]==expected_checks
            direct_view=m['de'].export(spec,m['direct'],m['core'])
            assert {k:direct_view[k] for k in ('rows','pairs')}==expected
            semantic_cases.append(dict(factors=count,role=role,footprint=footprint,pairs=len(view['pairs']),predicates=len(expected_checks)))
    for case in cases(pilot):
        caches={arm:{} if arm=='fara_projection' else None for arm in ARMS}
        for step in ('nominal','revised'):
            document=case[step]; expected=m['oracle'].checks(document['spec'],document['records'])
            expected_failures=[c['id'] for c in expected if not c['passed']]
            blobs=[]
            for arm in ARMS:
                got=complete(arm,document,caches[arm],m)
                assert got['diagnostic']['checks']==expected,(case['id'],step,arm,'INDEPENDENT_CHECK_MISMATCH')
                assert got['diagnostic']['failures']==expected_failures
                assert got['diagnostic']['effect_permission']==(not expected_failures)
                blobs.append(got['blob'])
            assert blobs[0]==blobs[1]==blobs[2],(case['id'],step,'FULL_OUTPUT_MISMATCH')
            reports.append(dict(case=case['id'],step=step,predicates=len(expected),
                failures=len(expected_failures),output_sha256=sha(blobs[0]),output_bytes=len(blobs[0])))
        print('GATE',case['id'],flush=True)
    assert before==source_hashes()
    write(out/'gate.json',dict(status='PASS',pilot=pilot,sources=before,cases=reports,permission_truth_tables=semantic_cases,
        oracle_scope='Finite valid-schema semantics and explicit mutations; shared effect/assurance not independently proved.'))
    return reports

def rewrite_fields(node,old,new):
    if isinstance(node,dict):
        if set(node)=={'field'}:
            if node['field']==old:node['field']=new
        elif set(node)!={'const'}:
            for v in node.values():rewrite_fields(v,old,new)
    elif isinstance(node,list):
        for v in node:rewrite_fields(v,old,new)

def interface_cases():
    answer=[]
    for task in ('mobilenet','resnet','residency'):
        original=normalize(dict(spec=read(ROOT/f'data/{task}_spec.json'),records=read(ROOT/f'data/{task}_records.json')))
        spec,rows=copy.deepcopy(original['spec']),copy.deepcopy(original['records'])
        def add(name):answer.append(dict(id=task+'/'+name,task=task,document=normalize(dict(spec=spec,records=rows))))
        add('00_archived')
        spec['fields']['completed']['role']='context'; add('01_role')
        spec['fields']['h2c']=dict(role='response',type='int',causes=[]); add('02_response_role')
        spec['laws'][0]['expr']={'and':[copy.deepcopy(spec['laws'][0]['expr']),{'const':True}]}; add('03_expression')
        spec['fields']['generation_tag']=dict(role='evidence',type='int',causes=[])
        for row in rows:row['generation_tag']=0
        spec['laws'].append(dict(id='GENERATION_TAG',expr={'eq':[{'field':'generation_tag'},{'const':0}]})); add('04_added_law')
        spec['fields']['logical_tasks']=spec['fields'].pop('tasks')
        for row in rows:row['logical_tasks']=row.pop('tasks')
        for law in spec['laws']:rewrite_fields(law['expr'],'tasks','logical_tasks')
        add('05_renamed_field')
        rows[0]['errors'][0]=7; rows[0]['generation_tag']=1; add('06_two_failures')
        rows[0]['errors'][0]=0; rows[0]['generation_tag']=0; rows.reverse(); add('07_recovered_reordered')
    return answer

def obligation_inputs(view,records):
    """Shared consumer: semantic inputs per obligation; not a checker."""
    spec=view['spec']; index={(r['block'],r['cell']):r for r in records}; answer={}
    for (block,cell),row in sorted(index.items()):
        for factor,level in spec['cells'][cell].items():
            answer[f'{block}/{cell}/FACTOR_{factor}']=dict(expr={'factor':[factor,level]},inputs={factor:row[factor]})
        for law in view['rows']:
            answer[f'{block}/{cell}/{law["id"]}']=dict(expr=law['expr'],inputs={k:row[k] for k in law['dependencies']})
    for block in spec['blocks']:
        for pair in view['pairs']:
            a,b=index[block,pair['a']],index[block,pair['b']]
            for field in pair['fixed']:
                answer[f'{block}/{pair["a"]}:{pair["b"]}/FIXED_{field}']=dict(expr={'equal_pair':field},inputs={field:[a[field],b[field]]})
    return answer

def consumers(view,records,checks,previous=None):
    current=obligation_inputs(view,records); previous=previous or {}
    old,new=set(previous),set(current)
    failures=[dict(id=check['id'],dependencies=check['dependencies'],semantic_inputs=current[check['id']])
              for check in checks if not check['passed']]
    return dict(inventory={k:view[k] for k in ('rows','pairs')},
                impact=dict(added=sorted(new-old),retired=sorted(old-new),
                    changed=sorted(k for k in new&old if current[k]!=previous[k]),
                    unchanged=sorted(k for k in new&old if current[k]==previous[k])),
                failures=failures),current

def interface_task(case,m,arm,previous):
    start=time.perf_counter_ns()
    inp=normalize(case['document']); spec,rows=inp['spec'],inp['records']
    view=(m['fe'].export(spec,m['engine']) if arm=='fara_public' else m['de'].export(spec,m['direct'],m['core']))
    # Both receive the same already validated diagnostic as post-validation consumers.
    checks=case['checks']
    output,current=consumers(view,rows,checks,previous)
    blob=encoded(output); end=time.perf_counter_ns()
    return blob,current,end-start

def executable_lines(path):
    source=path.read_text(encoding='utf-8'); tree=ast.parse(source); excluded=set()
    for node in ast.walk(tree):
        if isinstance(node,(ast.Module,ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)) and node.body:
            first=node.body[0]
            if isinstance(first,ast.Expr) and isinstance(first.value,ast.Constant) and isinstance(first.value.value,str):
                excluded.update(range(first.lineno,first.end_lineno+1))
    return sum(bool(line.strip()) and not line.lstrip().startswith('#') and i not in excluded
               for i,line in enumerate(source.splitlines(),1))

def interface_run(out,worker):
    m=modules(); before=source_hashes(); fixtures=interface_cases(); reports=[]; outputs={}
    for case in fixtures:
        spec,rows=case['document']['spec'],case['document']['records']
        case['checks']=m['oracle'].checks(spec,rows)
        expected=m['oracle'].schema_inventory(spec)
        for arm in ('fara_public','direct_export'):
            view=(m['fe'].export(spec,m['engine']) if arm=='fara_public' else m['de'].export(spec,m['direct'],m['core']))
            assert {k:view[k] for k in ('rows','pairs')}==expected,(case['id'],arm,'INVENTORY_ORACLE')
        result=m['engine'].audit(m['engine'].compile_contract(spec),rows,None)
        assert [{k:c[k] for k in ('id','passed','dependencies')} for c in result['trace']]==case['checks']
    # Eight complete task sequences per worker, orders alternate; same warm-up in both arms.
    for iteration in range(8):
        old={a:{} for a in ('fara_public','direct_export')}
        for case in fixtures:
            order=('direct_export','fara_public') if (iteration+worker)%2 else ('fara_public','direct_export')
            for arm in order:
                previous=old[arm].get(case['task'])
                blob,current,elapsed=interface_task(case,m,arm,previous)
                old[arm][case['task']]=current
                digest=sha(blob)
                if case['id'] in outputs:assert digest==outputs[case['id']]['sha256']
                else:outputs[case['id']]=dict(sha256=digest,output=json.loads(blob))
                reports.append(dict(worker=worker,iteration=iteration,case=case['id'],arm=arm,
                                    total_ns=elapsed,output_bytes=len(blob),sha256=digest))
    assert before==source_hashes()
    write(out/'interface_observations.json',reports)
    if worker==0:write(out/'interface_outputs.json',outputs)
    write(out/'interface_worker.json',dict(status='PASS',sources=before,cases=24,observations=len(reports),
        adapters={name:dict(lines=executable_lines(ROOT/f'method/{name}.py'),
                            sha256=sha((ROOT/f'method/{name}.py').read_bytes())) for name in ('fara_export','direct_export')},
        frozen_implementation_lines={p.name:executable_lines(p) for p in (ROOT/'frozen').glob('*.py')},
        revision_specific_adapter_edits=0,scope='Post-validation inventory, impact and triage; not full checker runtime or measured developer effort.'))
    print('INTERFACE_WORKER_PASS',worker,len(reports),flush=True)

def scale_worker(out,worker,pilot=False,memory=False):
    m=modules(); before=source_hashes(); observations=[]; ordercases=cases(pilot)
    fixed_index={case['id']:i for i,case in enumerate(ordercases)}
    if memory:
        ordercases=[c for c in ordercases if c['n'] in (32,2048) and c['fraction'] in (0,1)]
    rotation=worker%len(ordercases); ordercases=ordercases[rotation:]+ordercases[:rotation]
    if worker%2:ordercases.reverse()
    for ordinal,case in enumerate(ordercases):
        expected={}
        for arm in ORDERS[(worker+fixed_index[case['id']])%6]:
            cache={} if arm=='fara_projection' else None
            if memory:gc.collect(); tracemalloc.start()
            for step in ('nominal','revised'):
                if memory:tracemalloc.reset_peak()
                result=complete(arm,case[step],cache,m)
                peak=tracemalloc.get_traced_memory()[1] if memory else None
                digest=sha(result['blob'])
                if step in expected:assert digest==expected[step],(case['id'],step,arm,'OUTPUT_MISMATCH')
                else:expected[step]=digest
                wanted='REJECT' if step=='revised' and case['kind']=='error_word' and case['changed_rows'] else 'PASS'
                assert result['diagnostic']['comparison']==wanted
                observations.append(dict(worker=worker,case=case['id'],n=case['n'],fraction=case['fraction'],
                    kind=case['kind'],changed_rows=case['changed_rows'],step=step,arm=arm,
                    output_sha256=digest,output_bytes=len(result['blob']),times=result['times'],
                    predicates=result['predicates'],evaluated=result['evaluated'],reused=result['reused'],
                    failed=result['failed'],cache_entries=result['cache_entries'],python_peak_bytes=peak))
                if worker==0 and arm=='direct_full' and not memory:
                    path=out/'outputs'/f'{case["id"]}_{step}.json.gz';path.parent.mkdir(parents=True,exist_ok=True)
                    path.write_bytes(gzip.compress(result['blob'],mtime=0))
                del result
            if memory:tracemalloc.stop()
        print('MEMORY' if memory else 'TIMING',worker,case['id'],flush=True)
    assert before==source_hashes()
    write(out/('memory_observations.json' if memory else 'scale_observations.json'),observations)
    write(out/'worker.json',dict(status='PASS',pilot=pilot,memory=memory,worker=worker,sources=before,
        python=sys.version,cpu=m['direct'].cpu_model(),started_utc=datetime.now(timezone.utc).isoformat(),
        observations=len(observations),hardware_samples=0))

def ratios(values):
    logs=[math.log(x) for x in values]; mean=statistics.fmean(logs)
    half=T5*statistics.stdev(logs)/math.sqrt(6)
    return dict(estimate=math.exp(mean),ci95=[math.exp(mean-half),math.exp(mean+half)],n_workers=6)

def summarize(out):
    scale=[]; interfaces=[]; memory=[]
    for w in range(6):
        scale+=read(out/f'worker_{w}/scale_observations.json')
        interfaces+=read(out/f'worker_{w}/interface_observations.json')
    for w in range(3):memory+=read(out/f'memory_{w}/memory_observations.json')
    groups={}
    for row in scale:groups.setdefault((row['case'],row['step']),[]).append(row)
    summary=[]
    for (case,step),rows in groups.items():
        metric=dict(case=case,step=step,n=rows[0]['n'],fraction=rows[0]['fraction'],kind=rows[0]['kind'],arms={},ratios={})
        for arm in ARMS:
            selected=[r for r in rows if r['arm']==arm]
            assert len(selected)==6
            metric['arms'][arm]=dict(mean_ms=statistics.fmean(r['times']['total']/1e6 for r in selected),
                median_ms=statistics.median(r['times']['total']/1e6 for r in selected),
                stage_mean_ms={k:statistics.fmean(r['times'][k]/1e6 for r in selected) for k in STAGES},
                predicates=selected[0]['predicates'],failed=selected[0]['failed'],
                evaluated=selected[0]['evaluated'],reused=selected[0]['reused'],
                output_bytes=selected[0]['output_bytes'],cache_entries=selected[0]['cache_entries'])
        by={(r['worker'],r['arm']):r for r in rows}
        for numerator,denominator in (('direct_full','fara_projection'),('fara_no_cache','fara_projection')):
            metric['ratios'][numerator+'/'+denominator]=ratios([by[w,numerator]['times']['total']/by[w,denominator]['times']['total'] for w in range(6)])
        summary.append(metric)
    worker_ratios=[]
    for w in range(6):
        by={arm:sum(r['total_ns'] for r in interfaces if r['worker']==w and r['arm']==arm) for arm in ('direct_export','fara_public')}
        worker_ratios.append(by['direct_export']/by['fara_public'])
    inter=dict(ratio_direct_over_fara=ratios(worker_ratios),
        mean_24_case_workflow_ms={arm:statistics.fmean(sum(r['total_ns'] for r in interfaces if r['worker']==w and r['iteration']==i and r['arm']==arm)/1e6 for w in range(6) for i in range(8)) for arm in ('direct_export','fara_public')},
        footprint=read(out/'worker_0/interface_worker.json'))
    mem=[]
    for case,step,arm in sorted({(r['case'],r['step'],r['arm']) for r in memory}):
        rows=[r for r in memory if (r['case'],r['step'],r['arm'])==(case,step,arm)]
        mem.append(dict(case=case,step=step,arm=arm,median_peak_bytes=statistics.median(r['python_peak_bytes'] for r in rows),
                        min_peak_bytes=min(r['python_peak_bytes'] for r in rows),max_peak_bytes=max(r['python_peak_bytes'] for r in rows)))
    write(out/'SUMMARY.json',dict(status='PASS',scaling=summary,interface=inter,memory=mem,
        timing_observations=len(scale),interface_observations=len(interfaces),memory_observations=len(memory),
        limitations=['Synthetic workload scaling, no new hardware evidence.','CI unit is six worker processes on one non-isolated host.',
                     'Interface adapter footprint is not measured human effort.','Memory is traced Python allocations, not process RSS.']))
    print('SUMMARY_PASS',len(scale),len(interfaces),len(memory),flush=True)

def main():
    p=argparse.ArgumentParser();p.add_argument('mode',choices=('gate','worker','memory','summarize'))
    p.add_argument('--out',type=Path,required=True);p.add_argument('--worker',type=int,default=0);p.add_argument('--pilot',action='store_true')
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    if a.mode=='gate':finite_gate(a.out,a.pilot);interface_run(a.out,a.worker)
    elif a.mode=='worker':interface_run(a.out,a.worker);scale_worker(a.out,a.worker,a.pilot)
    elif a.mode=='memory':scale_worker(a.out,a.worker,a.pilot,True)
    else:summarize(a.out)

if __name__=='__main__':main()
