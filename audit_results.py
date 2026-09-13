"""Independent numeric/hash audit; does not import experiment calculation code."""
import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path

def read(p):return json.loads(p.read_text(encoding='utf-8'))
def mean(xs):return sum(xs)/len(xs)
def median(xs):
    values=sorted(xs);n=len(values)
    return values[n//2] if n%2 else (values[n//2-1]+values[n//2])/2
def check(a,b):
    assert math.isclose(a,b,rel_tol=1e-11,abs_tol=1e-9),(a,b)
def ratio(values):
    logs=[math.log(v) for v in values];mu=mean(logs)
    sd=math.sqrt(sum((x-mu)**2 for x in logs)/(len(logs)-1))
    half=2.570581835636305*sd/math.sqrt(6)
    return [math.exp(mu),math.exp(mu-half),math.exp(mu+half)]

def audit(root):
    expected=read(root/'SUMMARY.json');gate=read(root/'correctness/gate.json')
    canonical={};byte_counts={};hash_checks=0;number_checks=0
    for p in (root/'worker_0/outputs').glob('*.json.gz'):
        blob=gzip.decompress(p.read_bytes());key=p.name[:-8]
        canonical[key]=hashlib.sha256(blob).hexdigest();byte_counts[key]=len(blob)
        obj=json.loads(blob)
        assert obj['predicates']==len(obj['checks'])
        assert obj['failures']==[c['id'] for c in obj['checks'] if not c['passed']]
        assert obj['effect_permission']==(len(obj['failures'])==0)
        assert (obj['effect'] is not None)==obj['effect_permission']
    assert len(canonical)==80
    for c in gate['cases']:
        assert canonical[c['case']+'_'+c['step']]==c['output_sha256']
    rows=[];inter=[];memory=[];sources=[]
    for worker in range(6):
        rows+=read(root/f'worker_{worker}/scale_observations.json')
        inter+=read(root/f'worker_{worker}/interface_observations.json')
        sources.append(read(root/f'worker_{worker}/worker.json')['sources'])
    assert all(s==gate['sources'] for s in sources)
    for worker in range(3):
        memory+=read(root/f'memory_{worker}/memory_observations.json')
    stages=('input_json','declaration','checks','effects','assurance_output')
    for r in rows+memory:
        key=r['case']+'_'+r['step'];assert canonical[key]==r['output_sha256'];hash_checks+=1
        assert byte_counts[key]==r['output_bytes']
        assert sum(r['times'][s] for s in stages)==r['times']['total']
        assert r['evaluated']+r['reused']==r['predicates']
        assert r['failed']==(r['changed_rows'] if r['kind']=='error_word' and r['step']=='revised' else 0)
        assert r['predicates']==38*r['n']
        if r['arm']!='fara_projection':assert r['reused']==0 and r['cache_entries']==0
    for s in expected['scaling']:
        current=[r for r in rows if r['case']==s['case'] and r['step']==s['step']]
        assert len(current)==18
        by={(r['worker'],r['arm']):r for r in current}
        for name,calc in s['ratios'].items():
            a,b=name.split('/');actual=ratio([by[w,a]['times']['total']/by[w,b]['times']['total'] for w in range(6)])
            for av,bv in zip(actual,[calc['estimate'],*calc['ci95']]):check(av,bv);number_checks+=1
        for arm,calc in s['arms'].items():
            selected=[r for r in current if r['arm']==arm]
            check(mean([r['times']['total']/1e6 for r in selected]),calc['mean_ms']);number_checks+=1
            check(median([r['times']['total']/1e6 for r in selected]),calc['median_ms']);number_checks+=1
            for stage in stages:check(mean([r['times'][stage]/1e6 for r in selected]),calc['stage_mean_ms'][stage]);number_checks+=1
    inter_outputs=read(root/'worker_0/interface_outputs.json')
    for r in inter:assert inter_outputs[r['case']]['sha256']==r['sha256'];hash_checks+=1
    ratios=[]
    for worker in range(6):
        totals={a:sum(r['total_ns'] for r in inter if r['worker']==worker and r['arm']==a) for a in ('direct_export','fara_public')}
        ratios.append(totals['direct_export']/totals['fara_public'])
    calc=expected['interface']['ratio_direct_over_fara']
    for a,b in zip(ratio(ratios),[calc['estimate'],*calc['ci95']]):check(a,b);number_checks+=1
    for s in expected['memory']:
        values=[r['python_peak_bytes'] for r in memory if (r['case'],r['step'],r['arm'])==(s['case'],s['step'],s['arm'])]
        assert len(values)==3
        check(median(values),s['median_peak_bytes']);check(min(values),s['min_peak_bytes']);check(max(values),s['max_peak_bytes']);number_checks+=3
    assert len(rows)==1440 and len(inter)==2304 and len(memory)==144
    return dict(status='PASS',numeric_checks=number_checks,observation_hash_checks=hash_checks,
                canonical_outputs=80,permission_truth_table_cases=len(gate['permission_truth_tables']),
                source_consistency=True,scope='Stored-data arithmetic and output consistency, not new timing or hardware certification.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);a=p.parse_args()
    result=audit(a.root);(a.root/'INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))
