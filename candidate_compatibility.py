"""Frozen/candidate byte identity, cache interoperability and ownership checks."""
import argparse
import copy
from pathlib import Path
import experiment_candidate as candidate

e=candidate.experiment

def run(out):
    old=candidate.original_modules();new=candidate.modules();cases=[]
    for fixture in e.interface_cases():
        doc=fixture['document'];spec,rows=doc['spec'],doc['records']
        od=old['direct'].explicit_audit(spec,rows,old['direct'].explicit_declaration(spec,old['core']),old['core'])
        nd=new['direct'].explicit_audit(spec,rows,new['direct'].explicit_declaration(spec,new['core']),new['core'])
        assert e.encoded(od)==e.encoded(nd),(fixture['id'],'DIRECT_IDENTITY')
        op=old['engine'].compile_contract(spec);np=new['engine'].compile_contract(spec)
        oc={};nc={}
        a=old['engine'].audit(op,rows,oc);b=new['engine'].audit(np,rows,nc)
        assert e.encoded(a)==e.encoded(b),(fixture['id'],'FARA_IDENTITY')
        assert oc==nc,(fixture['id'],'CACHE_IDENTITY')
        a2=old['engine'].audit(op,rows,nc);b2=new['engine'].audit(np,rows,oc)
        assert e.encoded(a2)==e.encoded(b2),(fixture['id'],'CROSS_CACHE')
        view_before=e.encoded(new['engine'].plan_view(np))
        target=next(t for t in b['trace'] if t['dependencies'])
        target['dependencies'].append('caller_mutation')
        assert e.encoded(new['engine'].plan_view(np))==view_before
        fresh=new['engine'].audit(np,rows,{})
        assert e.encoded(fresh)==e.encoded(old['engine'].audit(op,rows,{})),(fixture['id'],'RESULT_OWNERSHIP')
        nd['trace'][0]['dependencies'].append('caller_mutation')
        fresh_direct=new['direct'].explicit_audit(spec,rows,new['direct'].explicit_declaration(spec,new['core']),new['core'])
        assert e.encoded(fresh_direct)==e.encoded(od),(fixture['id'],'DIRECT_OWNERSHIP')
        cases.append(dict(id=fixture['id'],status='PASS',predicates=a['predicates']))
    result=dict(status='PASS',cases=cases,sources=candidate.source_hashes(),
                checks=['Direct serialized identity','FARA serialized identity','cache byte/key identity',
                        'bidirectional old/new cache interoperability','plan and future-call ownership'],
                boundary='Dependency annotations may alias within one returned result, never with an owned plan or later call.')
    e.write(out/'compatibility.json',result)
    print('CANDIDATE_COMPATIBILITY_PASS',len(cases),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);run(p.parse_args().out)
