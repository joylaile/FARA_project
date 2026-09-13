"""Portable stored-result audit, optionally rerun the fresh software gates."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def run():
    p=argparse.ArgumentParser();p.add_argument('--gates',action='store_true');a=p.parse_args()
    manifest=json.loads((ROOT/'MANIFEST.json').read_text(encoding='utf-8'))
    for name,digest in manifest.items():
        path=(ROOT/name).resolve();assert ROOT in path.parents
        assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,name
    print('MANIFEST_PASS',len(manifest),flush=True)
    # Audit into a new directory so frozen numeric reports remain immutable.
    import importlib.util
    spec=importlib.util.spec_from_file_location('independent_audit',ROOT/'audit_results.py')
    audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
    reports={version:audit.audit(ROOT/f'results/{version}') for version in ('final_01','final_02')}
    out=ROOT/'replay_outputs';out.mkdir(exist_ok=True)
    if a.gates:
        for command in ([sys.executable,'-B',str(ROOT/'candidate_compatibility.py'),'--out',str(out/'compatibility')],
                        [sys.executable,'-B',str(ROOT/'experiment_candidate.py'),'gate','--out',str(out/'correctness')]):
            subprocess.run(command,check=True,cwd=ROOT)
        expected=json.loads((ROOT/'results/final_02/correctness/gate.json').read_text())
        actual=json.loads((out/'correctness/gate.json').read_text())
        assert expected==actual,'FRESH_GATE_DIFFERS'
        print('FRESH_GATE_MATCH',len(actual['cases']),len(actual['permission_truth_tables']),flush=True)
    result=dict(status='PASS',reports=reports,fresh_software_gates=a.gates,
                scope='Stored-data audit and optional fresh software fixtures; no hardware reacquisition or timing replication.')
    (out/'REPLAY.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('PHASE99_ARTIFACT_PASS',flush=True)
if __name__=='__main__':run()
