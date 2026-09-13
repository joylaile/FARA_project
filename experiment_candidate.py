"""Allocation-aware candidate; original frozen run and harness are retained."""
from pathlib import Path
import importlib.util

ROOT=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('experiment99',ROOT/'method/experiment.py')
experiment=importlib.util.module_from_spec(sp);sp.loader.exec_module(experiment)
original_modules=experiment.modules
original_hashes=experiment.source_hashes

def modules():
    m=original_modules()
    m['engine']=experiment.load('candidate99',ROOT/'candidate/optimized_contract.py')
    optimized=experiment.load('direct_optimized99',ROOT/'candidate/direct_optimized.py')
    m['direct'].explicit_audit=lambda spec,rows,deps,core:optimized.explicit_audit(spec,rows,deps,core,m['direct'])
    return m

def source_hashes():
    result=original_hashes()
    for p in sorted([*ROOT.glob('candidate/*.py'),ROOT/'experiment_candidate.py',ROOT/'CANDIDATE_PROTOCOL.md']):
        result[p.relative_to(ROOT).as_posix()]=experiment.sha(p.read_bytes())
    return result

experiment.modules=modules
experiment.source_hashes=source_hashes
if __name__=='__main__':experiment.main()
