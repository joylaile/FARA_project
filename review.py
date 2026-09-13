"""Verify the code/data archive and replay stored results; no hardware run."""
import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: the frozen auditors use assertions.')
    parser = argparse.ArgumentParser(
        description='Verify the manifest, recalculate archived results and replay eight existing cases. Requires Python 3.12; no third-party packages or hardware.')
    parser.add_argument('--gates', action='store_true', help='also run the included software fixtures; default is stored-result replay only')
    args = parser.parse_args()
    manifest = json.loads((ROOT/'MANIFEST.json').read_text(encoding='utf-8'))
    for name, digest in manifest.items():
        path = (ROOT/name).resolve()
        if ROOT not in path.parents or sha(path) != digest:
            raise RuntimeError('Manifest mismatch: '+name)
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    command = [sys.executable, '-B', str(ROOT/'reproduce.py')]
    if args.gates:
        command.append('--gates')
    subprocess.run(command, check=True, cwd=ROOT, env=environment)
    subprocess.run([sys.executable, '-B', str(ROOT/'worked_example.py')],
                   check=True, cwd=ROOT, env=environment)
    matches = {}
    for name in ('WORKED_TRACE.json', 'WORKED_SUMMARY.json'):
        actual = ROOT/'replay_outputs/worked_example'/name
        expected = ROOT/'examples'/name
        if json.loads(actual.read_text(encoding='utf-8')) != json.loads(expected.read_text(encoding='utf-8')):
            raise RuntimeError('Worked output differs: '+name)
        matches[name] = dict(match=True, expected_sha256=sha(expected), actual_sha256=sha(actual))
    result = dict(status='PASS', package_format='code-data-only', manifest_files=len(manifest),
                  worked_outputs=matches, fresh_software_gates=args.gates,
                  new_performance_experiment=False, auxiliary_fixture_timings=args.gates,
                  auxiliary_timings_used_in_paper=False, new_hardware_acquisition=False,
                  external_delivery_verified=False)
    (ROOT/'replay_outputs/REVIEW.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print('FARA_REVIEW_PACKAGE_PASS', flush=True)


if __name__ == '__main__':
    main()
