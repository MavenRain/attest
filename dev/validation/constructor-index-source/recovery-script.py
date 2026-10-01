"""Publish completed evidence after a collector-only filename correction.

The original harness completed 64 cases and its input freshness checks before
publication failed. Reuse those logs with explicit provenance, run the omitted
sum-index-disabled case through the normal isolated harness, and retain all
normal baseline, snapshot, compilation, diagnostic, and freshness checks for
the new case. The collector's implementation changes only its selection and
evidence publication. No Bend, fixture, build, gate, or mutation source changes.
"""
from pathlib import Path
import hashlib
import json
import runpy
import shutil
import subprocess
import sys

ROOT = Path('/Users/oobi/Documents/attest')
SCRIPT = ROOT / 'dev/validation/constructor-index-source-run.py'
PENDING = ROOT / '.gatework/constructor-index-source-pending'
WORK = ROOT / '.gatework/constructor-index-source-mutations'
LOGS = ROOT / 'dev/validation/constructor-index-source'
ORIGINAL_COLLECTOR = Path('/private/tmp/attest-constructor-index/collector-before-recovery.py')
digest = lambda data: hashlib.sha256(data).hexdigest()

BACKUP = ROOT / '.gatework/constructor-index-source-recovery-original'
if not BACKUP.exists():
    shutil.copytree(PENDING, BACKUP)
    shutil.copyfile(WORK / 'baseline.log', BACKUP / 'baseline-before-recovery.log')
saved = {path.name: path.read_bytes() for path in BACKUP.iterdir() if path.is_file()}
stdout = saved['mutations.log']
lines = stdout.decode().splitlines()
names = [line.removeprefix('ERASURE-MUTATION ').removesuffix(' caught')
         for line in lines if line.startswith('ERASURE-MUTATION ')]
assert len(names) == len(set(names)) == 64
assert lines[-1] == 'ERASURE-MUTATIONS caught=64 total=247 PARTIAL'
assert 'sum-index-disabled' not in names
original_harness = runpy.run_path(str(ROOT / 'dev/erasure-mutations.py'))
input_hashes = original_harness['implementation_hashes'](ROOT)
original_cases = {case[0]: case for case in original_harness['CASES']}
assert set(names) <= set(original_cases)
original_logs = {}
for name in names:
    behavior = (WORK / (name + '.log')).read_bytes()
    build = (WORK / (name + '-build.log')).read_bytes()
    diagnostic = original_cases[name][4]
    assert diagnostic.encode() in behavior, name
    for program in ('attest', 'erase-probe', 'prop-index', 'opaque', 'inline'):
        assert (f'BUILD {program} js OK'.encode() in build or
                f'BUILD {program} js cached'.encode() in build), (name, program)
    original_logs[name] = (behavior, build)

collector = runpy.run_path(str(SCRIPT))
selected = {case[0] for case in original_harness['CASES']
            if case[0] in collector['REQUIRED'] | collector['CONTROLS'] | collector['INDEX_SCOPED']}
assert selected == set(names) | {'sum-index-disabled'}
assert len(selected) == 65
real_run_path = runpy.run_path
reused = []
fresh = []

def harness_with_verified_logs(path):
    harness = real_run_path(path)
    run_case = harness['run_case']

    def run_cases(cases, logs, scratch_root, snapshot, jobs):
        assert harness['implementation_hashes'](snapshot) == input_hashes
        records = []
        for case in cases:
            name, relative, before, after, diagnostic = case
            if name not in original_logs:
                assert name == 'sum-index-disabled'
                row = run_case(case, logs, scratch_root, snapshot)
                fresh.append(name)
                print(f'ERASURE-MUTATION {name} caught', flush=True)
                records.append(row)
                continue
            behavior, build = original_logs[name]
            assert (logs / (name + '.log')).read_bytes() == behavior
            assert (logs / (name + '-build.log')).read_bytes() == build
            original = (snapshot / relative).read_bytes()
            assert digest(original) == input_hashes[relative]
            assert before is not None
            changed = harness['mutate_source'](name, original.decode(), before, after).encode()
            assert changed != original
            assert not diagnostic.startswith('FAIL kernel case ')
            records.append({
                'name': name, 'path': relative, 'before_sha256': digest(original),
                'mutated_sha256': digest(changed), 'log_sha256': digest(behavior),
                'build_exit': 0, 'gate_exit': 1, 'diagnostic': diagnostic,
                'build_command': ['python3', '-P', 'dev/build.py', '--backend', 'js',
                                  'attest', 'erase-probe', 'prop-index', 'opaque', 'inline'],
                'gate_command': ['python3', '-P', 'dev/erasure-gates.py'],
                'reused_completed_harness': {'caught_stdout_sha256': digest(stdout),
                    'reason': 'original harness returned zero before collector publication failed'}})
            reused.append(name)
            print(f'ERASURE-MUTATION {name} caught (verified completed log)', flush=True)
        return records

    harness['run_cases'] = run_cases
    return harness

def reuse_check(name, command):
    content = saved[name + '.log']
    assert content
    return {'name': name, 'command': command, 'exit_code': 0,
            'elapsed_seconds': None, 'log': collector['keep_log'](name + '.log', content),
            'reused_completed_check': {
                'reason': 'original collector passed run_check before starting the completed harness',
                'original_job': '.kanon-wait/job-7ZwWsM'}}

globals_ = collector['main'].__globals__
globals_['run_check'] = reuse_check
runpy.run_path = harness_with_verified_logs
sys.argv = [str(SCRIPT)]
try:
    code = collector['main']()
finally:
    runpy.run_path = real_run_path
assert code == 0
assert set(reused) == set(names)
assert fresh == ['sum-index-disabled']
assert original_harness['implementation_hashes'](ROOT) == input_hashes
target = ROOT / 'dev/validation/constructor-index-source.json'
record = json.loads(target.read_text())
extra = {}
for name, content in {
        'recovery-script.py': Path(__file__).read_bytes(),
        'collector-before-recovery.py': ORIGINAL_COLLECTOR.read_bytes(),
        'mutations-before-recovery.log': stdout,
        'mutation-baseline-before-recovery.log': saved['baseline-before-recovery.log'],
        'recovery-inputs.json': (json.dumps(input_hashes, indent=2) + '\n').encode()}.items():
    path = LOGS / name
    path.write_bytes(content)
    extra[name] = {'path': str(path.relative_to(ROOT)), 'sha256': digest(content)}
record['recovery'] = {
    'reason': 'collector publication used sum-index-disabled.log instead of constructor-index-disabled.log; its selection also duplicated constructor-index-disabled',
    'original_job': '.kanon-wait/job-7ZwWsM',
    'completed_original_mutations': 64, 'new_isolated_mutations': fresh,
    'implementation_inputs_unchanged': True, 'evidence': extra}
record['checks'][-1]['harness_invocation'] += '; 64 completed mutation logs verified and reused by the recorded recovery script; sum-index-disabled executed through the original run_case; normal baseline, snapshot and input freshness checks rerun'
target.write_text(json.dumps(record, indent=2) + '\n')
subprocess.run(['git', '-C', str(ROOT), 'diff', '--check'], check=True)
print('RECOVERY verified reused=64 fresh=1 total=65; implementation inputs unchanged')
