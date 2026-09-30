#!/usr/bin/env python3
"""Collect the index-reduction source slice evidence using the existing mutation harness.

The helper runs the tests and gates itself. Scoped results do not replace the
historical complete mutation record. The harness keeps its normal baseline,
snapshot, compilation, named failure, and input freshness checks. The input
freshness check also covers the test and gate runs.
A Bun compiler segmentation fault can retry once with its crash log preserved.
New logs stay in a pending directory until every check passes; then they
replace the kept logs, and kept logs the new run did not write are removed.
"""
import argparse
import contextlib
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
LOGS = ROOT / 'dev/validation/index-reduction-source'
WORK_LOGS = ROOT / '.gatework/index-reduction-source-mutations'
PENDING = ROOT / '.gatework/index-reduction-source-pending'
REQUIRED = {'index-reduction-disabled', 'index-reduction-fixture-let',
            'index-reduction-fixture-beta', 'index-reduction-fixture-annotation',
            'index-reduction-fixture-projection'}
CONTROLS = {'proof-guard', 'case-head-fuel', 'case-result-fuel',
            'case-fuel', 'inline-local-type', 'inline-shape-payload',
            'inline-leg-binders', 'leg-scope-root',
            'alias-global-scope', 'alias-local-scope', 'alias-local-shift',
            'alias-opaque', 'alias-recursive', 'alias-partial'}
INDEX_SCOPED = {
    'index-alias-bound', 'index-alias-disabled', 'index-alias-equality',
    'index-alias-exhausted', 'index-alias-fixture-call',
    'index-alias-global-endpoint', 'index-alias-global-scope',
    'index-alias-local-neutral', 'index-alias-local-scope',
    'index-alias-neutral', 'index-alias-parameter-endpoint',
    'index-alias-tail', 'index-alias-width', 'index-disabled',
    'index-fixture-call', 'index-motive-missing', 'index-reduction-alias-pair',
    'index-reduction-cases', 'index-reduction-disabled',
    'index-reduction-fixture-annotation', 'index-reduction-fixture-beta',
    'index-reduction-fixture-let', 'index-reduction-fixture-projection',
    'index-reduction-free-application', 'index-reduction-fuel',
    'index-reduction-left', 'index-reduction-let-skip',
    'index-reduction-pop-skip', 'index-reduction-refund',
    'index-reduction-reset', 'index-reduction-right', 'index-reduction-short',
    'index-reduction-step-bound', 'index-result-count', 'index-result-scope',
    'index-result-tail', 'index-shape-count', 'index-shape-length',
    'index-shape-tail', 'index-shape-value', 'index-telescope-offset',
    'index-telescope-parameters', 'index-telescope-scope'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def keep_log(name, content):
    path = PENDING / name
    path.write_bytes(content)
    return {'path': str((LOGS / name).relative_to(ROOT)), 'sha256': digest(path)}


def run_check(name, command):
    start = time.monotonic()
    result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=3600)
    log = keep_log(f'{name}.log', result.stdout + result.stderr)
    if result.returncode:
        raise ValueError(f'{name}: exit={result.returncode}; see {PENDING.relative_to(ROOT)}/{name}.log')
    return {'name': name, 'command': command, 'exit_code': result.returncode,
            'elapsed_seconds': round(time.monotonic() - start, 3), 'log': log}


def run_case_with_retry(run_case, case, logs, scratch_root, snapshot):
    try:
        return run_case(case, logs, scratch_root, snapshot)
    except ValueError as error:
        name = case[0]
        if str(error) != f'{name}: build failed, not a caught behavior mutation':
            raise
        failure = (logs / (name + '-build.log')).read_bytes()
        markers = (b'Bun v', b'panic(main thread): Segmentation fault', b' js exit=-5;')
        if not all(marker in failure for marker in markers):
            raise
        crash = keep_log(name + '-bun-crash.log', failure)
        print(f'INDEX-REDUCTION-SOURCE {name}: retrying Bun compiler segmentation fault once', flush=True)
    result = run_case(case, logs, scratch_root, snapshot)
    result['compiler_retry'] = {'reason': 'Bun compiler segmentation fault', 'log': crash}
    return result


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    LOGS.mkdir(parents=True, exist_ok=True)
    shutil.rmtree(PENDING, ignore_errors=True)
    PENDING.mkdir(parents=True)
    harness = runpy.run_path(str(ROOT / 'dev/erasure-mutations.py'))
    selected = [case[0] for case in harness['CASES']
                if case[0].startswith(('index-',))
                or case[0] in REQUIRED | CONTROLS]
    missing = sorted((REQUIRED | CONTROLS) - {case[0] for case in harness['CASES']})
    if missing:
        raise ValueError(f'scoped names missing from the catalog: {missing}')
    if set(selected) != INDEX_SCOPED | REQUIRED | CONTROLS:
        unexpected = sorted(set(selected) - INDEX_SCOPED - REQUIRED - CONTROLS)
        absent = sorted((INDEX_SCOPED | REQUIRED | CONTROLS) - set(selected))
        raise ValueError(f'scoped selection changed: unexpected={unexpected}, missing={absent}')
    inputs =harness['implementation_hashes'](ROOT)
    for path in [Path(__file__).resolve(), ROOT / 'dev/bend-policy.json',
                 *sorted((ROOT / 'fixtures/erasure').glob('lambda-index-reduction-*.att'))]:
        inputs[str(path.relative_to(ROOT))] = digest(path)
    checks = [run_check('tests', ['make', 'test']),
              run_check('gates', ['zsh', '-f', 'dev/gates.sh']),
              run_check('anchors', ['python3', '-P', 'dev/erasure-mutations.py', '--check-anchors']),
              run_check('erasure-record', ['python3', '-P', 'dev/erasure-gates.py', '--record'])]
    records = []
    original_run_case = harness['run_case']
    original_run_cases = harness['run_cases']

    def collect(*arguments):
        priority = {'index-reduction-disabled': 0,
                    **{name: 1 for name in REQUIRED if name != 'index-reduction-disabled'}}
        ordered = sorted(arguments[0], key=lambda case: priority.get(case[0], 2))
        result = original_run_cases(ordered, *arguments[1:])
        records.extend(result)
        return result

    harness['main'].__globals__['run_case'] = lambda *arguments: run_case_with_retry(original_run_case, *arguments)
    harness['main'].__globals__['run_cases'] = collect
    command = ['dev/erasure-mutations.py', '--jobs', '2', '--logs', str(WORK_LOGS)]
    for name in selected:
        command += ['--case', name]
    sys.argv = command
    start = time.monotonic()
    with contextlib.redirect_stdout(io.StringIO()) as output:
        code = harness['main']()
    harness_log = keep_log('mutations.log', output.getvalue().encode())
    if code != 0 or {row['name'] for row in records} != set(selected):
        raise ValueError(f'scoped mutation run failed: exit={code}, caught={len(records)}')
    disabled_log = (WORK_LOGS / 'index-reduction-disabled.log').read_text()
    for name in ('lambda-index-reduction-let', 'lambda-index-reduction-beta',
                 'lambda-index-reduction-annotation', 'lambda-index-reduction-projection'):
        if f'INLINE-ERASE row={name} FAIL' not in disabled_log:
            raise ValueError(f'disabled index reduction did not fail its checked-core variant: {name}')
    for path, expected in inputs.items():
        if digest(ROOT / path) != expected:
            raise ValueError(f'input changed during collection: {path}')
    erasure_record = ROOT / 'dev/validation/erasure.json'
    for row in records:
        name = row['name']
        for suffix in ('.log', '-build.log'):
            source = WORK_LOGS / (name + suffix)
            evidence = keep_log(name + suffix, source.read_bytes())
            row['build_log' if suffix == '-build.log' else 'log'] = evidence
        if row['log_sha256'] != row['log']['sha256']:
            raise ValueError(f'mutant log changed: {name}')
    checks.append({'name': 'mutations', 'command': ['python3', '-P', 'dev/validation/index-reduction-source-run.py'],
                   'harness_argv': command,
                   'harness_invocation': 'in-process main() with the one-retry Bun segmentation fault run_case wrapper and the ordered run_cases collector',
                   'log': harness_log,
                   'exit_code': code, 'elapsed_seconds': round(time.monotonic() - start, 3),
                   'baseline': keep_log('mutation-baseline.log',
                       (WORK_LOGS / 'baseline.log').read_bytes())})
    record = {'version': 1, 'recorded_at': datetime.now(timezone.utc).isoformat(),
              'root': str(ROOT), 'scope': 'Bounded let, beta, annotation and projection reductions in constructor source indices; scoped mutation selection.',
              'base_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'implementation_sha256': inputs, 'checks': checks,
              'supporting_records_sha256': {str(erasure_record.relative_to(ROOT)): digest(erasure_record)},
              'catalog_total': len(harness['CASES']), 'selected': selected, 'mutations': records}
    keep = {path.name for path in PENDING.iterdir()}
    [path.unlink() for path in LOGS.iterdir() if path.name not in keep]
    for path in sorted(PENDING.iterdir()):
        shutil.copyfile(path, LOGS / path.name)
    target = ROOT / 'dev/validation/index-reduction-source.json'
    target.write_text(json.dumps(record, indent=2) + '\n')
    print(f'INDEX-REDUCTION-SOURCE recorded checks={len(checks)} caught={len(records)} total={record["catalog_total"]}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
