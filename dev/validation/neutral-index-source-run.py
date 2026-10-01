#!/usr/bin/env python3
"""Collect the neutral-index source slice evidence using the existing mutation harness.

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
LOGS = ROOT / 'dev/validation/neutral-index-source'
WORK_LOGS = ROOT / '.gatework/neutral-index-source-mutations'
PENDING = ROOT / '.gatework/neutral-index-source-pending'
REQUIRED = {'neutral-index-argument', 'neutral-index-curried', 'neutral-index-disabled', 'neutral-index-fixture-left', 'neutral-index-fixture-right', 'neutral-index-fuel', 'neutral-index-head', 'neutral-index-quantity', 'neutral-index-size', 'neutral-index-step-bound'}
CONTROLS = {'alias-global-scope', 'alias-local-scope', 'alias-opaque', 'index-shape-tail', 'inline-shape-payload', 'proof-guard'}
INDEX_SCOPED = {'constructor-index-disabled', 'index-reduction-disabled', 'index-reduction-fuel', 'index-reduction-pop-skip', 'index-reduction-reset', 'index-reduction-step-bound', 'nested-index-step-bound', 'sum-index-shape'}


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
        print(f'NEUTRAL-INDEX-SOURCE {name}: retrying Bun compiler segmentation fault once', flush=True)
    result = run_case(case, logs, scratch_root, snapshot)
    result['compiler_retry'] = {'reason': 'Bun compiler segmentation fault', 'log': crash}
    return result


FIXTURES = 'erase/test/lambda_fixtures.bend'
MIGRATION = 'dev/bend-migration.json'
# The reviewed opaque fixture annotation fix as (Stage A hash, current hash) pairs.
FIXTURE_FIX = {
    FIXTURES: ('e64542579c65832c6842adb92fa29716b15b048b214610e6adb5f4ccea1c3d33',
               'bfe0fa74d7cd498dc6afd11786c478b3ec4c9d77701eb7c86b9625d43399bf60'),
    'fixtures/erasure/lambda-neutral-index-left-opaque.att':
        ('835ed0f03deafcd7c8281f36e3bbc2a4ff13bb67cf41f4d953f8cfb6c7b25e6e',
         'ff69a1924deb489b607ed3696ef2b5ad4cfc4138a7af012dc446d41a64ba669a'),
    'fixtures/erasure/lambda-neutral-index-right-opaque.att':
        ('cde43df57dc68f8579b35400cdf0a7235d3bb124eb190600197606c227214a0b',
         'b303f88711f60e398b7c1b3f07c2418a4fc78f9b79759f8e9f73c2be39103046'),
}


def stage_a_reuse(path):
    """Reuse completed Stage A only across the opaque fixture annotation fix.

    Build, carry and HOUSE checks still run on the current files. The kernel,
    frontend, benchmark corpus and every other recorded source must be unchanged.
    The fixed files must match the exact reviewed hashes before and after the fix.
    """
    receipt = json.loads(path.read_text())
    if receipt['root'] != str(ROOT) or receipt['base_revision'] != subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip():
        raise ValueError('Stage A receipt belongs to another checkout or revision')
    absent = sorted({*FIXTURE_FIX, MIGRATION} - set(receipt['source_sha256']))
    if absent:
        raise ValueError(f'Stage A receipt lacks the fixed subjects: {absent}')
    for name, expected in receipt['source_sha256'].items():
        if name in FIXTURE_FIX and (expected, digest(ROOT / name)) != FIXTURE_FIX[name]:
            raise ValueError(f'Stage A subject differs from the reviewed fixture fix: {name}')
        if name not in FIXTURE_FIX and name != MIGRATION and digest(ROOT / name) != expected:
            raise ValueError(f'Stage A subject changed: {name}')
    before, after = FIXTURE_FIX[FIXTURES]
    current = json.loads((ROOT / MIGRATION).read_text())
    if receipt['migration']['bend_sources'][FIXTURES] != before or current['bend_sources'][FIXTURES] != after:
        raise ValueError('Stage A migration fixture module hash differs from the reviewed fixture fix')
    if {**current, 'bend_sources': {**current['bend_sources'], FIXTURES: before}} != receipt['migration']:
        raise ValueError('Stage A migration changed beyond the fixture module hash')
    source = Path(receipt['log']['path'])
    if digest(source) != receipt['log']['sha256']:
        raise ValueError('Stage A log changed')
    output = source.read_bytes()
    if not output.endswith(b'STAGE-A OK\n') or b'runs=7' not in output:
        raise ValueError('Stage A receipt lacks the completed seven-run benchmark')
    log = keep_log('stage-a-reused.log', output)
    receipt['log'] = {'path': str(ROOT / log['path']), 'sha256': log['sha256']}
    evidence = keep_log('stage-a-receipt.json', (json.dumps(receipt, indent=2) + '\n').encode())
    return {'name': 'stage-a-reused', 'exit_code': 0,
            'command': ['python3', '-P', 'dev/stage-a-gates.py'],
            'log': log, 'receipt': evidence,
            'reused': True, 'changed_subjects': sorted({*FIXTURE_FIX, MIGRATION}),
            'refresh': 'Current make test, CARRY and HOUSE checks are required separately.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage-a-receipt', type=Path,
                        help='reuse completed Stage A after only the opaque fixture annotation fix; all other source hashes must match')
    args = parser.parse_args()
    LOGS.mkdir(parents=True, exist_ok=True)
    shutil.rmtree(PENDING, ignore_errors=True)
    PENDING.mkdir(parents=True)
    keep_log('.gitattributes', b'# Preserve captured process output exactly for hash verification.\n*.log whitespace=-blank-at-eof\n')
    harness = runpy.run_path(str(ROOT / 'dev/erasure-mutations.py'))
    selected = [case[0] for case in harness['CASES']
                if case[0] in INDEX_SCOPED | REQUIRED | CONTROLS]
    missing = sorted((REQUIRED | CONTROLS) - {case[0] for case in harness['CASES']})
    if missing:
        raise ValueError(f'scoped names missing from the catalog: {missing}')
    if set(selected) != INDEX_SCOPED | REQUIRED | CONTROLS:
        unexpected = sorted(set(selected) - INDEX_SCOPED - REQUIRED - CONTROLS)
        absent = sorted((INDEX_SCOPED | REQUIRED | CONTROLS) - set(selected))
        raise ValueError(f'scoped selection changed: unexpected={unexpected}, missing={absent}')
    inputs =harness['implementation_hashes'](ROOT)
    for path in [Path(__file__).resolve(), ROOT / 'dev/bend-policy.json',
                 *sorted((ROOT / 'fixtures/erasure').glob('lambda-*index-*.att'))]:
        inputs[str(path.relative_to(ROOT))] = digest(path)
    (PENDING / 'inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
    checks = [run_check('anchors', ['python3', '-P', 'dev/erasure-mutations.py', '--check-anchors']),
              run_check('tests', ['make', 'test'])]
    if args.stage_a_receipt:
        checks += [stage_a_reuse(args.stage_a_receipt),
                   run_check('carry-refresh', ['zsh', '-f', 'dev/carry-check.sh']),
                   run_check('house-refresh', ['zsh', '-f', 'dev/house.sh']),
                   run_check('erasure-gates', ['zsh', '-f', 'dev/gates.sh', 'ERASURE']),
                   run_check('lean-twin', ['zsh', '-f', 'dev/gates.sh', 'LEAN-TWIN'])]
    else:
        checks.append(run_check('gates', ['zsh', '-f', 'dev/gates.sh']))
    checks.append(run_check('erasure-record', ['python3', '-P', 'dev/erasure-gates.py', '--record']))
    (PENDING / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    records = []
    original_run_case = harness['run_case']
    original_run_cases = harness['run_cases']

    def collect(*arguments):
        priority = {'neutral-index-disabled': 0,
                    **{name: 1 for name in REQUIRED if name != 'neutral-index-disabled'}}
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
    caught = {row['name'] for row in records}
    if code != 0 or caught != set(selected):
        raise ValueError(f'scoped mutation run failed: exit={code}, caught={len(records)}, '
                         f'missing={sorted(set(selected) - caught)}, unexpected={sorted(caught - set(selected))}; '
                         f'see {PENDING.relative_to(ROOT)}/mutations.log')
    disabled_log = (WORK_LOGS / 'neutral-index-disabled.log').read_text()
    for name in ('lambda-neutral-index-left', 'lambda-neutral-index-right'):
        if f'INLINE-ERASE row={name} FAIL' not in disabled_log:
            raise ValueError(f'disabled neutral recovery did not fail its checked-core variant: {name}')
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
    checks.append({'name': 'mutations', 'command': ['python3', '-P', 'dev/validation/neutral-index-source-run.py'],
                   'harness_argv': command,
                   'harness_invocation': 'in-process main() with the one-retry Bun segmentation fault run_case wrapper and the ordered run_cases collector',
                   'log': harness_log,
                   'exit_code': code, 'elapsed_seconds': round(time.monotonic() - start, 3),
                   'baseline': keep_log('mutation-baseline.log',
                       (WORK_LOGS / 'baseline.log').read_bytes())})
    (PENDING / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    (PENDING / 'mutation-records.json').write_text(json.dumps(records, indent=2) + '\n')
    record = {'version': 1, 'recorded_at': datetime.now(timezone.utc).isoformat(),
              'root': str(ROOT), 'scope': 'Bounded neutral point application recovery in source indices with shared reduction and transition limits and a reconstruction size cap; scoped mutation selection.',
              'base_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'implementation_sha256': inputs, 'checks': checks,
              'supporting_records_sha256': {str(erasure_record.relative_to(ROOT)): digest(erasure_record)},
              'catalog_total': len(harness['CASES']), 'selected': selected, 'mutations': records}
    keep = {path.name for path in PENDING.iterdir()}
    [path.unlink() for path in LOGS.iterdir() if path.name not in keep]
    for path in sorted(PENDING.iterdir()):
        shutil.copyfile(path, LOGS / path.name)
    target = ROOT / 'dev/validation/neutral-index-source.json'
    target.write_text(json.dumps(record, indent=2) + '\n')
    print(f'NEUTRAL-INDEX-SOURCE recorded checks={len(checks)} caught={len(records)} total={record["catalog_total"]}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
