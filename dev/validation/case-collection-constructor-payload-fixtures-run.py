#!/usr/bin/env python3
"""Record constructor-valued cases inside collection payload fields."""
import argparse
import contextlib
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
LOGS = ROOT / "dev/validation/case-collection-constructor-payload-fixtures"
WORK = ROOT / ".gatework/case-collection-constructor-payload-mutations"
REQUIRED = {
    f"constructor-payload-{kind}-{edit}"
    for kind in ('case-finite-tuple', 'case-finite-sum-left', 'case-finite-sum-right', 'case-constructor-tuple', 'case-constructor-sum-left', 'case-constructor-sum-right')
    for edit in ("fixture-call", "passthrough", "elimination-passthrough", "recovery-passthrough")
}
CONTROLS = {
    "constructor-payload-disabled",
    "constructor-payload-order",
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def evidence(path):
    return {"path": str(path.relative_to(ROOT)), "sha256": digest(path)}

def check(name, command):
    log = LOGS / (name + ".log")
    started = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, timeout=3600)
    row = {"name": name, "command": command, "exit_code": result.returncode,
           "log": evidence(log), "elapsed_seconds": round(time.monotonic() - started, 3)}
    if result.returncode:
        raise ValueError(f"{name}: exit={result.returncode}; see {log}")
    print(f"CASE-COLLECTION-CONSTRUCTOR-PAYLOAD-FIXTURES {name} OK", flush=True)
    return row

def run_case_with_retry(run_case, case, logs, scratch_root, snapshot):
    try:
        return run_case(case, logs, scratch_root, snapshot)
    except ValueError as error:
        name = case[0]
        if str(error) != f"{name}: build failed, not a caught behavior mutation":
            raise
        failure = (logs / (name + "-build.log")).read_bytes()
        markers = (b"Bun v", b"panic(main thread): Segmentation fault", b" js exit=-5;")
        if not all(marker in failure for marker in markers):
            raise
        crash = LOGS / (name + "-bun-crash.log")
        crash.write_bytes(failure)
        print(f"CASE-COLLECTION-CONSTRUCTOR-PAYLOAD-FIXTURES {name}: retrying Bun compiler segmentation fault once", flush=True)
    result = run_case(case, logs, scratch_root, snapshot)
    result["compiler_retry"] = {"reason": "Bun compiler segmentation fault", "log": evidence(crash)}
    return result

def reuse_checks(inputs):
    checkpoint = json.loads((LOGS / "checks.json").read_text())
    if checkpoint["validated_inputs"] != inputs:
        raise ValueError("checked implementation changed; rerun the full collector")
    checks = checkpoint["checks"]
    expected = {
        "anchors": ["python3", "-P", "dev/erasure-mutations.py", "--check-anchors"],
        "tests": ["make", "test"],
        "gates": ["zsh", "-f", "dev/gates.sh"],
        "erasure-record": ["python3", "-P", "dev/erasure-gates.py", "--record"],
    }
    if len(checks) != len(expected) or {row["name"] for row in checks} != set(expected):
        raise ValueError("incomplete passed-check checkpoint")
    for row in checks:
        if set(row) != {"name", "command", "exit_code", "log", "elapsed_seconds"}:
            raise ValueError("passed-check checkpoint row was not written by check()")
        if row["exit_code"] != 0 or row["command"] != expected[row["name"]]:
            raise ValueError("invalid passed-check checkpoint")
        if evidence(ROOT / row["log"]["path"]) != row["log"]:
            raise ValueError("passed-check log changed")
    return [dict(row, reused=True) for row in checks]

def equivalent_completed(case, saved, original_case):
    source = (ROOT / case[1]).read_bytes()
    changed = original_case.__globals__["mutate_source"](
        case[0], source.decode(), case[2], case[3]).encode()
    before_hash = hashlib.sha256(source).hexdigest()
    changed_hash = hashlib.sha256(changed).hexdigest()
    for completed in saved["cases"].values():
        recipe = completed["recipe"]
        if recipe[1:4] != list(case[1:4]):
            continue
        row = completed["record"]
        if row["name"] != recipe[0] or row["path"] != case[1] or row["diagnostic"] != recipe[4]:
            raise ValueError("equivalent mutation identity changed")
        if row["build_exit"] != 0 or row["gate_exit"] != 1:
            raise ValueError("equivalent mutation did not pass its build and fail its gate")
        if row["before_sha256"] != before_hash or row["mutated_sha256"] != changed_hash:
            raise ValueError("equivalent mutation source recipe changed")
        if row["log_sha256"] != row["log"]["sha256"]:
            raise ValueError("equivalent mutation log identity changed")
        for key in ("log", "build_log"):
            if evidence(ROOT / row[key]["path"]) != row[key]:
                raise ValueError("equivalent mutation log changed")
        output = (ROOT / row["log"]["path"]).read_text()
        if row["diagnostic"] not in output:
            raise ValueError("equivalent mutation original diagnostic changed")
        if case[4] not in output:
            continue
        return dict(row, name=case[0], diagnostic=case[4], reused=True,
                    shared_execution=row.get("shared_execution", row["name"]))
    return None

def check_reuse():
    global ROOT
    original_root = ROOT
    checks = 0
    try:
        with tempfile.TemporaryDirectory(prefix="attest-mutation-reuse-") as directory:
            ROOT = Path(directory)
            (ROOT / "source.txt").write_text("before")
            (ROOT / "gate.log").write_text("FAIL base\nFAIL alias\n")
            (ROOT / "build.log").write_text("BUILD inline js OK\n")
            recipe = ["base", "source.txt", "before", "after", "FAIL base"]
            alias = ("alias", "source.txt", "before", "after", "FAIL alias")
            row = {"name": "base", "path": "source.txt", "diagnostic": "FAIL base",
                   "build_exit": 0, "gate_exit": 1, "before_sha256": digest(ROOT / "source.txt"),
                   "mutated_sha256": hashlib.sha256(b"after").hexdigest(),
                   "log": evidence(ROOT / "gate.log"), "build_log": evidence(ROOT / "build.log"),
                   "log_sha256": digest(ROOT / "gate.log")}
            saved = {"cases": {"base": {"recipe": recipe, "record": row}}}
            mutation = SimpleNamespace(__globals__={"mutate_source": lambda name, source, before, after: source.replace(before, after)})
            reused = equivalent_completed(alias, saved, mutation)
            if reused is None or reused["name"] != "alias" or reused["shared_execution"] != "base":
                raise ValueError("identical validated mutation was not reused")
            checks += 1
            for key, value in (("name", "wrong"), ("path", "wrong"), ("diagnostic", "wrong"),
                               ("build_exit", 1), ("gate_exit", 0), ("before_sha256", "wrong"),
                               ("mutated_sha256", "wrong"), ("log_sha256", "wrong")):
                changed = json.loads(json.dumps(saved))
                changed["cases"]["base"]["record"][key] = value
                try:
                    equivalent_completed(alias, changed, mutation)
                except ValueError:
                    checks += 1
                else:
                    raise ValueError(f"invalid mutation cache accepted: {key}")
            changed = json.loads(json.dumps(saved))
            changed["cases"]["base"]["recipe"][2] = "different"
            if equivalent_completed(alias, changed, mutation) is not None:
                raise ValueError("different mutation recipe reused")
            checks += 1
            (ROOT / "gate.log").write_text("FAIL base\n")
            changed = json.loads(json.dumps(saved))
            changed["cases"]["base"]["record"]["log"] = evidence(ROOT / "gate.log")
            changed["cases"]["base"]["record"]["log_sha256"] = digest(ROOT / "gate.log")
            if equivalent_completed(alias, changed, mutation) is not None:
                raise ValueError("mutation without its named failure reused")
            checks += 1
            (ROOT / "gate.log").write_text("FAIL base\nFAIL alias\n")
            for name in ("gate.log", "build.log"):
                content = (ROOT / name).read_bytes()
                (ROOT / name).write_bytes(content + b"changed\n")
                try:
                    equivalent_completed(alias, saved, mutation)
                except ValueError:
                    checks += 1
                else:
                    raise ValueError(f"changed cache evidence accepted: {name}")
                (ROOT / name).write_bytes(content)
    finally:
        ROOT = original_root
    print(f"MUTATION-REUSE checks={checks} OK", flush=True)

def checkpoint_case(case, logs, inputs, original_case, arguments, reuse):
    path = LOGS / "completed-mutations.json"
    saved = json.loads(path.read_text()) if path.exists() else {
        "version": 1, "implementation_sha256": inputs, "cases": {},
    }
    if saved["version"] != 1 or saved["implementation_sha256"] != inputs:
        if reuse:
            raise ValueError("completed mutation inputs changed; rerun without cached results")
        saved = {"version": 1, "implementation_sha256": inputs, "cases": {}}
    cached = saved["cases"].get(case[0])
    if reuse and cached is not None:
        row = cached["record"]
        if cached["recipe"] != list(case) or row["build_exit"] != 0 or row["gate_exit"] != 1:
            raise ValueError("invalid completed mutation checkpoint")
        source = (ROOT / case[1]).read_bytes()
        changed = original_case.__globals__["mutate_source"](
            case[0], source.decode(), case[2], case[3]).encode()
        if row["before_sha256"] != hashlib.sha256(source).hexdigest() or row["mutated_sha256"] != hashlib.sha256(changed).hexdigest():
            raise ValueError("completed mutation source recipe changed")
        if row["diagnostic"] != case[4] or row["log_sha256"] != row["log"]["sha256"]:
            raise ValueError("completed mutation identity changed")
        for key, suffix in (("log", ".log"), ("build_log", "-build.log")):
            source = ROOT / row[key]["path"]
            if evidence(source) != row[key]:
                raise ValueError("completed mutation log changed")
            shutil.copyfile(source, logs / (case[0] + suffix))
        if case[4] not in (logs / (case[0] + ".log")).read_text():
            raise ValueError("completed mutation diagnostic changed")
        return dict(row, reused=True)
    row = equivalent_completed(case, saved, original_case)
    if row is None:
        row = run_case_with_retry(original_case, *arguments)
    else:
        for key, suffix in (("log", ".log"), ("build_log", "-build.log")):
            shutil.copyfile(ROOT / row[key]["path"], logs / (case[0] + suffix))
    for key, suffix in (("log", ".log"), ("build_log", "-build.log")):
        target = LOGS / (case[0] + suffix)
        shutil.copyfile(logs / target.name, target)
        row[key] = evidence(target)
    saved["cases"][case[0]] = {"recipe": list(case), "record": row}
    path.write_text(json.dumps(saved, indent=2) + "\n")
    return row

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, choices=(1,), default=1)
    parser.add_argument("--check-reuse", action="store_true",
                        help="check identical mutation reuse and refusal of changed cache evidence")
    parser.add_argument("--reuse-checks", action="store_true",
                        help="reuse unchanged, hash-checked checks.json after a mutation failure")
    parser.add_argument("--reuse-mutations", action="store_true",
                        help="reuse completed, hash-checked isolated mutation results")
    args = parser.parse_args()
    if args.check_reuse:
        check_reuse()
        return
    LOGS.mkdir(parents=True, exist_ok=True)
    (LOGS / ".gitattributes").write_text(
        "# Preserve process output exactly for hash verification.\n*.log whitespace=-blank-at-eof\n")
    harness = runpy.run_path(str(ROOT / "dev/erasure-mutations.py"))
    selected = [case[0] for case in harness["CASES"] if case[0] in REQUIRED | CONTROLS]
    if set(selected) != REQUIRED | CONTROLS:
        raise ValueError("scoped mutation catalog changed")
    inputs = harness["implementation_hashes"](ROOT)
    for name in ("dev/bend-policy.json", "dev/bend-migration.json"):
        inputs[name] = digest(ROOT / name)
    if args.reuse_checks:
        checks = reuse_checks(inputs)
    else:
        checks = [
            check("anchors", ["python3", "-P", "dev/erasure-mutations.py", "--check-anchors"]),
            check("tests", ["make", "test"]),
            check("gates", ["zsh", "-f", "dev/gates.sh"]),
            check("erasure-record", ["python3", "-P", "dev/erasure-gates.py", "--record"]),
        ]
        (LOGS / "checks.json").write_text(json.dumps({
            "version": 1, "validated_inputs": inputs, "checks": checks,
            "producer_sha256": digest(Path(__file__)),
        }, indent=2) + "\n")
    inputs["dev/validation/case-collection-constructor-payload-fixtures-run.py"] = digest(Path(__file__))
    checks.append(check("reuse-validation", ["python3", "-P",
                        "dev/validation/case-collection-constructor-payload-fixtures-run.py", "--check-reuse"]))
    if not args.reuse_mutations:
        (LOGS / "completed-mutations.json").unlink(missing_ok=True)
    records = []
    original = harness["run_cases"]
    original_case = harness["run_case"]
    def collect(*arguments):
        result = original(*arguments)
        records.extend(result)
        return result
    harness["main"].__globals__["run_case"] = lambda *arguments: checkpoint_case(
        arguments[0], arguments[1], inputs, original_case, arguments, args.reuse_mutations)
    harness["main"].__globals__["run_cases"] = collect
    command = ["dev/erasure-mutations.py", "--jobs", str(args.jobs), "--logs", str(WORK)]
    for name in selected:
        command += ["--case", name]
    old_arguments = sys.argv
    started = time.monotonic()
    log = LOGS / "mutations.log"
    try:
        sys.argv = command
        with log.open("w") as output, contextlib.redirect_stdout(output):
            code = harness["main"]()
    finally:
        sys.argv = old_arguments
    if code != 0 or {row["name"] for row in records} != set(selected) or len(records) != len(selected):
        raise ValueError(f"scoped mutations failed: exit={code}; see {log}")
    for row in records:
        for suffix, key in ((".log", "log"), ("-build.log", "build_log")):
            target = LOGS / (row["name"] + suffix)
            shutil.copyfile(WORK / target.name, target)
            row[key] = evidence(target)
        if row["log_sha256"] != row["log"]["sha256"] or row["build_exit"] != 0:
            raise ValueError(f"mutation evidence mismatch: {row['name']}")
    shutil.copyfile(WORK / "baseline.log", LOGS / "mutation-baseline.log")
    checks.append({"name": "mutations", "harness_argv": command, "exit_code": code,
                   "log": evidence(log), "elapsed_seconds": round(time.monotonic() - started, 3),
                   "baseline": evidence(LOGS / "mutation-baseline.log")})
    for name, expected in inputs.items():
        if digest(ROOT / name) != expected:
            raise ValueError(f"input changed during validation: {name}")
    record = {
        "version": 1, "recorded_at": datetime.now(timezone.utc).isoformat(),
        "root": str(ROOT), "base_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "scope": "Six parsed fixture pairs place constructor-valued finite and constructor cases inside tuple and both sum payload fields. The selected branch reduces compound constructor fields to distinct values; the unused branch reverses them. A tuple sibling and a trailing outer field also reduce. Semantic variants recheck Pick and keep, preparation, proof sealing and runtime equality with opaque twins. The gate binds exact sources and modes 28 through 33. The direct constructor case collection syntax row compares explicit reduced terms for all six combinations, checking branch substitution, nested and outer field order and both sum addresses. Twenty-four mutations drop semantic variants or bypass constructor, case or collection recovery. Each recovery group shares anchors but requires distinct named fixture failures. Constructor recovery and field order are controls. Every mutation requires a successful isolated build and its named failure. Identical edits reuse verified isolated build and gate logs only with unchanged inputs, exact recipes and source hashes, matching log hashes and the required named failure. Shared execution is explicit in each reused mutation row.",
        "implementation_sha256": inputs, "checks": checks,
        "check_checkpoint": evidence(LOGS / "checks.json"),
        "mutation_checkpoint": evidence(LOGS / "completed-mutations.json"),
        "supporting_records_sha256": {"dev/validation/erasure.json": digest(ROOT / "dev/validation/erasure.json")},
        "catalog_total": len(harness["CASES"]), "selected": selected, "mutations": records,
    }
    (ROOT / "dev/validation/case-collection-constructor-payload-fixtures.json").write_text(
        json.dumps(record, indent=2) + "\n")
    print(f"CASE-COLLECTION-CONSTRUCTOR-PAYLOAD-FIXTURES recorded checks={len(checks)} caught={len(records)} total={len(harness['CASES'])}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
