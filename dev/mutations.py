#!/usr/bin/env python3
"""Probe Stage A's failure paths in independent temporary source copies.

Scratch outputs go to .gatework/mutations/ (baseline.log, one log per probe,
results.json). With --record (the dev/mutations.sh wrapper forwards its
arguments) or MUTATIONS_RECORD=1, a fully caught run also writes the committed
record:
dev/validation/stage-a.json (envelope plus the probe records),
dev/validation/stage-a-gates.txt (the baseline gate transcript that
baseline_sha256 hashes) and dev/validation/mutations/<name>.log (the probe
logs that log_sha256 hashes). Regenerate with
`MUTATIONS_RECORD=1 zsh -f dev/mutations.sh` from the repository root.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
logs = root / ".gatework/mutations"
logs.mkdir(parents=True, exist_ok=True)
validation = root / "dev/validation"
build = ["python3", "-P", "dev/build.py", "--backend", "js", "attest", "suite-probe"]
# dev/mutations.sh sets MUTATIONS_VIA_WRAPPER=1 so mutation_command names the
# invocation that really ran: wrapper or direct, env flag or --record.
via_wrapper = os.environ.get("MUTATIONS_VIA_WRAPPER") == "1"
record_env = os.environ.get("MUTATIONS_RECORD") == "1"
record_flag = "--record" in sys.argv[1:]
record = record_env or record_flag
baseline_command = "zsh -f dev/gates.sh"
mutation_command = "".join((
    "MUTATIONS_RECORD=1 " if record_env else "",
    "zsh -f dev/mutations.sh" if via_wrapper else "python3 -P dev/mutations.py",
    " --record" if record_flag else ""))

# Stage A implementation surface pinned by dev/validation/stage-a.json: the
# kernel driver, the gate scripts and their probes, the build files and the
# fixtures the gates read. Hashed from the live tree at record time.
# Pin the complete active implementation; historical hashes live in the migration record.
implementation = tuple(sorted({
    "corpus/id.att", "dev/PIN", "dev/carry-manifest.json", "dev/bend-migration.json",
    "dev/bend-toolchain.json", "Makefile", "SPEC.md", "dev/r0-diff/SHA256",
    "fixtures/axiom.att", "fixtures/ill-typed.att",
    *(str(path.relative_to(root)) for folder in ("lib", "surface", "bin", "erase", "test", "dev")
      for path in (root / folder).rglob("*.bend")),
    *(str(path.relative_to(root)) for path in (root / "dev").glob("*.py")),
    *(str(path.relative_to(root)) for path in (root / "dev").glob("*.sh")),
}))


def script(name):
    return ["zsh", "-f", "dev/" + name + ".sh"]

def sha256(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()

def run(command, cwd):
    """Run a gate with UTF-8 decoding so the hashed logs do not depend on the locale."""
    environment = dict(os.environ)
    environment.setdefault("ATTEST_BEND_ROOT", str(root / "_tools/bend"))
    return subprocess.run(command, cwd=cwd, env=environment, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")

def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError(f"mutation anchor is not unique: {before!r}")
    return text.replace(before, after, 1)

def first_match(pattern, output):
    return next((line for line in output.splitlines() if re.search(pattern, line)), "")

def write_record(baseline_output, records):
    """Write the committed Stage A record so every pinned hash resolves in the tree."""
    kept = validation / "mutations"
    kept.mkdir(parents=True, exist_ok=True)
    (validation / "stage-a-gates.txt").write_text(baseline_output, encoding="utf-8")
    for entry in records:
        shutil.copyfile(root / entry["log"], kept / (entry["name"] + ".log"))
    envelope = {
        "version": 1,
        "stage": "A",
        "recorded_at": datetime.now(timezone.utc).isoformat(),
        "baseline_command": baseline_command,
        "baseline_exit": 0,
        "baseline_sha256": sha256(baseline_output),
        "implementation_sha256": {
            path: hashlib.sha256((root / path).read_bytes()).hexdigest()
            for path in implementation},
        "mutation_command": mutation_command,
        "mutation_exit": 0,
        "mutations": [
            {**entry, "log": str((kept / (entry["name"] + ".log")).relative_to(root))}
            for entry in records],
    }
    target = validation / "stage-a.json"
    target.write_text(json.dumps(envelope, indent=2) + "\n", encoding="utf-8")
    print(f"MUTATIONS RECORD {target.relative_to(root)} logs={len(records)}")

def corrupt_reference(text):
    record = json.loads(text)
    row = next(entry for entry in record["removed"] if entry["path"] == "dev/r0-diff/term.ml")
    row["sha256"] = ("0" if row["sha256"][0] != "0" else "1") + row["sha256"][1:]
    return json.dumps(record, indent=2) + "\n"


def kernel_growth(text):
    files = [root / "lib/foundation.bend", *sorted((root / "lib").glob("kernel*.bend"))]
    count = sum(len(path.read_bytes().splitlines()) for path in files
                if path.name not in {"kernel_pp.bend", "kernel_metadata.bend"})
    return text + "\n" + "# kernel budget mutant\n" * max(1, 6001 - count)


# The BUILD mutant replaces OCaml unused-variable warnings with Bend's affine
# binder discipline. Both require the compiler to reject an invalid source edit.
# R0-walk-order still mutates traversal order; the migration fingerprint now
# supplies the rejection instead of claiming byte equality across languages.
# name, source path, mutation, gate command, required diagnostic, build first
cases = [
    ("PIN", "dev/PIN", lambda s: s[:-2] + ("0" if s[-2] != "0" else "1") + "\n",
     script("carry-check"), r"PIN .* FAIL expected=", False),
    ("CARRY", "lib/foundation.bend", lambda s: s + "# unreviewed source edit\n",
     script("carry-check"), r"CARRY FAIL: unreviewed Bend source change: lib/foundation.bend", False),
    ("CARRY-unlisted", "lib/unlisted.bend", lambda s: "import Base\ndef marker() -> Unit: Unit{}\n",
     script("carry-check"), r"unlisted or missing Bend sources:.*lib/unlisted.bend", False),
    ("CARRY-origin", "dev/carry-manifest.json",
     lambda s: s.replace('"origin": "assay"', '"origin": "unknown"', 1),
     script("carry-check"), r"unknown carry origin", False),
    ("BUILD", "lib/foundation.bend",
     lambda s: s + "\ndef mutant_affinity(x: Unit) -> Pair2<Unit, Unit>:\n  Pair2{x, x}\n",
     build, r"consumed|usage|multiplicity|more than once", False),
    ("SUITE-KERNEL", "test/golden/a01-fun-app.checked",
     lambda s: s + "invalid expected checked form\n",
     ["_build/default/test/main.exe", "test"], r"SUITE-KERNEL FAIL", True),
    ("R0-former-count", "lib/foundation.bend",
     lambda s: replace_once(s, '["Lan", "Ran"]', '["Lan", "Ran", "KHost"]'),
     script("r0-count"), r"R0-COUNT FAIL", True),
    ("R0-third-constructor", "lib/foundation.bend",
     lambda s: replace_once(s, "  Term.Lan{x0: Shape.t<Term.t>, x1: Term.t}",
                           "  Term.KHost{x0: Shape.t<Term.t>, x1: Term.t}\n  Term.Lan{x0: Shape.t<Term.t>, x1: Term.t}"),
     build, r"KHost", False),
    ("R0-shape", "lib/foundation.bend",
     lambda s: replace_once(s, "  Shape.SNu{x0: String, x1: List<&2, A>}",
                           "  Shape.SNu{x0: String, x1: List<&2, A>}\n  Shape.KHost{x0: A}"),
     script("r0-audit"), r"KHost.*no refusal row", False),
    ("R0-walk-order", "lib/foundation.bend",
     lambda s: replace_once(s, "case Shape.SPar{x0, x1}:\n      [x0, x1]",
                           "case Shape.SPar{x0, x1}:\n      [x1, x0]"),
     script("r0-diff"), r"R0-DIFF FAIL: unreviewed Bend source change: lib/foundation.bend", False),
    ("R0-reference", "dev/bend-migration.json", corrupt_reference,
     script("r0-diff"), r"R0-DIFF FAIL row=term.ml: historical reference checksum", False),
    ("AXIOMS", "corpus/id.att", lambda s: s + "\naxiom smuggled : Type 0\n",
     script("axioms-empty"), r"AXIOM smuggled", True),
    ("kernel-growth", "lib/kernel_check.bend", kernel_growth,
     script("trusted-lines"), r"kernel=[0-9]+/6000.*FAIL", False),
]


def main():
    unknown = [arg for arg in sys.argv[1:] if arg != "--record"]
    if unknown:
        print(f"MUTATIONS FAIL: unknown argument {unknown[0]!r}; only --record is accepted")
        return 2
    records = []
    try:
        baseline = run(script("gates"), root)
        baseline_output = baseline.stdout + baseline.stderr
        (logs / "baseline.log").write_text(baseline_output, encoding="utf-8")
        if baseline.returncode:
            raise ValueError("unmutated Stage A gates failed; see baseline.log")
        for name, relative, mutate, command, diagnostic, needs_build in cases:
            with tempfile.TemporaryDirectory(prefix="mutation-", dir=logs) as temporary:
                scratch = Path(temporary) / "tree"
                shutil.copytree(root, scratch, ignore=shutil.ignore_patterns(
                    ".git", "_build", "_tools", ".lake", ".gatework", ".kanon-*", "__pycache__"))
                cached = root / "_build/js"
                if cached.is_dir():
                    shutil.copytree(cached, scratch / "_build/js")
                source = scratch / relative
                original = source.read_text(encoding="utf-8") if source.exists() else ""
                changed = mutate(original)
                if changed == original:
                    raise ValueError(f"{name}: mutation made no change")
                source.write_text(changed, encoding="utf-8")
                if name == "CARRY-origin":
                    migration_path = scratch / "dev/bend-migration.json"
                    migration = json.loads(migration_path.read_text())
                    migration["carry_manifest_sha256"] = sha256(changed)
                    migration_path.write_text(json.dumps(migration, indent=2) + "\n")
                if needs_build:
                    built = run(build, scratch)
                    (logs / (name + "-build.log")).write_text(built.stdout + built.stderr,
                                                              encoding="utf-8")
                    if built.returncode:
                        raise ValueError(f"{name}: prerequisite build failed; see build log")
                result = run(command, scratch)
                output = result.stdout + result.stderr
                log = logs / (name + ".log")
                log.write_text(output, encoding="utf-8")
                caught = result.returncode != 0 and re.search(diagnostic, output) is not None
                records.append({"name": name, "path": relative, "gate": command,
                                "before_sha256": sha256(original),
                                "after_sha256": sha256(changed),
                                "exit": result.returncode, "caught": caught,
                                "diagnostic": diagnostic, "log": str(log.relative_to(root)),
                                "observed": first_match(diagnostic, output),
                                "log_sha256": sha256(output)})
                print(f"MUTATION {name} " + ("CAUGHT" if caught else "MISSED"), flush=True)
                if not caught:
                    raise ValueError(f"{name}: expected a nonzero exit and {diagnostic!r}; see {log}")
        print(f"MUTATIONS caught={len(records)} total={len(cases)} OK")
        if record:
            write_record(baseline_output, records)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"MUTATIONS FAIL: {error}")
        sys.exit(1)
    finally:
        (logs / "results.json").write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    sys.exit(main())
