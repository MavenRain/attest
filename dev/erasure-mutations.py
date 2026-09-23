#!/usr/bin/env python3
"""Mutate isolated copies of the erasure increment and require named failures."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SOURCE = "erase/opaque.ml"
KERNEL = "lib/check.ml"
CASES = (
    ("proof-guard", SOURCE, "if List.mem name names then",
     "if List.mem name names && false then", "row=f2-a first_diff="),
    ("row-reinsertion", SOURCE,
     "let rows = List.map (fun (name, entry) -> (name, seal names name entry)) rows in",
     "let rows = rows in", "row=f2-a first_diff="),
    ("inherited-scope", SOURCE,
     "Global.StringMap.mapi (seal names) globals.Global.entries",
     "Global.StringMap.mapi (fun name entry -> let _ = seal names name entry in entry) globals.Global.entries",
     "OPAQUE-ERASE exit=1"),
    # The gate tests the presence of every opaque twin before it reads it, so the
    # pin is the gate's named diagnostic and not a missing-file errno.
    ("missing-twin", "fixtures/erasure/f2-a-opaque.att", None, None,
     "row=f2-a opaque twin missing"),
    # The twin gate runs lean with -DwarningAsError=true, so a sorry ends the
    # LEAN-F2 leg on exit 1 before the empty-log and axiom checks run.
    ("lean-sorry", "twin/F2.lean", "def proof : AttestTwin.Equal := .refl trivial",
     "def proof : AttestTwin.Equal := sorry", "LEAN-F2 exit=1 expected=0"),
    ("prop-index-withdrawn", KERNEL,
     "if Level.equal level Level.zero || Level.le l level then Ok ()",
     "if Level.le l level then Ok ()", "PROP-INDEX row=nat-index FAIL"),
    ("type-index-unbounded", KERNEL,
     "if Level.equal level Level.zero || Level.le l level then Ok ()",
     "if Level.le l l then Ok ()", "PROP-INDEX row=type-index-bound FAIL"),
    ("prop-field-quantity", KERNEL,
     "&& Quantity.equal q Quantity.Zero",
     "&& (Quantity.equal q Quantity.Zero || true)",
     "PROP-INDEX row=runtime-proof-field FAIL"),
    ("prop-field-unindexed", KERNEL,
     "&& List.exists (parameter_at index) cd.ct_res_idx",
     "&& (List.exists (parameter_at index) cd.ct_res_idx || true)",
     "PROP-INDEX row=unindexed-proof-field FAIL"),
    ("prop-field-depth", KERNEL,
     "(depth - i - 1, field)", "(i, field)",
     "PROP-INDEX row=accessibility-family FAIL"),
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(root, command):
    return subprocess.run(command, cwd=root, capture_output=True, timeout=90)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    logs = ROOT / ("dev/validation/erasure-mutations" if args.record else ".gatework/erasure-mutations")
    logs.mkdir(parents=True, exist_ok=True)
    scratch_root = ROOT / ".gatework/erasure-copies"
    scratch_root.mkdir(parents=True, exist_ok=True)
    try:
        baseline = run(ROOT, ["python3", "-P", "dev/erasure-gates.py"])
        (logs / "baseline.log").write_bytes(baseline.stdout + baseline.stderr)
        if baseline.returncode != 0:
            raise ValueError("unmutated erasure gate failed")
        records = []
        for name, relative, before, after, diagnostic in CASES:
            with tempfile.TemporaryDirectory(dir=scratch_root, prefix=name + "-") as directory:
                scratch = Path(directory) / "tree"
                shutil.copytree(ROOT, scratch, ignore=shutil.ignore_patterns(
                    ".git", "_build", ".lake", ".gatework", ".kanon-*", "__pycache__"))
                path = scratch / relative
                original = path.read_bytes()
                if before is None:
                    path.unlink()
                    changed = None
                else:
                    source = original.decode()
                    if source.count(before) != 1:
                        raise ValueError(f"{name}: mutation anchor is not unique")
                    changed = source.replace(before, after, 1).encode()
                    path.write_bytes(changed)
                build = run(scratch, ["zsh", "-f", "dev/dunecho.sh", "build"])
                (logs / (name + "-build.log")).write_bytes(build.stdout + build.stderr)
                if build.returncode:
                    raise ValueError(f"{name}: build failed, not a caught behavior mutation")
                result = run(scratch, ["python3", "-P", "dev/erasure-gates.py"])
                output = result.stdout + result.stderr
                if diagnostic.startswith("PROP-INDEX row="):
                    if b"PROP-INDEX exit=1 expected=0" not in output:
                        raise ValueError(f"{name}: did not reach the Prop index regression")
                    output += (scratch / ".gatework/erasure/PROP-INDEX.log").read_bytes()
                # A temporary checkout path is not part of a diagnostic's identity.
                output = output.replace(str(scratch).encode(), b"<mutation-tree>")
                (logs / (name + ".log")).write_bytes(output)
                if result.returncode != 1 or diagnostic.encode() not in output:
                    raise ValueError(f"{name}: expected named gate failure {diagnostic!r}")
                records.append({"name": name, "path": relative, "before_sha256": digest(original),
                    "mutated_sha256": None if changed is None else digest(changed),
                    "log_sha256": digest(output),
                    "build_exit": build.returncode, "gate_exit": result.returncode,
                    "diagnostic": diagnostic, **({"deleted": True} if changed is None else {})})
                print(f"ERASURE-MUTATION {name} caught")
        if args.record:
            record = {"version": 1, "baseline_sha256": digest(baseline.stdout + baseline.stderr),
                      "implementation_sha256": {p: digest((ROOT / p).read_bytes()) for p in
                        (SOURCE, KERNEL, "erase/test/prop_index.ml", "erase/test/dune",
                         "erase/test/opaque_test.ml", "dev/erasure-mutations.py", "dev/erasure-gates.py")},
                      "mutations": records}
            (ROOT / "dev/validation/erasure-mutations.json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"ERASURE-MUTATIONS caught={len(records)} total={len(CASES)} OK")
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"ERASURE-MUTATIONS FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
