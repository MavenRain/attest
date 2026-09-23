#!/usr/bin/env python3
"""Exercise corpus guards with passing controls and isolated broken twins."""
from pathlib import Path
import argparse
import datetime
import json
import runpy
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
GATE = runpy.run_path(str(ROOT / "dev/lean_twin.py"))

# name, row (None selects inventory), file, old bytes, new bytes, expected refusal
MUTATIONS = (
    ("missing-row", None, "lean/corpus.json", None, None, "24 ACCEPT and 12 REFUSE"),
    ("missing-source", None, "lean/Corpus/nat-literal.lean", None, None, "missing="),
    ("sorry", "nat-literal", "lean/Corpus/nat-literal.lean", ":= 7", ":= sorry", "term proofs"),
    ("axiom", "nat-literal", "lean/Corpus/nat-literal.lean", "def checked : Nat := 7",
     "axiom unchecked : Nat\ndef checked : Nat := unchecked", "term proofs"),
    ("lean-axiom-reached", "nat-literal", "lean/Corpus/nat-literal.lean", "def checked : Nat := 7",
     "def checked : Nat := 7\ntheorem classical (p : Prop) : p ∨ ¬p := Classical.em p",
     "unexpected Lean diagnostic or axiom"),
    ("lean-sorryax", "nat-literal", "lean/Corpus/nat-literal.lean", ":= 7", ":= sorryAx Nat false",
     "nat-literal-lean exit=1 expected=0"),
    ("attest-refuses", "nat-literal", "fixtures/lean-twin/nat-literal.att", ":= 7", ":= ()",
     "nat-literal-attest exit=1 expected=0"),
    ("refuse-accepted", "universe-refuse", "fixtures/lean-twin/universe-refuse.att",
     "def rejected : Type 0 := Type 0", "def rejected : Type 1 := Type 0", "exit=0 expected=1"),
    ("wrong-attest-diagnostic", "universe-refuse", "fixtures/lean-twin/universe-refuse.att",
     "def rejected : Type 0 := Type 0", "def rejected : Type 0 := ()", "wrong attest refusal"),
    ("wrong-attest-universe", "universe-refuse", "fixtures/lean-twin/universe-refuse.att",
     "def rejected : Type 0 := Type 0", "def rejected : Nat := Type 0", "wrong attest refusal"),
    ("attest-prefix", "universe-refuse", "fixtures/lean-twin/universe-refuse.att",
     "def seed : Nat := 0", "def seed : Nat := ()", "prefix-attest exit=1 expected=0"),
    ("lean-prefix", "universe-refuse", "lean/Corpus/universe-refuse.lean",
     "def seed : Nat := 0", "def seed : Nat := PUnit.unit", "prefix-lean exit=1 expected=0"),
    ("wrong-diagnostic", "universe-refuse", "lean/Corpus/universe-refuse.lean",
     "def rejected : Type := Type", "def rejected : Type := missingName", "wrong Lean refusal"),
)


def check(root, logs, row_id):
    rows = GATE["inventory"](root)
    if row_id is not None:
        row = next(row for row in rows if row["id"] == row_id)
        GATE["check_row"](root, logs, row)


def run(record):
    if not (ROOT / "_build/default/bin/attest.exe").is_file() or not (ROOT / ".lake/build/lib/lean/AttestTwin.olean").is_file():
        raise ValueError("run dev/lean-twin.sh before the mutation checks")
    logs = ROOT / ".gatework/lean-twin-mutations"
    if logs.exists():
        shutil.rmtree(logs)
    logs.mkdir(parents=True)
    results = []
    for name, row_id, relative, old, new, expected in MUTATIONS:
        with tempfile.TemporaryDirectory(prefix="attest-twin-" + name + "-") as directory:
            root = Path(directory)
            for path in ("lean", "fixtures/lean-twin", "AttestTwin"):
                shutil.copytree(ROOT / path, root / path)
            for path in ("AttestTwin.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json"):
                shutil.copyfile(ROOT / path, root / path)
            for path in ("_build", ".lake"):
                (root / path).symlink_to(ROOT / path, target_is_directory=True)
            control = logs / name / "control"
            changed = logs / name / "mutant"
            control.mkdir(parents=True)
            changed.mkdir()
            check(root, control, row_id)
            path = root / relative
            before = GATE["digest"](path.read_bytes())
            if name == "missing-row":
                data = json.loads(path.read_text())
                data["rows"].pop()
                path.write_text(json.dumps(data, indent=2) + "\n")
                after = GATE["digest"](path.read_bytes())
            elif old is None:
                path.unlink()
                after = None
            else:
                source = path.read_text()
                if old not in source:
                    raise ValueError(f"{name} mutation target missing")
                path.write_text(source.replace(old, new, 1))
                after = GATE["digest"](path.read_bytes())
            caught = ""
            try:
                check(root, changed, row_id)
            except ValueError as error:
                caught = str(error)
            if expected not in caught:
                raise ValueError(f"{name} expected={expected!r} caught={caught!r}")
            (changed / "refusal.log").write_text(caught + "\n")
            results.append({"name": name, "path": relative, "control": "pass",
                            "before_sha256": before, "after_sha256": after,
                            "expected": expected, "caught": True})
            print(f"LEAN-TWIN-MUTATION {name} caught=1 control=pass", flush=True)
    summary = f"LEAN-TWIN-MUTATIONS caught={len(results)} total={len(MUTATIONS)} OK"
    print(summary)
    if record:
        destination = ROOT / "dev/validation/lean-twin-mutations"
        hashes = {}
        for path in sorted(logs.rglob("*.log")):
            relative = path.relative_to(logs)
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            hashes[str(relative)] = GATE["digest"](path.read_bytes())
        sources = ["dev/lean-twin-mutations.py", "dev/lean_twin.py", "lean/corpus.json"]
        payload = {"version": 1, "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "root": str(ROOT), "summary": summary, "rows": results, "log_sha256": hashes,
                   "implementation_sha256": {p: GATE["digest"]((ROOT / p).read_bytes()) for p in sources}}
        (ROOT / "dev/validation/lean-twin-mutations.json").write_text(json.dumps(payload, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    try:
        run(args.record)
    except (OSError, ValueError) as error:
        print(f"LEAN-TWIN-MUTATIONS FAIL {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
