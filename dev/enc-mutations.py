#!/usr/bin/env python3
"""ENC-MUTATIONS: the five Stage C encoder mutants of parts/09-mutants.md:33-37.

Each case copies the checkout under .gatework/enc-copies/, applies one source
edit (an anchor that occurs exactly once) or deletes one reference object, and
runs dev/enc-xcheck.py in the copy.  A mutant is caught when the gate exits 1
and prints the expected diagnostic.  Verdict:
`ENC-MUTATIONS caught=5 total=5 OK`.  `--record` writes
dev/validation/enc-mutations.json; `--check-anchors` only checks that every
anchor is unique in the checkout.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENCODER = "elf/rv64im.bend"
IGNORE = shutil.ignore_patterns(".git", "_build", "_tools", ".lake", ".gatework", ".kanon-*", "__pycache__")
# (name, file, before, after, diagnostic).  after = None deletes the file.
CASES = (
    ("funct3", ENCODER,
     "Rv.i_type(19, 0, rd, rs1, imm)",
     "Rv.i_type(19, 1, rd, rs1, imm)",
     "FAIL insn=addi ours=0x00559513 ref=0x00558513"),
    ("immediate", ENCODER,
     "Done{(i .&. 4095 : U32)}, 20n",
     "Done{(i .&. 4095 : U32)}, 19n",
     "mismatch=1 FAIL"),
    ("register", ENCODER,
     "Rv.base(opcode, f3, f7), Rv.reg_bits(rd), 7n), Rv.reg_bits(rs1), 15n), Rv.reg_bits(rs2), 20n)",
     "Rv.base(opcode, f3, f7), Rv.reg_bits(rd), 7n), Rv.reg_bits(rs2), 15n), Rv.reg_bits(rs1), 20n)",
     "FAIL insn=add ours="),
    ("compressed", ENCODER,
     'Rv.done("addi", 32n,',
     'Rv.done("c.addi", 16n,',
     "FAIL insn=c.addi width=16 allowed=32"),
    ("w-object", "corpus/ref/addw.o", None, None,
     "FAIL missing=addw"),
)
PINS = ("dev/enc-xcheck.py", "dev/enc-mutations.py", "corpus/ref/manifest.json")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def anchors(root):
    for name, relative, before, after, diagnostic in CASES:
        if before is None:
            if not (root / relative).is_file():
                raise ValueError(f"{name}: {relative} is missing")
        elif (root / relative).read_text().count(before) != 1:
            raise ValueError(f"{name}: mutation anchor is not unique: {before!r}")


def mutate(scratch, case):
    name, relative, before, after, diagnostic = case
    target = scratch / relative
    if before is None:
        target.unlink()
        return
    source = target.read_text()
    target.write_text(source.replace(before, after, 1))


def gate(scratch):
    environment = dict(os.environ)
    environment.setdefault("ATTEST_BEND_ROOT", str(ROOT / "_tools/bend"))
    return subprocess.run(["python3", "-P", "dev/enc-xcheck.py"], cwd=scratch, env=environment,
                          capture_output=True, text=True, timeout=900)


def run_case(case, logs, scratch_root):
    name, relative, before, after, diagnostic = case
    with tempfile.TemporaryDirectory(dir=scratch_root, prefix=name + "-") as directory:
        scratch = Path(directory) / "tree"
        shutil.copytree(ROOT, scratch, ignore=IGNORE)
        if (ROOT / "_build/js").is_dir():
            shutil.copytree(ROOT / "_build/js", scratch / "_build/js")
        mutate(scratch, case)
        result = gate(scratch)
    output = result.stdout + result.stderr
    (logs / f"{name}.log").write_text(output)
    caught = result.returncode == 1 and diagnostic in result.stdout
    print(f"MUTANT {name} exit={result.returncode} caught={'yes' if caught else 'NO'} want={diagnostic!r}")
    if not caught:
        raise ValueError(f"{name} survived: exit {result.returncode}, output {output.strip()[-200:]!r}")
    return {"name": name, "file": relative, "diagnostic": diagnostic, "exit": result.returncode,
            "output_sha256": digest(output.encode())}


def implementation_hashes():
    paths = list((ROOT / "elf").rglob("*.bend")) + [ROOT / p for p in PINS]
    return {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--check-anchors", action="store_true")
    args = parser.parse_args()
    try:
        anchors(ROOT)
        if args.check_anchors:
            print(f"ENC-MUTATIONS anchors={len(CASES)} OK")
            return 0
        logs = ROOT / ("dev/validation/enc-mutations" if args.record else ".gatework/enc-mutations")
        logs.mkdir(parents=True, exist_ok=True)
        scratch_root = ROOT / ".gatework/enc-copies"
        scratch_root.mkdir(parents=True, exist_ok=True)
        inputs = implementation_hashes()
        baseline = gate(ROOT)
        if baseline.returncode != 0:
            raise ValueError(f"baseline gate failed: {baseline.stdout.strip()}")
        records = [run_case(case, logs, scratch_root) for case in CASES]
        if implementation_hashes() != inputs:
            raise ValueError("implementation changed during the mutation battery")
        if args.record:
            data = {"version": 1, "baseline_sha256": digest((baseline.stdout + baseline.stderr).encode()),
                    "implementation_sha256": inputs, "mutations": records,
                    "logs_sha256": {p.name: digest(p.read_bytes()) for p in sorted(logs.glob("*.log"))}}
            (ROOT / "dev/validation/enc-mutations.json").write_text(json.dumps(data, indent=2) + "\n")
        print(f"ENC-MUTATIONS caught={len(records)} total={len(CASES)} OK")
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"ENC-MUTATIONS FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
