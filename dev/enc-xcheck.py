#!/usr/bin/env python3
"""ENC-XCHECK: cross-check the Bend RV64IM encoder against LLVM reference objects.

The gate builds and runs test/enc_xcheck.bend, which prints one
`ROW <name> <mnemonic> <width> <decimal word>` line per encoder row and one
`HALT <decimal bytes>` line for the HALT ELF64 image.  Every row has a
reference object under corpus/ref/, assembled once by Homebrew clang
(`--assemble`) and pinned by sha256 in corpus/ref/manifest.json.  The word
that llvm-objdump reads back from each object must equal our word.  The HALT
image must equal corpus/halt.elf (written only with `--pin`)
and llvm-readelf must read it as an ELF64 little endian RISC-V executable with
one LOAD segment and the entry 0x78000000.

Verdicts: `ELF-HALT bytes=4108 entry=0x78000000 OK` then
`ENC-XCHECK rows=14 objects=13 mismatch=0`.  Any failure prints one
`ENC-XCHECK ... FAIL ...` line and exits 1.  `--record` writes
dev/validation/enc-xcheck.json with the implementation and log digests.
"""
import argparse
import hashlib
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LLVM = Path("/opt/homebrew/opt/llvm/bin")
REF = ROOT / "corpus/ref"
MANIFEST = REF / "manifest.json"
HALT = ROOT / "corpus/halt.elf"
PROGRAM = ROOT / "_build/default/test/enc_xcheck.exe"
ENTRY = 0x78000000
TEXT_OFFSET = 4096
HALT_CODE = bytes.fromhex("930200001305000073000000")
HALT_BYTES = TEXT_OFFSET + len(HALT_CODE)
WIDTH = 32
# (name, kind, assembly).  The 14 dossier rows carry the reference table of
# kan-sp1-lang-dossier-toolchain.md:220-253; the 13 object rows add the
# negative immediate, the 64-bit loads and stores, the eight W forms and the
# HALT register row.  Order = the ROW order of test/enc_xcheck.bend.
ROWS = (
    ("add", "dossier", "add a0, a1, a2"),
    ("addi", "dossier", "addi a0, a1, 5"),
    ("lw", "dossier", "lw a0, 8(a1)"),
    ("sw", "dossier", "sw a0, 12(a1)"),
    ("beq", "dossier", "beq a0, a1, . + 36"),
    ("lui", "dossier", "lui a0, 0x12345"),
    ("auipc", "dossier", "auipc a0, 0x1"),
    ("jal", "dossier", "jal ra, . + 24"),
    ("jalr", "dossier", "jalr ra, 4(a1)"),
    ("mul", "dossier", "mul a0, a1, a2"),
    ("mulh", "dossier", "mulh a0, a1, a2"),
    ("div", "dossier", "div a0, a1, a2"),
    ("rem", "dossier", "rem a0, a1, a2"),
    ("ecall", "dossier", "ecall"),
    ("addi-neg", "object", "addi a0, a0, -1"),
    ("lwu", "object", "lwu a0, 0(a0)"),
    ("ld", "object", "ld a0, 0(sp)"),
    ("sd", "object", "sd a0, 0(sp)"),
    ("addw", "object", "addw a0, a1, a2"),
    ("subw", "object", "subw a0, a1, a2"),
    ("sllw", "object", "sllw a0, a1, a2"),
    ("srlw", "object", "srlw a0, a1, a2"),
    ("sraw", "object", "sraw a0, a1, a2"),
    ("mulw", "object", "mulw a0, a1, a2"),
    ("divw", "object", "divw a0, a1, a2"),
    ("remw", "object", "remw a0, a1, a2"),
    ("halt-addi", "object", "addi t0, x0, 0"),
)
PINS = ("dev/enc-xcheck.py", "dev/enc-xcheck-test.py", "dev/build.py", "dev/gates.sh", "dev/bend-toolchain.json",
        "test/enc_xcheck.bend", "test/elf_test.bend", "corpus/halt.elf")
OBJDUMP_WORD = re.compile(r"^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s", re.MULTILINE)


class GateError(Exception):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run(command, cwd=ROOT):
    environment = dict(os.environ)
    environment.setdefault("ATTEST_BEND_ROOT", str(ROOT / "_tools/bend"))
    environment.setdefault("BEND_NO_TELEMETRY", "1")
    result = subprocess.run(command, cwd=cwd, env=environment, capture_output=True, text=True, timeout=600)
    if result.returncode != 0:
        tail = (result.stdout + result.stderr).strip().splitlines()[-3:]
        raise GateError(f"{command[0]} exit {result.returncode}: {' | '.join(tail)}")
    return result.stdout


def assemble(logs):
    REF.mkdir(parents=True, exist_ok=True)
    manifest = []
    for name, kind, asm in ROWS:
        source = REF / f"{name}.s"
        source.write_text(f"\t.text\n\t{asm}\n")
        run([str(LLVM / "clang"), "--target=riscv64-unknown-elf", "-march=rv64im", "-mno-relax",
             "-c", str(source), "-o", str(REF / f"{name}.o")])
        data = (REF / f"{name}.o").read_bytes()
        manifest.append({"name": name, "kind": kind, "asm": asm, "object": f"corpus/ref/{name}.o",
                         "sha256": digest(data), "word": f"0x{reference_word(name):08x}"})
    MANIFEST.write_text(json.dumps({"version": 1, "assembler": "clang --target=riscv64-unknown-elf -march=rv64im -mno-relax",
                                    "rows": manifest}, indent=2) + "\n")
    (logs / "assemble.log").write_text("".join(f"{row['name']} {row['word']} {row['asm']}\n" for row in manifest))


def reference_word(name):
    text = run([str(LLVM / "llvm-objdump"), "-d", str(REF / f"{name}.o")])
    words = OBJDUMP_WORD.findall(text)
    if len(words) != 1:
        raise GateError(f"objdump of {name}.o gives {len(words)} words, expected 1")
    return int(words[0], 16)


def our_rows(logs):
    run(["python3", "-P", "dev/build.py", "--backend", "js", "enc-xcheck"])
    text = run([str(PROGRAM)])
    (logs / "dump.log").write_text(text)
    rows = {}
    halt = None
    order = []
    for line in text.splitlines():
        parts = line.split()
        if parts[:1] == ["ROW"] and len(parts) == 5:
            rows[parts[1]] = (parts[2], int(parts[3]), int(parts[4]))
            order.append(parts[1])
        elif parts[:1] == ["HALT"]:
            halt = bytes(int(part) for part in parts[1:])
    if order != [name for name, kind, asm in ROWS]:
        raise GateError(f"dump rows {order} differ from the row table")
    if halt is None:
        raise GateError("dump has no HALT line")
    return rows, halt


def check_widths(rows):
    for name, kind, asm in ROWS:
        mnemonic, width, word = rows[name]
        if width != WIDTH:
            return f"ENC-XCHECK FAIL insn={mnemonic} width={width} allowed={WIDTH}"
    return None


def check_objects(rows, logs):
    pinned = {row["name"]: row for row in json.loads(MANIFEST.read_text())["rows"]}
    dossier = sum(1 for name, kind, asm in ROWS if kind == "dossier")
    present = sum(1 for name, kind, asm in ROWS if kind == "object" and (REF / f"{name}.o").is_file())
    prefix = f"ENC-XCHECK rows={dossier} objects={present}"
    for name, kind, asm in ROWS:
        if not (REF / f"{name}.o").is_file():
            return f"{prefix} FAIL missing={name}"
        if name not in pinned:
            return f"{prefix} FAIL unpinned={name}"
        if digest((REF / f"{name}.o").read_bytes()) != pinned[name]["sha256"]:
            return f"{prefix} FAIL stale={name}"
    table = []
    for name, kind, asm in ROWS:
        mnemonic, width, ours = rows[name]
        ref = reference_word(name)
        table.append(f"{name} {mnemonic} ours=0x{ours:08x} ref=0x{ref:08x}\n")
        if ours != ref:
            (logs / "rows.log").write_text("".join(table))
            return f"{prefix} mismatch=1 FAIL insn={name} ours=0x{ours:08x} ref=0x{ref:08x}"
    (logs / "rows.log").write_text("".join(table))
    return f"{prefix} mismatch=0"


def check_halt(halt, pin, logs):
    if len(halt) != HALT_BYTES:
        return f"ENC-XCHECK FAIL halt bytes={len(halt)} expected={HALT_BYTES}"
    header_fields = struct.unpack_from("<16sHHIQQQIHHHHHH", halt)
    expected_header = (b"\x7fELF\x02\x01\x01" + bytes(9), 2, 243, 1, ENTRY,
                       64, 0, 0, 64, 56, 1, 0, 0, 0)
    if header_fields != expected_header:
        return "ENC-XCHECK FAIL halt ELF header fields"
    segment = struct.unpack_from("<IIQQQQQQ", halt, 64)
    if segment != (1, 5, TEXT_OFFSET, ENTRY, ENTRY, len(HALT_CODE), len(HALT_CODE), 4096):
        return "ENC-XCHECK FAIL halt LOAD layout (offset, address, size, flags or alignment)"
    if halt[120:TEXT_OFFSET] != bytes(TEXT_OFFSET - 120) or halt[TEXT_OFFSET:] != HALT_CODE:
        return "ENC-XCHECK FAIL halt padding or instruction bytes"
    if not pin:
        if not HALT.is_file():
            return "ENC-XCHECK FAIL missing=corpus/halt.elf (use --pin to create it)"
        if HALT.read_bytes() != halt:
            return "ENC-XCHECK FAIL halt=differs from corpus/halt.elf"
    with tempfile.NamedTemporaryFile(suffix=".elf") as candidate:
        candidate.write(halt)
        candidate.flush()
        header = run([str(LLVM / "llvm-readelf"), "-h", candidate.name])
        segments = run([str(LLVM / "llvm-readelf"), "-l", candidate.name])
    (logs / "readelf.log").write_text(header + segments)
    wanted = ("Class:                             ELF64", "little endian", "Type:                              EXEC",
              "Machine:                           RISC-V", f"Entry point address:               0x{ENTRY:x}")
    for text in wanted:
        if text not in header:
            return f"ENC-XCHECK FAIL halt header lacks {text.split(':')[0].strip()}={text.split()[-1]}"
    loads = [line for line in segments.splitlines() if line.strip().startswith("LOAD")]
    if len(loads) != 1:
        return f"ENC-XCHECK FAIL halt segments={len(loads)} expected=1"
    if " R E " not in loads[0] + " ":
        return f"ENC-XCHECK FAIL halt segment flags={loads[0].split()[-2]} expected=R E"
    if pin:
        HALT.write_bytes(halt)
    return f"ELF-HALT bytes={len(halt)} entry=0x{ENTRY:x} OK"


def record(logs, verdicts):
    paths = [p for p in (ROOT / "elf").rglob("*.bend")]
    paths.extend(p for p in REF.iterdir() if p.is_file())
    paths.extend(ROOT / p for p in PINS)
    data = {"version": 1, "scope": "Stage C encoder cross-check (unit C2)", "verdicts": verdicts,
            "rows": {"dossier": sum(1 for name, kind, asm in ROWS if kind == "dossier"),
                     "object": sum(1 for name, kind, asm in ROWS if kind == "object")},
            "implementation_sha256": {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in sorted(set(paths))},
            "logs_sha256": {p.name: digest(p.read_bytes()) for p in sorted(logs.glob("*.log"))}}
    (ROOT / "dev/validation/enc-xcheck.json").write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assemble", action="store_true", help="assemble and pin the reference objects")
    parser.add_argument("--pin", action="store_true", help="rewrite corpus/halt.elf from the encoder")
    parser.add_argument("--record", action="store_true", help="write dev/validation/enc-xcheck.json")
    args = parser.parse_args()
    logs = ROOT / ("dev/validation/enc-xcheck" if args.record else ".gatework/enc-xcheck")
    logs.mkdir(parents=True, exist_ok=True)
    try:
        if args.assemble:
            assemble(logs)
        if not MANIFEST.is_file():
            raise GateError("corpus/ref/manifest.json is missing: run with --assemble once")
        rows, halt = our_rows(logs)
        # Order: widths, then the row words, then the HALT image.  A mutant of
        # the addi encoder also changes the HALT bytes, so the row verdict
        # must come first to name the instruction.
        objects = check_objects(rows, logs)
        verdicts = [v for v in (check_widths(rows), objects if " FAIL" in objects else None) if v is not None]
        if not verdicts:
            verdicts.append(check_halt(halt, args.pin, logs))
            if " FAIL" not in verdicts[-1]:
                verdicts.append(objects)
        for verdict in verdicts:
            print(verdict)
        (logs / "enc-xcheck.log").write_text("".join(v + "\n" for v in verdicts))
        if any(" FAIL" in v for v in verdicts):
            return 1
        if args.record:
            record(logs, verdicts)
        return 0
    except (OSError, ValueError, GateError, subprocess.TimeoutExpired) as error:
        print(f"ENC-XCHECK FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
