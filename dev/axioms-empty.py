#!/usr/bin/env python3
"""Require a nonempty accepted corpus with zero disclosed postulates."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
HALT_IMAGE = "corpus/halt.elf"
REFERENCE_SUFFIXES = (".s", ".o")


def encoder_fixture(relative):
    """Stage C fixtures under corpus/: the clang reference objects of corpus/ref/
    (one .s and one .o per row plus manifest.json) and the HALT ELF image.
    ENC-XCHECK pins and checks them; they carry no postulates."""
    path = Path(relative)
    in_reference = path.parts[:2] == ("corpus", "ref") and len(path.parts) == 3
    reference_file = path.suffix in REFERENCE_SUFFIXES or path.name == "manifest.json"
    return relative == HALT_IMAGE or (in_reference and reference_file)


try:
    accepted = (".att", ".kan")
    entries = sorted(p for p in (root / "corpus").rglob("*") if p.is_file())
    strangers = [str(p.relative_to(root)) for p in entries
                 if p.suffix not in accepted and not encoder_fixture(str(p.relative_to(root)))]
    if strangers:
        raise ValueError("unexpected corpus content: " + ", ".join(strangers))
    sources = [p for p in entries if p.suffix in accepted]
    if not sources:
        raise ValueError("accepted corpus is empty")
    for source in sources:
        relative = str(source.relative_to(root))
        result = subprocess.run([str(root / "_build/default/bin/attest.exe"),
                                 "check", "--axioms", relative],
                                cwd=root, capture_output=True, text=True)
        if result.returncode or result.stdout != f"AXIOMS {relative} count=0\n":
            print(result.stdout, end="")
            print(result.stderr, end="")
            raise ValueError(f"row={relative} exit={result.returncode}")
        print(result.stdout, end="")
    print(f"AXIOMS-empty rows={len(sources)} OK")
except (OSError, ValueError) as error:
    print(f"AXIOMS-empty FAIL: {error}")
    sys.exit(1)
