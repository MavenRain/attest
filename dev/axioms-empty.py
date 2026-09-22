#!/usr/bin/env python3
"""Require a nonempty accepted corpus with zero disclosed postulates."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
try:
    accepted = (".att", ".kan")
    entries = sorted(p for p in (root / "corpus").rglob("*") if p.is_file())
    strangers = [str(p.relative_to(root)) for p in entries
                 if p.suffix not in accepted]
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
