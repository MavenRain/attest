#!/usr/bin/env python3
"""Compare the entire inherited R0 block with the built driver."""
from pathlib import Path
import difflib
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
try:
    spec = (root / "SPEC.md").read_text()
    blocks = re.findall(r"^## R0 counts\n(?:(?!^## ).)*?^```[^\n]*\n(.*?)^```",
                        spec, re.M | re.S)
    if len(blocks) != 1:
        raise ValueError("expected exactly one fenced R0 counts block")
    result = subprocess.run([str(root / "_build/default/bin/attest.exe"), "spec-count"],
                            cwd=root, capture_output=True, text=True)
    if result.returncode != 0:
        raise ValueError(f"spec-count exit={result.returncode}: {result.stderr.strip()}")
    if result.stdout != blocks[0]:
        print("".join(difflib.unified_diff(blocks[0].splitlines(True),
                                         result.stdout.splitlines(True),
                                         fromfile="SPEC.md", tofile="attest spec-count")), end="")
        raise ValueError("inherited counts changed")
    print("R0-COUNT formers=2 schema=4 shapes=5 admitted=3 OK")
except (OSError, ValueError) as error:
    print(f"R0-COUNT FAIL: {error}")
    sys.exit(1)
