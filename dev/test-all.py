#!/usr/bin/env python3
"""Run the preserved regression suite and the Bend implementation tests."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
PROGRAMS = (
    ("test/main.exe", "test"),
    ("test/foundation.exe",), ("test/global_map.exe",), ("test/order.exe",), ("test/kernel.exe",),
    ("test/sl_surface.exe",),
    ("erase/test/ir_test.exe",), ("erase/test/repr_test.exe",),
    ("erase/test/inline_scan.exe",), ("erase/test/inline_sealing.exe",),
    ("erase/test/opaque_core.exe",), ("erase/test/budget_test.exe",),
    ("erase/test/refusal_test.exe",),
    ("erase/test/prop_index.exe",), ("erase/test/opaque_test.exe",),
    ("erase/test/inline_test.exe",),
)

def main():
    for relative, *arguments in PROGRAMS:
        program = ROOT / "_build/default" / relative
        result = subprocess.run([str(program), *arguments], cwd=ROOT)
        if result.returncode:
            print(f"TESTS FAIL program={relative} exit={result.returncode}", file=sys.stderr)
            return 1
    print(f"TESTS programs={len(PROGRAMS)} OK")
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except OSError as error:
        print(f"TESTS FAIL: {error}", file=sys.stderr)
        sys.exit(1)
