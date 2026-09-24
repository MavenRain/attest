#!/usr/bin/env python3
"""Refresh the explicit HOUSE site registry after reviewing source changes.

This is a maintenance command, never part of a build or gate. Review the diff
of the generated registry alongside each changed catch-all or unsafe function.
"""
import json
from pathlib import Path
import runpy

root = Path(__file__).resolve().parent.parent
sites = runpy.run_path(str(root / "dev/bend-source.py"))["policy_sites"](root)
record = {"version": 1,
          "scope": "Bend implementation and tests; file input has an explicit Result boundary.",
          "unsafe_meaning": "These scoped functions bypass Bend termination checking for unbounded interpreters and semantic recursion. Type, affine-use and exhaustiveness checks remain required.",
          "catchall_meaning": "These named sites implement scalar dispatch, parser fallback or explicit refusal. New sites require a reviewed registry change.",
          **sites}
target = root / "dev/bend-policy.json"
target.write_text(json.dumps(record, indent=2) + "\n")
print(f"HOUSE registry catchalls={len(sites['catchalls'])} unsafe={len(sites['unsafe'])}")
