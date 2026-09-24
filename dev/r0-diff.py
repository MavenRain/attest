#!/usr/bin/env python3
"""Check historical R0 provenance and the pinned Bend replacement sources.

The reference table dev/r0-diff/SHA256 is tied to three sources: the assay
carry hashes in dev/carry-manifest.json, the removed-source migration record,
and the kanon blobs at the manifest's kanon pin. The kanon comparison reads the
checkout named by ATTEST_KANON_PIN (default DEFAULT_KANON_PIN); when the default
checkout is absent the record falls back to the manifest hashes and says so.
Semantic checks run separately through R0-COUNT, R0-AUDIT, and the differential corpus.
"""
from functools import reduce
from pathlib import Path
import hashlib
import json
import os
import runpy
import subprocess
import sys

DEFAULT_KANON_PIN = Path("/Users/oobi/Documents/kanon")

root = Path(__file__).resolve().parent.parent
names = {"term.ml", "shape.ml", "spec_count.ml"}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def split_blob(data, label):
    """Split one `cat-file --batch` record off the front of data: (sha256, rest)."""
    header, _, body = data.partition(b"\n")
    fields = header.split()
    size = int(fields[2]) if len(fields) == 3 and fields[1] == b"blob" else -1
    content = body[:max(size, 0)]
    if len(content) != size:
        raise ValueError(f"missing or truncated pinned kanon blob: {label}")
    return digest(content), body[size + 1:]

def kanon_blobs(pin_root, revision, order):
    """Return name -> sha256 of the pinned kanon blobs, read in the requested order."""
    requests = "".join(f"{revision}:lib/{name}\n" for name in order)
    result = subprocess.run(["git", "-C", str(pin_root), "cat-file", "--batch"],
                            input=requests.encode(), capture_output=True, check=True)
    def step(state, name):
        hashes, rest = state
        blob, remaining = split_blob(rest, f"{revision[:7]}:lib/{name}")
        return {**hashes, name: blob}, remaining
    hashes, _ = reduce(step, order, ({}, result.stdout))
    return hashes

try:
    reference = root / "dev/r0-diff"
    rows = [line.split() for line in (reference / "SHA256").read_text().splitlines()]
    if len(rows) != 3 or any(len(row) != 2 for row in rows):
        raise ValueError("invalid R0 reference checksum table")
    if {row[1] for row in rows} != names:
        raise ValueError("incomplete R0 reference checksum table")
    manifest = json.loads((root / "dev/carry-manifest.json").read_text())
    originals = {entry["path"]: entry["source_sha256"] for entry in manifest["files"]}
    revision = manifest["pins"]["kanon"]
    if len(revision) != 40 or any(c not in "0123456789abcdef" for c in revision):
        raise ValueError("invalid kanon pin in the carry manifest")
    setting = os.environ.get("ATTEST_KANON_PIN")
    pin_root = Path(setting) if setting else DEFAULT_KANON_PIN
    if pin_root.is_dir():
        pinned = kanon_blobs(pin_root, revision, [row[1] for row in rows])
        source_of_truth = "kanon:git"
    elif setting:
        raise ValueError(f"missing configured kanon pin: {pin_root}")
    else:
        pinned = {}
        source_of_truth = "kanon:manifest"
    bad = []
    migration = runpy.run_path(str(root / "dev/bend-migration.py"))["validate"](root)
    removed = {entry["path"]: entry for entry in migration["removed"]}
    for expected, name in rows:
        if expected != originals["lib/" + name]:
            raise ValueError(f"{name}: reference hash differs from the pinned carry")
        if name in pinned and pinned[name] != expected:
            bad.append(name + ": kanon blob")
        if removed["dev/r0-diff/" + name]["sha256"] != expected:
            bad.append(name + ": historical reference checksum")
        if removed["lib/" + name]["sha256"] != expected:
            bad.append(name + ": migration source checksum")
    for name in bad:
        print(f"R0-DIFF FAIL row={name}")
    print(f"R0-DIFF vs={revision[:7]} rows=3 diff={len(bad)}" + (" FAIL" if bad else " OK"))
    print(f"R0-DIFF reference={source_of_truth}")
    print("R0-DIFF mode=Bend-provenance semantic-checks=R0-COUNT,R0-AUDIT,differential")
    sys.exit(int(bool(bad)))
except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
    print(f"R0-DIFF FAIL: {error}")
    sys.exit(1)
