#!/usr/bin/env python3
"""Verify the pinned carry and the exact, documented adaptation hashes."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import os
import subprocess
import sys

PIN = "eebe37e00ecb7fdce739c49f50a6dd49c45022b1"
DEFAULT_PINS = {
    "assay": Path("/Users/oobi/Documents/kan-sp1-lang-assay-pin"),
    "mechanism": Path("/Users/oobi/Documents/kan-sp1-lang-mech-pin"),
}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def check(root):
    manifest = json.loads((root / "dev/carry-manifest.json").read_text())
    if manifest["version"] != 1 or manifest["pins"]["assay"] != PIN:
        raise ValueError("unexpected carry manifest or assay revision")
    pin = (root / "dev/PIN").read_text().strip()
    if pin != PIN:
        print(f"PIN {pin} FAIL expected={PIN}")
        return 1
    entries = manifest["files"]
    paths = [entry["path"] for entry in entries]
    if len(paths) != len(set(paths)):
        raise ValueError("duplicate carry paths")
    for entry in entries:
        if entry["origin"] not in DEFAULT_PINS:
            raise ValueError(f'unknown carry origin: {entry["origin"]}')
        for key in ("path", "source"):
            path = PurePosixPath(entry[key])
            if path.is_absolute() or ".." in path.parts or str(path) != entry[key]:
                raise ValueError(f"invalid carry path: {entry[key]}")
    expected = set(paths)
    actual = {str(path.relative_to(root))
              for folder in ("lib", "surface", "test")
              for path in (root / folder).rglob("*") if path.is_file() or path.is_symlink()}
    extra = sorted(actual - expected)
    missing = []
    bad = []
    docs = (root / "CARRIED.md").read_text()
    for entry in entries:
        path = root / entry["path"]
        wanted = entry.get("adapted_sha256", entry["source_sha256"])
        if path.is_symlink() or not path.is_file() or digest(path.read_bytes()) != wanted:
            bad.append(entry["path"])
        if "adapted_sha256" in entry and f'| `{entry["path"]}` |' not in docs:
            bad.append(entry["path"] + ": undocumented adaptation")
    references = []
    for origin, default in DEFAULT_PINS.items():
        setting = os.environ.get("ATTEST_" + origin.upper() + "_PIN")
        pin_root = Path(setting) if setting else default
        if not pin_root.is_dir():
            if setting:
                raise ValueError(f"missing configured {origin} pin: {pin_root}")
            references.append(origin + ":manifest")
            continue
        selected = [entry for entry in entries if entry["origin"] == origin]
        revision = manifest["pins"][origin]
        requests = "".join(f'{revision}:{entry["source"]}\n' for entry in selected)
        result = subprocess.run(["git", "-C", str(pin_root), "cat-file", "--batch"],
                                input=requests.encode(), capture_output=True, check=True)
        data = result.stdout
        offset = 0
        for entry in selected:
            newline = data.index(b"\n", offset)
            header = data[offset:newline].split()
            if len(header) != 3 or header[1] != b"blob":
                raise ValueError(f'missing pinned blob: {entry["source"]}')
            size = int(header[2])
            start = newline + 1
            content = data[start:start + size]
            if len(content) != size or digest(content) != entry["source_sha256"]:
                bad.append(entry["path"] + ": source hash differs from pin")
            offset = start + size + 1
        if origin == "assay":
            listing = subprocess.run(["git", "-C", str(pin_root), "ls-tree", "-r", "-z", "--name-only",
                                      revision, "--", "lib", "surface", "test"],
                                     capture_output=True, check=True)
            pinned = {name.decode() for name in listing.stdout.split(b"\0") if name}
            carried = {entry["source"] for entry in selected}
            missing.extend(sorted(pinned - carried))
        references.append(origin + ":git")
    for name in bad + extra:
        print(f"CARRY FAIL path={name}")
    for name in missing:
        print(f"CARRY FAIL path={name}: pin file not carried")
    failed = bool(bad or extra or missing)
    print(f"CARRY files={len(entries)} diff={len(bad)} unlisted={len(extra)}"
          + (" FAIL" if failed else ""))
    print(f"PIN {PIN[:7]}")
    print("CARRY reference=" + ",".join(references))
    return int(failed)

if __name__ == "__main__":
    try:
        sys.exit(check(Path(sys.argv[1]).resolve()))
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f"CARRY FAIL: {error}")
        sys.exit(1)
