#!/usr/bin/env python3
"""Keep shape names in their owners, and keep every SPEC.md shape naming
tied to the refusal row that cites its milestone and its refusing module."""

from pathlib import Path
import re
import sys

SHAPES = r"SColl|SMu|SNu|SPar|SPi"
ROW = re.compile(r"^\|\s*`(" + SHAPES + r")\b[^`]*`\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*$")


def declared_shapes(root):
    """Read constructors only from the Bend shape type declaration."""
    text = (root / "lib/foundation.bend").read_text()
    block = re.search(r"^type Shape\.t[^\n]*:\n((?:  [^\n]*\n)+)", text, re.M)
    if block is None:
        raise ValueError("missing Shape.t declaration")
    return re.findall(r"^  Shape\.([A-Z][A-Za-z0-9_]*)\{", block.group(1), re.M)


def table_rows(spec):
    """The rows of the shape refusal table of SPEC.md section 2.1."""
    rows = []
    inside = False
    for number, line in enumerate(spec.splitlines(), 1):
        if line.startswith("### 2.1 Shapes"):
            inside = True
        elif inside and line.startswith("#"):
            inside = False
        elif inside:
            match = ROW.match(line)
            if match:
                rows.append((number, match.group(1), match.group(2), match.group(3)))
    return rows


def listed(spec, key):
    """The names printed after `key` inside the R0 counts block."""
    match = re.search(r"^" + key + r" \d+: (.*)$", spec, re.M)
    return match.group(1).split() if match else []


def audit_spec(root):
    """Every naming of a shape in SPEC.md carries its refusal citation:  a
    row that names the milestone and the module that refuses the shape."""
    spec = (root / "SPEC.md").read_text()
    rows = table_rows(spec)
    bad = []
    named = [name for _number, name, _milestone, _refuser in rows]
    for number, name, milestone, refuser in rows:
        if not re.fullmatch(r"M[0-9]", milestone):
            bad.append(f"SPEC.md:{number}: {name} names no milestone")
        if refuser != "admitted" and not (root / "lib" / refuser).exists():
            bad.append(f"SPEC.md:{number}: {name} cites the absent refuser {refuser}")
        if named.count(name) != 1:
            bad.append(f"SPEC.md:{number}: {name} has more than one refusal row")
    for name in declared_shapes(root):
        if name not in named:
            bad.append(f"SPEC.md: {name} of lib/foundation.bend has no refusal row")
    for name in named:
        if name not in declared_shapes(root):
            bad.append(f"SPEC.md: {name} is named with no constructor in lib/foundation.bend")
    admitted = [name for _number, name, _milestone, refuser in rows
                if refuser == "admitted"]
    if listed(spec, "shapes declared") != named:
        bad.append("SPEC.md: the declared shape list differs from the refusal table")
    if listed(spec, "shapes admitted") != admitted:
        bad.append("SPEC.md: the admitted shape list differs from the refusal table")
    return bad


def check(root):
    if not (root / "lib").is_dir():
        print("R0-AUDIT FAIL: missing lib")
        return 1
    allowed = {"lib/foundation.bend", "lib/kernel_rules.bend", "lib/kernel_pp.bend", "lib/erasure.bend"}
    bad = []
    for folder in ("lib", "erase", "lower", "elf", "emu", "host", "bin"):
        for path in (root / folder).rglob("*.bend"):
            relative = str(path.relative_to(root))
            if "test" in path.relative_to(root).parts:
                continue
            if relative not in allowed:
                for number, line in enumerate(path.read_text().splitlines(), 1):
                    if re.search(SHAPES, line):
                        bad.append(f"{relative}:{number}:{line}")
    bad.extend(audit_spec(root))
    for line in bad:
        print(line)
    print("R0-AUDIT " + ("FAIL" if bad else "OK"))
    return int(bool(bad))


if __name__ == "__main__":
    try:
        sys.exit(check(Path(sys.argv[1]).resolve()))
    except (OSError, ValueError) as error:
        print(f"R0-AUDIT FAIL: {error}")
        sys.exit(1)
