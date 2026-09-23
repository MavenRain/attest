#!/usr/bin/env python3
"""Validate the erasure increment; the full Stage B gate remains explicit."""
from functools import reduce
from itertools import accumulate
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
DRIVER = "_build/default/bin/attest.exe"
ROWS = {"f2-a": ("proof",), "f2-b": ("proof",),
        "proof-alias": ("proof", "alias"), "proof-function": ("proof",)}
INLINE_ROWS = ("let-proof", "scrutinee-proof", "projection-proof", "projection-second-proof",
               "lambda-proof", "binder-proof", "local-proof", "local-dependent",
               "local-let", "local-let-alias", "local-diagram", "local-runtime-call",
               "local-proof-let-value", "local-proof-let-type",
               "local-proof-let-alias", "local-proof-let-family", "local-proof-let-universe")
# Suite rows the slice relies on; the count comes from the suite summary.
INLINE_SUITE_ROWS = frozenset(("let-body", "scrutinee-body", "inherited", "name-collision",
                               "family-collision", "runtime", "local-type", "rows", "binders",
                               "motive", "shape-payload", "redeclared", "payload-postulates",
                               "local-index", "local-dependent", "local-let", "local-diagram",
                               "local-inherited", "local-poison", "local-universe", "local-payload",
                               "branch-scope", "local-runtime-call", "local-let-alias",
                               "local-hypothesis", "local-proof-let",
                               "local-proof-let-value", "local-proof-let-type",
               "local-proof-let-alias", "local-proof-let-family", "local-proof-let-universe"))
# Constructor branch binders still lack a local telescope (SPEC.md 1.1).
OPEN_ROWS = {"branch-local-proof": "proof depending on a constructor branch index"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def execute(logs, name, command, expected=0):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=60)
    (logs / (name + ".log")).write_bytes(result.stdout + result.stderr)
    if result.returncode != expected:
        raise ValueError(f"{name} exit={result.returncode} expected={expected}; "
                         f"log={logs.relative_to(ROOT) / (name + '.log')}")
    return result


def opaque_source(source, names):
    for name in names:
        source, count = re.subn(r"^def " + re.escape(name) + r" : (.+?) := .+$",
                                r"axiom " + name + r" : \1", source, flags=re.M)
        if count != 1:
            raise ValueError(f"proof replacement count={count} name={name}")
    return source


def regression(logs):
    execute(logs, "BUILD", ["zsh", "-f", "dev/dunecho.sh", "build"])
    indices = execute(logs, "PROP-INDEX", ["_build/default/erase/test/prop_index.exe"])
    if indices.stderr:
        raise ValueError(f"PROP-INDEX unexpected diagnostics: {indices.stderr[:200]!r}")
    last = indices.stdout.rstrip(b"\n").rsplit(b"\n", 1)[-1]
    summary = re.fullmatch(rb"PROP-INDEX pass=(\d+) total=(\d+) OK", last)
    rows = indices.stdout.count(b"PROP-INDEX row=")
    if (summary is None or int(summary[1]) != int(summary[2]) or int(summary[2]) <= 0
            or int(summary[2]) != rows):
        raise ValueError(f"PROP-INDEX summary mismatch rows={rows} last={last!r}")
    print(last.decode())
    unit = execute(logs, "OPAQUE-ERASE", ["_build/default/erase/test/opaque_test.exe"])
    if unit.stdout != b"OPAQUE-ERASE pass=6 fail=0\n":
        raise ValueError("incomplete opaque evaluator tests")
    records = []
    for name, proofs in ROWS.items():
        body = Path("fixtures/erasure") / (name + ".att")
        opaque = body.with_name(name + "-opaque.att")
        if not (ROOT / opaque).exists():
            raise ValueError(f"row={name} opaque twin missing")
        if opaque_source((ROOT / body).read_text(), proofs) != (ROOT / opaque).read_text():
            raise ValueError(f"row={name} opaque twin changes more than proof bodies")
        a = execute(logs, name + "-body", [DRIVER, "build", "--erase", str(body)]).stdout
        b = execute(logs, name + "-opaque", [DRIVER, "build", "--erase", str(opaque)]).stdout
        if not a or a != b or b"fun " not in a:
            offset = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
            raise ValueError(f"row={name} first_diff={offset} or empty runtime output")
        before_a = execute(logs, name + "-carried-body",
                           ["_build/default/dev/erase_probe.exe", str(body)]).stdout
        before_b = execute(logs, name + "-carried-opaque",
                           ["_build/default/dev/erase_probe.exe", str(opaque)]).stdout
        if not before_a or not before_b or before_a == before_b:
            raise ValueError(f"row={name} carried eraser did not reproduce the regression")
        records.append({"row": name, "body_sha256": digest((ROOT / body).read_bytes()),
                        "opaque_sha256": digest((ROOT / opaque).read_bytes()),
                        "erased_sha256": digest(a), "carried_diff": True,
                        "expected": "identical"})
    # Shape-insensitivity check, not a positive control: the closed proof of
    # f2-a-shape normalizes to refl, so the carried eraser agrees on it too.
    control = execute(logs, "proof-shape-control",
                      [DRIVER, "build", "--erase", "fixtures/erasure/f2-a-shape.att"])
    if control.stdout != (logs / "f2-a-body.log").read_bytes():
        raise ValueError("proof shape control changed erasure")
    print(f"ERASURE-REGRESSION rows={len(ROWS)} identical={len(records)} "
          f"carried_diff={len(records)} shape_insensitive=1 OK")
    return records


TWIN_TOKEN = re.compile(r"[\w']+|[^\s\w']")


def proof_span(postulate, before, after):
    """Compare the changed line token by token. Only one span may differ: the
    source span is one parenthesized proof, with optional projections, and the
    twin span applies the postulate to names from it, or the source span is
    one let of the postulate name that the twin drops, and nothing more."""
    a, b = TWIN_TOKEN.findall(before), TWIN_TOKEN.findall(after)
    head = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    tail = next((i for i, (x, y) in enumerate(zip(reversed(a[head:]), reversed(b[head:])))
                 if x != y), min(len(a), len(b)) - head)
    proof, use = a[head:len(a) - tail], b[head:len(b) - tail]
    depths = list(accumulate({"(": 1, ")": -1}.get(token, 0) for token in proof))
    close = next((i for i, depth in enumerate(depths) if depth == 0), None)
    projections = proof[close + 1:] if close is not None else []
    group = (bool(proof) and proof[0] == "(" and close is not None
             and len(projections) % 2 == 0
             and all(projections[i] == "." and projections[i + 1].isdigit()
                     for i in range(0, len(projections), 2)))
    applied = (group and bool(use) and use[0] == postulate
               and all(re.fullmatch(r"[\w']+", token) and token in proof for token in use[1:]))
    # A dropped span is exactly one let of the postulate name: one let token
    # and one in token, so a twin cannot drop an adjacent let with it.
    dropped = (not use and len(proof) > 3 and proof[0] == "let" and proof[1] == postulate
               and proof[-1] == "in" and proof.count("let") == 1 and proof.count("in") == 1)
    return applied or dropped


def twin_structure(name, body, opaque):
    """An inline twin adds one axiom line and changes exactly one other line,
    the line that holds the proof, and on that line only the proof span."""
    if not (ROOT / opaque).exists():
        raise ValueError(f"row={name} opaque twin missing")
    source = (ROOT / body).read_text().splitlines()
    twin = (ROOT / opaque).read_text().splitlines()
    axiom = re.compile(r"axiom (\S+) : .+")

    def fits(index):
        # Without the added axiom line, the twin must match the body except
        # for one line, and that line must name the added axiom.
        postulate = axiom.fullmatch(twin[index])[1]
        rest = twin[:index] + twin[index + 1:]
        changed = [(a, b) for a, b in zip(source, rest) if a != b]
        return (len(rest) == len(source) and len(changed) == 1
                and proof_span(postulate, *changed[0]))

    added = [i for i, line in enumerate(twin) if axiom.fullmatch(line) and line not in source]
    if sum(1 for index in added if fits(index)) != 1:
        raise ValueError(f"row={name} opaque twin changes more than its proof")


def runtime_output(output):
    return b"\n".join(line for line in output.splitlines() if not line.startswith(b"erased "))


def inline_rows(logs):
    unit = execute(logs, "INLINE-ERASE", ["_build/default/erase/test/inline_test.exe"])
    lines = unit.stdout.rstrip(b"\n").split(b"\n")
    rows = [re.fullmatch(rb"INLINE-ERASE row=(\S+) OK", line) for line in lines[:-1]]
    names = [row[1].decode() for row in rows if row is not None]
    summary = re.fullmatch(rb"INLINE-ERASE pass=(\d+) total=(\d+) OK", lines[-1])
    if (unit.stderr or summary is None or not names or len(names) != len(rows)
            or int(summary[1]) != int(summary[2]) or int(summary[2]) != len(names)):
        raise ValueError(f"INLINE-ERASE summary mismatch rows={len(names)} last={lines[-1]!r}")
    missing = sorted(INLINE_SUITE_ROWS - set(names))
    if missing:
        raise ValueError(f"INLINE-ERASE rows missing: {missing}")
    print(lines[-1].decode())
    records = []
    for name in INLINE_ROWS:
        body = Path("fixtures/erasure") / (name + ".att")
        opaque = body.with_name(name + "-opaque.att")
        twin_structure(name, body, opaque)
        a = runtime_output(execute(logs, name + "-body",
                           [DRIVER, "build", "--erase", str(body)]).stdout)
        b = runtime_output(execute(logs, name + "-opaque",
                           [DRIVER, "build", "--erase", str(opaque)]).stdout)
        if not a or a != b or b"fun keep " not in a or b"__attest_inline_proof_" in a:
            raise ValueError(f"row={name} inline proof changed runtime output")
        before_a = runtime_output(execute(logs, name + "-carried-body",
                           ["_build/default/dev/erase_probe.exe", str(body)]).stdout)
        before_b = runtime_output(execute(logs, name + "-carried-opaque",
                           ["_build/default/dev/erase_probe.exe", str(opaque)]).stdout)
        if before_a == before_b or b"fun keep " not in before_b:
            raise ValueError(f"row={name} carried eraser did not reproduce the inline regression")
        records.append({"row": name, "expected": "runtime-identical", "carried_diff": True,
                        "body_sha256": digest((ROOT / body).read_bytes()),
                        "opaque_sha256": digest((ROOT / opaque).read_bytes()),
                        "runtime_sha256": digest(a)})
    print(f"ERASURE-INLINE rows={len(INLINE_ROWS)} identical={len(records)} "
          f"carried_diff={len(records)} OK")
    return records


def open_rows(logs):
    records = []
    for name, path in OPEN_ROWS.items():
        body = Path("fixtures/erasure") / (name + ".att")
        opaque = body.with_name(name + "-opaque.att")
        a = runtime_output(execute(logs, name + "-body", [DRIVER, "build", "--erase", str(body)]).stdout)
        b = runtime_output(execute(logs, name + "-opaque", [DRIVER, "build", "--erase", str(opaque)]).stdout)
        if not a or not b or a == b:
            raise ValueError(f"row={name} frontier moved: {path} erases like its sealed twin; "
                             "close the SPEC.md 1.1 entry and move the row into INLINE_ROWS")
        # The frontier is the runtime function keep dropped from the body.
        if b"fun keep " in a:
            raise ValueError(f"row={name} frontier moved: {path} kept its runtime function; "
                             "close the SPEC.md 1.1 entry and move the row into INLINE_ROWS")
        if b"fun keep " not in b:
            raise ValueError(f"row={name} sealed twin regressed: {path} dropped keep")
        records.append({"row": name, "expected": "different", "path": path,
                        "body_sha256": digest((ROOT / body).read_bytes()),
                        "opaque_sha256": digest((ROOT / opaque).read_bytes()),
                        "erased_body_sha256": digest(a), "erased_opaque_sha256": digest(b)})
    print(f"ERASURE-OPEN rows={len(OPEN_ROWS)} different={len(records)} OPEN")
    return records


def cli_checks(logs):
    cases = [(["build"], 64, b"usage: attest"),
             (["build", "--erase", "README.md"], 64, b"expected a .att"),
             (["build", "--erase", ".gatework/no-such-erasure.att"], 64, b"attest: check:"),
             (["build", "--erase", "fixtures/ill-typed.att"], 1, b"attest: check:"),
             (["build", "--erase", "fixtures/erasure/opaque-layout-refusal.att"],
              2, b"a tuple stands at a type that is not a right former")]
    for i, (args, code, diagnostic) in enumerate(cases):
        result = execute(logs, f"CLI-{i}", [DRIVER, *args], code)
        if diagnostic not in result.stderr or b"fun " in result.stdout:
            raise ValueError(f"CLI-{i} diagnostic or output contract")
    execute(logs, "checked-layout", [DRIVER, "check", "fixtures/erasure/opaque-layout-refusal.att"])
    print(f"ERASURE-CLI pass={len(cases) + 1} fail=0 OK")


ALLOWED_AXIOMS = {"F2Fixture.opaqueProof", "AccFixture.R"}
TWINS = ("F2", "Acc")
NEGATIVE_TWINS = (("F2Neg", b"but is expected to have type\n  PUnit"),)
TACTIC_TOKENS = re.compile(r"\b(by|sorry|admit|native_decide)\b")
AXIOM_ROW = re.compile(r"^'([^']+)' (?:does not depend on any axioms|"
                       r"depends on axioms: \[([^\]]*)\])$", re.M)
KEYWORDS = r"theorem|def|axiom|lemma|abbrev|instance|opaque|structure|inductive|class"
DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*"
                         r"(?:" + KEYWORDS + r")\s+(\S+)")
KEYWORD_LINE = re.compile(r".*\b(?:" + KEYWORDS + r")\b")
IDENTIFIER = re.compile(r"^[A-Za-z_][\w.'!?]*$")
SCOPE_OPEN = re.compile(r"^(namespace|section)(?:\s+(\S+))?\s*$")
SCOPE_CLOSE = re.compile(r"^end(?:\s+(\S+))?\s*$")


def stripped(source):
    """Drop block and line comments so the guards read code only."""
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", source, flags=re.S))


def guard_tokens(name, source):
    token = TACTIC_TOKENS.search(stripped(source))
    if token:
        raise ValueError(f"twin/{name}.lean carries the token {token.group(1)}")


def toolchain(logs):
    pinned = (ROOT / "lean-toolchain").read_text().strip()
    ran = execute(logs, "LEAN-TOOLCHAIN", ["lake", "env", "lean", "--version"]).stdout.decode()
    found = re.search(r"Lean \(version ([0-9A-Za-z.\-]+)", ran)
    version = found.group(1) if found else ""
    if not version or pinned.rsplit(":v", 1)[-1] != version:
        raise ValueError(f"LEAN-TOOLCHAIN pinned={pinned} ran={ran.strip()}")
    print(f"LEAN-TOOLCHAIN pinned={pinned} ran={version} OK")


def open_scope(state, line, where):
    scopes, names = state
    found = SCOPE_OPEN.match(line)
    return scopes + [(found.group(1), found.group(2) or "")], names


def close_scope(state, line, where):
    scopes, names = state
    label = SCOPE_CLOSE.match(line).group(1) or ""
    if not scopes or scopes[-1][1] != label:
        raise ValueError(f"{where}: end {label} closes no open scope")
    return scopes[:-1], names


def add_declaration(state, line, where):
    scopes, names = state
    name = DECLARATION.match(line).group(1)
    if not IDENTIFIER.match(name):
        raise ValueError(f"{where}: unnamed declaration head {line.strip()!r}")
    prefix = "".join(label + "." for kind, label in scopes if kind == "namespace")
    return scopes, names + [prefix + name]


def reject_head(state, line, where):
    raise ValueError(f"{where}: declaration head not enumerated {line.strip()!r}")


def keep(state, line, where):
    return state


LINE_KINDS = ((SCOPE_OPEN, open_scope), (SCOPE_CLOSE, close_scope),
              (DECLARATION, add_declaration), (KEYWORD_LINE, reject_head))


def declarations(name, source):
    """Name every declaration of a comment-free module; an unparsed head fails closed."""
    def step(state, item):
        number, line = item
        handler = next((h for pattern, h in LINE_KINDS if pattern.match(line)), keep)
        return handler(state, line, f"twin/{name}.lean:{number}")
    return reduce(step, enumerate(source.splitlines(), 1), ([], []))[1]


def axioms(logs):
    scratch = ROOT / ".gatework/erasure-axioms"
    scratch.mkdir(parents=True, exist_ok=True)
    dump = b""
    found = set()
    total = 0
    for name in TWINS:
        source = (ROOT / "twin" / (name + ".lean")).read_text()
        guard_tokens(name, source)
        names = declarations(name, stripped(source))
        module = scratch / (name + ".lean")
        module.write_text(source + "".join(f"#print axioms {n}\n" for n in names))
        result = subprocess.run(["lake", "env", "lean", "-DwarningAsError=true",
                                 str(module.relative_to(ROOT))],
                                cwd=ROOT, capture_output=True, timeout=60)
        dump += result.stdout + result.stderr
        (logs / "LEAN-AXIOMS.log").write_bytes(dump)
        if result.returncode != 0:
            raise ValueError(f"LEAN-AXIOMS {name} exit={result.returncode}")
        reported = AXIOM_ROW.findall(result.stdout.decode())
        if [n for n, _ in reported] != names:
            raise ValueError(f"LEAN-AXIOMS {name} reported={len(reported)} declared={len(names)}")
        found.update(a.strip() for _, group in reported for a in group.split(",") if a.strip())
        total += len(names)
    extra = sorted(found - ALLOWED_AXIOMS)
    if extra:
        raise ValueError(f"LEAN-AXIOMS extra={extra}")
    print(f"LEAN-AXIOMS declarations={total} axioms={sorted(found)} extra=0 OK")


def twins(logs):
    builder = ["leancho", "AttestTwin"] if shutil.which("leancho") else ["lake", "build", "AttestTwin"]
    execute(logs, "LEAN-BUILD", builder)
    toolchain(logs)
    for name in TWINS:
        execute(logs, "LEAN-" + name, ["lake", "env", "lean", "-DwarningAsError=true",
                                       "twin/" + name + ".lean"])
        if (logs / ("LEAN-" + name + ".log")).read_bytes():
            raise ValueError(f"LEAN-{name} emitted diagnostics")
    for name, diagnostic in NEGATIVE_TWINS:
        guard_tokens(name, (ROOT / "twin" / (name + ".lean")).read_text())
        refused = execute(logs, "LEAN-" + name, ["lake", "env", "lean", "-DwarningAsError=true",
                                                 "twin/" + name + ".lean"], 1)
        if diagnostic not in refused.stdout:
            raise ValueError(f"LEAN-{name} was refused for a different reason")
    axioms(logs)
    execute(logs, "ACC-FAMILY", [DRIVER, "check", "fixtures/erasure/acc-family.att"])
    acc = execute(logs, "ACC-ATTEST", [DRIVER, "check", "fixtures/erasure/acc.att"], 1)
    if b"quantity: the erased binder accessible is read in a runtime position" not in acc.stderr:
        raise ValueError("Acc frontier changed; update the Stage B gate and corpus")
    recursive = execute(logs, "ACC-RECURSIVE",
                        [DRIVER, "check", "fixtures/erasure/acc-runtime-proof.att"], 1)
    if b"universe: a large elimination out of a proposition needs a subsingleton family at Acc" not in recursive.stderr:
        raise ValueError("Acc recursive elimination frontier changed")
    print(f"LEAN-ERASURE sources={len(TWINS) + len(NEGATIVE_TWINS)} "
          f"accepted={len(TWINS)} refused={len(NEGATIVE_TWINS)} OK")
    print("ACC-FAMILY accepted OK")
    print("ACC-FRONTIER lean=accepted attest=refused reason=proof-quantity OPEN")
    print("ACC-RECURSIVE attest=refused reason=recursive-singleton OPEN")


def record(logs, rows):
    paths = []
    for folder in ("lib", "surface", "bin", "erase", "fixtures/erasure", "AttestTwin", "twin"):
        paths.extend(p for p in (ROOT / folder).rglob("*") if p.is_file())
    paths.extend(ROOT / p for p in ("dev/erasure-gates.py", "dev/erase_probe.ml", "dev/dune",
        "dev/gates.sh", "dev/dunecho.sh", "test/sys_io.ml",
        "dune-project", "AttestTwin.lean",
        "lakefile.toml", "lean-toolchain", "lake-manifest.json", "dev/carry-manifest.json"))
    data = {"version": 1, "scope": "Stage B erasure increment", "stage_b": "OPEN",
            "rows": rows, "open": ["Acc erased proof binder and recursive proof elimination",
            "full TRACE-ERASURE including Acc",
            "proofs depending on constructor branch binders keep their bodies (row branch-local-proof)",
            "proofs depending on motive binders keep their bodies (no pinned row)",
            "lambda scopes without a syntactic expected function type",
            "local proofs without source type syntax",
            "unannotated proof introductions without an expected type and family metadata"],
            "implementation_sha256": {str(p.relative_to(ROOT)): digest(p.read_bytes())
                                      for p in sorted(set(paths))},
            "logs_sha256": {p.name: digest(p.read_bytes()) for p in sorted(logs.glob("*.log"))}}
    (ROOT / "dev/validation/erasure.json").write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("regression", "trace"), nargs="?", default="regression")
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    logs = ROOT / ("dev/validation/erasure" if args.record else ".gatework/erasure")
    logs.mkdir(parents=True, exist_ok=True)
    try:
        rows = regression(logs) + inline_rows(logs) + open_rows(logs)
        cli_checks(logs)
        twins(logs)
        if args.record:
            record(logs, rows)
        if args.mode == "trace":
            print("TRACE-ERASURE FAIL row=acc phase=check; Stage B remains OPEN")
            return 1
        print("ERASURE-INCREMENT OK; Stage B remains OPEN")
        return 0
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        print(f"ERASURE-INCREMENT FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
