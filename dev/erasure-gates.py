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
               "local-proof-let-alias", "local-proof-let-family", "local-proof-let-universe",
               "branch-local-proof", "branch-dependent", "branch-nested",
               "branch-multi-ctor")
# The pairs in PARAMETER_ROWS and MOTIVE_ROWS already share a coarse runtime
# layout in the carried eraser, so their runtime rows do not discriminate: the
# gate exempts them from the carried runtime difference and requires the
# carried outputs to be equal. Their semantic suite rows seal a postulate and
# recheck its type. The gate requires the suite strings in PARAMETER_FIXTURES
# and MOTIVE_FIXTURES to equal the .att files byte for byte, and fixture_calls
# binds each exempt pair to one exact sealed Suite.Case line in Suite.cases.
# Each motive line and each plain parameter line calls Suite.local_sealed with
# a postulate count of 1n; branch-parameter-ctor and branch-parameter-universe
# use the exact helper calls in fixture_call_table.
PARAMETER_FIXTURES = Path("erase/test/parameter_fixtures.bend")
# Suite strings with no runtime pair; any other extra string is refused.
SUITE_ONLY_FIXTURES = frozenset(("Fixture.branch_parameter_ctor_last",
                                 "Fixture.branch_parameter_ctor_last_opaque"))
PARAMETER_ROWS = ("branch-parameter", "branch-parameter-dependent",
                  "branch-parameter-function", "branch-parameter-annotated",
                  "branch-parameter-let", "branch-parameter-global",
                  "branch-parameter-ctor", "branch-parameter-universe")
MOTIVE_FIXTURES = Path("erase/test/motive_fixtures.bend")
MOTIVE_ROWS = ("motive-index", "motive-self", "motive-dependent", "motive-parameter",
               "motive-parameter-indices", "motive-plain-local", "motive-plain-annotated",
               "motive-plain-global", "motive-plain-let", "motive-plain-dependent",
               "motive-application-global", "motive-application-dependent",
               "motive-application-local", "motive-application-curried",
               "motive-alias-global", "motive-alias-dependent",
               "motive-alias-local", "motive-alias-curried",
               "motive-let-dependent", "motive-let-curried",
               "motive-beta-dependent", "motive-beta-curried",
               "motive-annotation-dependent", "motive-annotation-curried")
LAMBDA_FIXTURES = Path("erase/test/lambda_fixtures.bend")
LAMBDA_ROWS = ("lambda-alias-global", "lambda-alias-dependent",
               "lambda-alias-local", "lambda-alias-curried",
               "lambda-let-global", "lambda-let-dependent",
               "lambda-let-local", "lambda-let-curried",
               "lambda-beta-global", "lambda-beta-dependent",
               "lambda-beta-local", "lambda-beta-curried",
               "lambda-annotation-global", "lambda-annotation-dependent",
               "lambda-annotation-local", "lambda-annotation-curried",
               "lambda-projection-global", "lambda-projection-dependent",
               "lambda-projection-local", "lambda-projection-curried",
               "lambda-case-global", "lambda-case-dependent",
               "lambda-case-local", "lambda-case-curried",
               "lambda-constructor-global", "lambda-constructor-dependent",
               "lambda-constructor-local", "lambda-constructor-curried",
               "lambda-parameter-global", "lambda-parameter-dependent",
               "lambda-parameter-local", "lambda-parameter-curried",
               "lambda-index-global", "lambda-index-dependent",
               "lambda-index-local", "lambda-index-curried",
               "lambda-recursive-global", "lambda-recursive-dependent",
               "lambda-recursive-local", "lambda-recursive-indexed",
               "lambda-index-alias-global", "lambda-index-alias-local",
               "lambda-index-reduction-let", "lambda-index-reduction-beta",
               "lambda-index-reduction-annotation", "lambda-index-reduction-projection",
               "lambda-sum-index-left", "lambda-sum-index-right",
               "lambda-constructor-index-empty", "lambda-constructor-index-value",
               "lambda-nested-index-empty", "lambda-nested-index-value",
               "lambda-neutral-index-left", "lambda-neutral-index-right")
INLINE_ROWS += LAMBDA_ROWS
# Suite rows the slice relies on; the count comes from the suite summary.
INLINE_SUITE_ROWS = frozenset(("let-body", "scrutinee-body", "inherited", "name-collision",
                               "family-collision", "runtime", "local-type", "rows", "binders",
                               *MOTIVE_ROWS, "motive-guards", "motive-quantities",
                               "motive-plain-guards", "motive-plain-quantity",
                               "application-capture", "application-guards",
                               "alias-global", "alias-local", "alias-guards",
                               "alias-local-global", "alias-fuel",
                               *LAMBDA_ROWS, "lambda-alias-guards", "lambda-alias-scope",
                               "let-source-syntax", "let-source-guards", "let-source-fuel",
                               "lambda-let-scope",
                               "beta-source-syntax", "beta-source-guards", "beta-source-fuel", "beta-source-cycles",
                               "source-size-bound", "annotation-source-syntax", "annotation-source-guards", "annotation-source-fuel",
                               "projection-source-syntax", "projection-source-guards", "projection-source-fuel",
                               "case-source-syntax", "case-source-guards", "case-source-scope",
                               "case-source-fuel", "case-source-pending",
                               "constructor-source-syntax", "constructor-source-guards",
                               "constructor-source-metadata", "constructor-source-scope",
                               "constructor-source-fuel", "constructor-source-pending",
                               "parameter-source-syntax", "parameter-source-guards",
                               "parameter-source-scope", "parameter-source-metadata", "parameter-source-fuel",
                               "parameter-introductions",
                               "index-source-syntax", "index-source-motive",
                               "index-source-metadata", "index-source-shapes",
                               "index-source-scope", "index-source-fuel",
                               "recursive-source-syntax", "recursive-source-metadata",
                               "recursive-source-scope", "recursive-source-fuel",
                               "index-alias-source-syntax", "index-alias-source-local",
                               "index-alias-source-guards", "index-alias-source-fuel",
                               "index-reduction-source-syntax", "index-reduction-source-local",
                               "index-reduction-source-guards", "index-reduction-source-fuel",
                               "sum-index-source-syntax", "sum-index-source-local",
                               "sum-index-source-guards", "sum-index-source-fuel",
                               "constructor-index-source-syntax", "constructor-index-source-scope",
                               "constructor-index-source-guards", "constructor-index-source-metadata",
                               "constructor-index-source-fuel",
                               "nested-index-source-syntax", "nested-index-source-guards",
                               "nested-index-source-fuel", "nested-index-source-steps",
                               "neutral-index-source-syntax", "neutral-index-source-local",
                               "neutral-index-source-guards", "neutral-index-source-fuel",
                               "neutral-index-source-steps", "neutral-index-source-size",
                               "motive", "shape-payload", "redeclared", "payload-postulates",
                               "local-index", "local-dependent", "local-let", "local-diagram",
                               "local-inherited", "local-poison", "local-universe", "local-payload",
                               "branch-scope", "branch-dependent", "branch-nested", "branch-metadata", "branch-fallback",
                               "branch-multi-ctor", "alias-leg-scope",
                               "branch-parameter", "branch-parameter-dependent", "branch-parameter-function",
                               "branch-parameter-annotated", "branch-parameter-let", "branch-parameter-global",
                               "branch-parameter-ctor", "branch-parameter-universe", "branch-parameter-guards",
                               "local-runtime-call", "local-let-alias",
                               "local-hypothesis", "local-proof-let",
                               "local-proof-let-value", "local-proof-let-type",
               "local-proof-let-alias", "local-proof-let-family", "local-proof-let-universe"))
# Original Prop-index cases are required individually, including all refusal rows.
PROP_SUITE_ROWS = frozenset(('nat-index',
 'high-universe-index',
 'dependent-indices',
 'reordered-indices',
 'annotated-index',
 'accessibility-family',
 'indexed-singleton-elimination',
 'erased-index-read',
 'annotated-index-type',
 'result-index-type',
 'runtime-index',
 'type-index-bound',
 'type-field-bound',
 'unindexed-proof-field',
 'runtime-proof-field',
 'constant-result-index',
 'computed-result-index',
 'unindexed-first-field',
 'unindexed-last-field',
 'ill-typed-index',
 'index-twice',
 'index-in-later-field',
 'prop-typed-index',
 'parameter-index',
 'computed-application-index',
 'type-1-index-bound',
 'parameter-hidden-field',
 'recursive-big-later-field'))
# New frontier rows must reproduce a difference before they are added here.
OPEN_ROWS = {}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def execute(logs, name, command, expected=0):
    result = subprocess.run(command, cwd=ROOT, capture_output=True,
                            timeout=900 if name == "BUILD" else 120)
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
    execute(logs, "BUILD", ["python3", "-P", "dev/build.py", "--backend", "js",
                            "attest", "erase-probe", "prop-index", "opaque", "inline"])
    indices = execute(logs, "PROP-INDEX", ["_build/default/erase/test/prop_index.exe"])
    if indices.stderr:
        raise ValueError(f"PROP-INDEX unexpected diagnostics: {indices.stderr[:200]!r}")
    last = indices.stdout.rstrip(b"\n").rsplit(b"\n", 1)[-1]
    summary = re.fullmatch(rb"PROP-INDEX pass=(\d+) total=(\d+) OK", last)
    labels = [match[1].decode() for line in indices.stdout.splitlines()[:-1]
              if (match := re.fullmatch(rb"PROP-INDEX row=(\S+) OK .+", line))]
    rows = len(indices.stdout.splitlines()) - 1
    if (summary is None or int(summary[1]) != int(summary[2])
            or int(summary[2]) != rows or len(labels) != rows
            or len(set(labels)) != rows or set(labels) != PROP_SUITE_ROWS):
        raise ValueError(f"PROP-INDEX summary mismatch rows={rows} last={last!r}")
    print(last.decode())
    unit = execute(logs, "OPAQUE-ERASE", ["_build/default/erase/test/opaque_test.exe"])
    if unit.stderr or unit.stdout != b"OPAQUE-ERASE pass=6 fail=0\n":
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
    # Each argument is a distinct name from the proof span. Argument order
    # is not compared here: a dependent twin such as `proof n h` for
    # `(h : Equal n)` names the index before the proof that it indexes. The
    # branch-nested pair gives its binders distinct types, so a permuted
    # application fails the check instead.
    args = use[1:]
    applied = (group and bool(use) and use[0] == postulate
               and len(set(args)) == len(args)
               and all(re.fullmatch(r"[\w']+", token) and token in proof for token in args))
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


def row_groups(inline, parameter, suite_rows):
    """The two runtime groups are disjoint, and each parameter pair has a
    semantic suite row, since only that row checks its sealing."""
    both = sorted(set(inline) & set(parameter))
    unchecked = sorted(set(parameter) - suite_rows)
    if both or unchecked or len(set(parameter)) != len(parameter):
        raise ValueError(f"PARAMETER_ROWS overlap INLINE_ROWS={both} "
                         f"without a suite row={unchecked}")


def fixture_name(row):
    return "Fixture." + row.replace("-", "_")


def suite_fixtures(path):
    """Read the Fixture.* source strings of the semantic suite. The strings
    use only the newline escape; any other escape is refused."""
    text = path.read_text()
    found = re.findall(r'^def (Fixture\.\w+)\(\) -> String:\n  "((?:[^"\\\n]|\\n)*)"\n', text, flags=re.M)
    names = [name for name, _ in found]
    if len(names) != len(set(names)) or len(names) != len(re.findall(r"^def ", text, flags=re.M)):
        raise ValueError(f"{path.relative_to(ROOT)} has an unreadable or repeated fixture")
    return {name: value.replace("\\n", "\n").encode() for name, value in found}


def fixture_matches(name, body, opaque, suite, source=PARAMETER_FIXTURES):
    """The semantic suite must check the same sources as the runtime pair."""
    pairs = ((body, fixture_name(name)), (opaque, fixture_name(name) + "_opaque"))
    drift = [str(path) for path, key in pairs if (ROOT / path).read_bytes() != suite[key]]
    if drift:
        raise ValueError(f"row={name} fixture differs from {source}: {drift}")


SUITE_SOURCE = Path("erase/test/inline_test.bend")


def sealed_call(prefix, name, layout):
    fixture = fixture_name(name)
    return (f'Suite.Case{{"{name}",unit=>Suite.local_sealed('
            f'{prefix}.{fixture},{prefix}.{fixture}_opaque,{layout},1n)}}')


def fixture_call_table():
    """The exact Suite.Case line of each parameter, motive, and lambda pair."""
    universe = fixture_name("branch-parameter-universe")
    special = {"branch-parameter-ctor":
                   'Suite.Case{"branch-parameter-ctor",unit=>Suite.parameter_ctors(layout)}',
               "branch-parameter-universe":
                   ('Suite.Case{"branch-parameter-universe",unit=>Suite.sealed_syntax('
                    f'PF.{universe},PF.{universe}_opaque,layout)}}')}
    parameter = [(name, "parameter", special.get(name, sealed_call("PF", name, "layout")))
                 for name in PARAMETER_ROWS]
    motive = [(name, "motive", sealed_call("MF", name, "None{}")) for name in MOTIVE_ROWS]
    alias_calls = {
        name: (f'Suite.Case{{"{name}",unit=>Suite.index_alias_sealed('
               f'LF.{fixture_name(name)},LF.{fixture_name(name)}_opaque,layout,1n,{local})}}')
        for name, local in (("lambda-index-alias-global", "False{}"),
                            ("lambda-index-alias-local", "True{}"))
    }
    alias_calls.update({
        f"lambda-index-reduction-{kind}":
            (f'Suite.Case{{"lambda-index-reduction-{kind}",unit=>Suite.index_reduction_sealed('
             f'LF.{fixture_name(f"lambda-index-reduction-{kind}")},'
             f'LF.{fixture_name(f"lambda-index-reduction-{kind}")}_opaque,layout,{mode}n)}}')
        for mode, kind in enumerate(("let", "beta", "annotation", "projection"))
    })
    alias_calls.update({
        f"lambda-sum-index-{side}":
            (f'Suite.Case{{"lambda-sum-index-{side}",unit=>Suite.index_reduction_sealed('
             f'LF.{fixture_name(f"lambda-sum-index-{side}")},'
             f'LF.{fixture_name(f"lambda-sum-index-{side}")}_opaque,layout,{mode}n)}}')
        for mode, side in ((4, "left"), (5, "right"))
    })
    alias_calls.update({
        f"lambda-constructor-index-{kind}":
            (f'Suite.Case{{"lambda-constructor-index-{kind}",unit=>Suite.index_reduction_sealed('
             f'LF.{fixture_name(f"lambda-constructor-index-{kind}")},'
             f'LF.{fixture_name(f"lambda-constructor-index-{kind}")}_opaque,layout,{mode}n)}}')
        for mode, kind in ((6, "empty"), (7, "value"))
    })
    alias_calls.update({
        f"lambda-nested-index-{kind}":
            (f'Suite.Case{{"lambda-nested-index-{kind}",unit=>Suite.index_reduction_sealed('
             f'LF.{fixture_name(f"lambda-nested-index-{kind}")},'
             f'LF.{fixture_name(f"lambda-nested-index-{kind}")}_opaque,layout,{mode}n)}}')
        for kind, mode in (("empty", 8), ("value", 9))
    })
    alias_calls.update({
        f"lambda-neutral-index-{side}":
            (f'Suite.Case{{"lambda-neutral-index-{side}",unit=>Suite.index_reduction_sealed('
             f'LF.{fixture_name(f"lambda-neutral-index-{side}")},'
             f'LF.{fixture_name(f"lambda-neutral-index-{side}")}_opaque,layout,{mode}n)}}')
        for side, mode in (("left", 10), ("right", 11))
    })
    lambdas = [(name, "lambda", alias_calls.get(name, sealed_call("LF", name, "layout")))
               for name in LAMBDA_ROWS]
    return parameter + motive + lambdas


def def_body(source, name):
    """The whitespace-free lines of the one definition NAME, without its def
    line and without comment lines."""
    bodies = re.findall(rf"^def {re.escape(name)}\(.*?(?=^def |\Z)", source, flags=re.M | re.S)
    if len(bodies) != 1:
        raise ValueError(f"{SUITE_SOURCE} must define {name} exactly once")
    lines = [re.sub(r"\s+", "", line) for line in bodies[0].split("\n")[1:]]
    return [line for line in lines if line and not line.startswith("#")]


# The helper of branch-parameter-ctor seals these two pairs, in this order.
PARAMETER_CTOR_BODY = [
    "doResult<&2,&2,F.Error.t,Unit>:",
    "first:Unit<-Suite.local_sealed(PF.Fixture.branch_parameter_ctor,"
    "PF.Fixture.branch_parameter_ctor_opaque,layout,1n)",
    "Suite.local_sealed(PF.Fixture.branch_parameter_ctor_last,"
    "PF.Fixture.branch_parameter_ctor_last_opaque,layout,1n)"]


def fixture_calls():
    """Bind each listed runtime pair to the live case of the same name: the
    body of def Suite.cases must hold exactly one Case line for the row, and
    that line must call the exact source pair and sealing count. A copy of
    the line in other code or in a comment does not count."""
    source = (ROOT / SUITE_SOURCE).read_text()
    cases = def_body(source, "Suite.cases")
    for name, kind, expected in fixture_call_table():
        rows = [line.strip("[],") for line in cases if f'Suite.Case{{"{name}",' in line]
        if rows != [expected]:
            raise ValueError(f"row={name} {kind} fixture call differs")
    if def_body(source, "Suite.parameter_ctors") != PARAMETER_CTOR_BODY:
        raise ValueError("row=branch-parameter-ctor parameter fixture call differs")


def inline_rows(logs):
    unit = execute(logs, "INLINE-ERASE", ["_build/default/erase/test/inline_test.exe"])
    lines = unit.stdout.rstrip(b"\n").split(b"\n")
    rows = [re.fullmatch(rb"INLINE-ERASE row=(\S+) OK", line) for line in lines[:-1]]
    names = [row[1].decode() for row in rows if row is not None]
    summary = re.fullmatch(rb"INLINE-ERASE pass=(\d+) total=(\d+) OK", lines[-1])
    if (unit.stderr or summary is None or not names or len(names) != len(rows)
            or int(summary[1]) != int(summary[2]) or int(summary[2]) != len(names)
            or len(set(names)) != len(names)):
        raise ValueError(f"INLINE-ERASE summary mismatch rows={len(names)} last={lines[-1]!r}")
    missing = sorted(INLINE_SUITE_ROWS - set(names))
    if missing:
        raise ValueError(f"INLINE-ERASE rows missing: {missing}")
    print(lines[-1].decode())
    row_groups(INLINE_ROWS, PARAMETER_ROWS + MOTIVE_ROWS, INLINE_SUITE_ROWS)
    suite = suite_fixtures(ROOT / PARAMETER_FIXTURES)
    fixture_names = {fixture_name(name) + suffix for name in PARAMETER_ROWS for suffix in ("", "_opaque")}
    if set(suite) != fixture_names | SUITE_ONLY_FIXTURES or fixture_names & SUITE_ONLY_FIXTURES:
        raise ValueError(f"{PARAMETER_FIXTURES} fixtures differ from PARAMETER_ROWS: "
                         f"extra={sorted(set(suite) - fixture_names - SUITE_ONLY_FIXTURES)} "
                         f"missing={sorted((fixture_names | SUITE_ONLY_FIXTURES) - set(suite))}")
    motive_suite = suite_fixtures(ROOT / MOTIVE_FIXTURES)
    motive_names = {fixture_name(name) + suffix for name in MOTIVE_ROWS for suffix in ("", "_opaque")}
    if set(motive_suite) != motive_names:
        raise ValueError(f"{MOTIVE_FIXTURES} fixtures differ from MOTIVE_ROWS")
    lambda_suite = suite_fixtures(ROOT / LAMBDA_FIXTURES)
    lambda_names = {fixture_name(name) + suffix for name in LAMBDA_ROWS for suffix in ("", "_opaque")}
    if set(lambda_suite) != lambda_names:
        raise ValueError(f"{LAMBDA_FIXTURES} fixtures differ from LAMBDA_ROWS")
    fixture_calls()
    records = []
    for name in INLINE_ROWS + PARAMETER_ROWS + MOTIVE_ROWS:
        body = Path("fixtures/erasure") / (name + ".att")
        opaque = body.with_name(name + "-opaque.att")
        twin_structure(name, body, opaque)
        if name in PARAMETER_ROWS:
            fixture_matches(name, body, opaque, suite)
        if name in MOTIVE_ROWS:
            fixture_matches(name, body, opaque, motive_suite, MOTIVE_FIXTURES)
        if name in LAMBDA_ROWS:
            fixture_matches(name, body, opaque, lambda_suite, LAMBDA_FIXTURES)
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
        carried_diff = before_a != before_b
        if b"fun keep " not in before_b:
            raise ValueError(f"row={name} carried eraser gave no runtime keep")
        if name in INLINE_ROWS and not carried_diff:
            raise ValueError(f"row={name} carried eraser did not reproduce the inline regression")
        if name in PARAMETER_ROWS + MOTIVE_ROWS and carried_diff:
            raise ValueError(f"row={name} carried eraser now differs: move the row into INLINE_ROWS")
        records.append({"row": name,
                        "expected": "runtime-identical" if name in INLINE_ROWS else "runtime-identical-coarse",
                        "carried_diff": carried_diff,
                        "body_sha256": digest((ROOT / body).read_bytes()),
                        "opaque_sha256": digest((ROOT / opaque).read_bytes()),
                        "runtime_sha256": digest(a)})
    print(f"ERASURE-INLINE rows={len(records)} identical={len(records)} "
          f"carried_diff={sum(row['carried_diff'] for row in records)} "
          f"parameter_pairs={len(PARAMETER_ROWS)} motive_pairs={len(MOTIVE_ROWS)} "
          f"not_discriminating={len(PARAMETER_ROWS) + len(MOTIVE_ROWS)} "
          f"suite_fixtures={len(fixture_names) + len(motive_names) + len(lambda_names)} OK")
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
    for folder in ("lib", "surface", "bin", "erase"):
        paths.extend((ROOT / folder).rglob("*.bend"))
    for folder in ("fixtures/erasure", "AttestTwin", "twin"):
        paths.extend(p for p in (ROOT / folder).rglob("*") if p.is_file())
    paths.extend(ROOT / p for p in ("dev/erasure-gates.py", "dev/erase_probe.bend", "dev/build.py",
        "dev/gates.sh", "dev/cc.py", "dev/bend-toolchain.json", "dev/setup-bend.sh", "Makefile", "AttestTwin.lean",
        "lakefile.toml", "lean-toolchain", "lake-manifest.json", "dev/carry-manifest.json",
        "dev/bend-migration.json"))
    data = {"version": 1, "scope": "Stage B erasure increment", "stage_b": "OPEN",
            "rows": rows, "open": ["Acc erased proof binder and recursive proof elimination",
            "full TRACE-ERASURE including Acc",
            "constructor branch and named motive scopes without source syntax for family parameters",
            "unnamed motive scopes without a source scrutinee type",
            "lambda scopes whose expected type needs normalization beyond transparent alias hops and bounded head annotation, let, beta, tuple projection, finite case, and constructor case reduction",
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
