# M0 build log

## 2026-09-22: Stage B Lean checking corpus

Implemented the full LEAN-TWIN checking corpus: 24 ACCEPT and 12 REFUSE
pairs, with individual attest and Lean sources and a strict manifest. The
gate checks the pinned Lean version, complete source membership, term
proofs, and empty axiom reports. Refusal prefixes must check successfully;
the final declaration must fail for the expected reason in both languages,
with Lean diagnostic locations inside that declaration.

The default gate battery now includes LEAN-TWIN. Its standalone command is
`zsh -f dev/gates.sh LEAN-TWIN`. The carried gate wrapper's exact adapted
hash and CARRIED.md entry have been updated; no carried kernel or surface
source changed.

The corpus passes 24/24 ACCEPT and 12/12 REFUSE pairs. Thirteen mutation
controls pass and all thirteen mutations are caught. The executable records
are `validation/lean-twin.json` and `validation/lean-twin-mutations.json`,
with per-command logs and source hashes. The release check record
`dev/validation/lean-twin-checks.json` is written by
`python3 -P dev/lean-twin-checks.py --record`: it runs the full gate battery,
the forced dune tests, both record commands and the TRACE-ERASURE frontier,
pins each exit code, timing and log hash, hashes both records above, and
derives `record_hashes_verified` by rehashing the logs those records name.
See `lean/README.md` for coverage, refusal-site checks, and reproduction
commands.

Stage B remains OPEN on Acc checking and inline proof erasure. This corpus
covers the shared checking fragment and does not erase or conceal the
known Acc divergence. The initial F2, F2Neg, and Acc probes still run in
the separate ERASURE group. The earlier build-log entries and records
remain historical evidence of their own implementation trees.


## 2026-09-22: Stage A implementation

Carried 594 files from assay `eebe37e00ecb7fdce739c49f50a6dd49c45022b1`
and the pinned mechanism build wrapper. The kernel and surface OCaml sources
are unchanged. Twelve build and gate adaptations are listed in CARRIED.md
and frozen by exact hashes in dev/carry-manifest.json.

Implemented `attest check`, checked-form output, axiom disclosure, and
`spec-count`. The driver shares the carried result-returning file boundary.
The public package is attest; internal library names preserve upstream
module references. Dune runtest includes the fixture dependencies and
explicitly selects the kernel and surface runners.

Validation on the implementation tree. The gate battery ran on the checkout
/Users/oobi/Documents/gpt4/attest-stage-a, the working copy that produced
this slice; the attest repository carries the same files:

| check | result |
| --- | --- |
| BUILD | Passed with warnings as errors. |
| CARRY | 594 files, zero differences, zero unlisted paths; both origins checked against Git blobs. |
| R0-COUNT | Two formers, four schema constructors, five declared shapes, three admitted shapes. |
| R0-AUDIT and R0-DIFF | Passed; three canonical files agree with kanon 2c2e6e6. |
| HOUSE | Passed, with one inherited catch site and the exact CLI argument-dispatch allowance. |
| DRIVER-EXIT | 13 success, refusal, disclosure, and filesystem cases passed. |
| SUITE-KERNEL | 337 checks passed; seven-run median 207.645 ms in the recorded run. |
| SL-SURFACE | 20 checks passed. |
| AXIOMS-empty | The Stage A ACCEPT example reports zero axioms; a separate postulate fixture reports one. |
| TRUSTED-LINES | kernel 3997/4100, lower 0/1100, encoder 0/800, harness 0/100; whole-lib 6193 informational. |
| Rung 1 | Measured parse and combined elaboration/check on the named, hashed example. |
| Dune runtest | Exit 0; the wrapper's custom-runner summary does not supply test counts. |
| Mutation probes | 13/13 caught after a fresh successful baseline gate run. |

validation/stage-a-gates.txt is the positive gate transcript captured on
that checkout. Its one path row (the HOUSE catch site) is rewritten to the
tree-relative form that dev/house.sh prints since the review round of
2026-09-22, and baseline_sha256 is repinned over the rewritten text; the
record is captured again from this tree at the close of the review.
validation/stage-a.json pins the implementation files and records the
mutation diagnostics. The probes are rerunnable with `zsh -f dev/mutations.sh`;
`MUTATIONS_RECORD=1 zsh -f dev/mutations.sh` from the repository root also
rewrites validation/stage-a.json, validation/stage-a-gates.txt and
validation/mutations/<name>.log.

Integration fixes found during validation: include Sys_io in the kernel
test stanza; reuse that boundary in the driver; explicitly select Dune's
root through DUNE_ROOT so nested mutation copies build themselves. The
wrapper's dunecho frontend does not accept Dune's --root flag directly.
Final local review tightened unknown-origin and symlink handling in the
carry gate and tied R0 snapshot checksums to the pinned carry hashes.

This entry records local implementation review and executable validation.
No independent review agent, commit, or milestone ratification is claimed.
The changes are prepared for the user's review and commit.

Next: Stage B's opaque-proof erasure work. USER step 8 remains required for
a green TRACE-ERASURE row. Stage 0 toolchain, SP1, and denominator tasks are
not closed by Stage A. Rungs 2 and 3 remain OPEN until denominator freezing.

## 2026-09-22: Stage B erasure increment

Starting from Stage A commit `9a03183`, implemented `attest build --erase`
and a proof-opaque erasure environment in `erase/opaque.ml`. Classification
uses checked types; every Prop-valued definition becomes a typed postulate
before erasure. Both the full environment and the declaration stream are
sealed, so the carried program walker cannot restore proof bodies. Runtime
definitions, types, and the family table are preserved. No kernel or surface
source changed; all 594 carried files still pass the provenance gate.

USER step 8 now has executable evidence. The F2 function and pair examples
both change erased output on the actual assay `eebe37e` checkout. Those four
pin outputs agree with the newly compiled carried eraser. The pin commit,
binary hash, fixture hashes, and output hashes are in
`validation/f2-pin.json`; `python3 -P dev/f2-pin-check.py ASSAY_PIN`
regenerates the evidence on a clean pin checkout whose assay.exe digest
matches the value pinned in the script.

Validation on the implementation working copy:

| check | result |
| --- | --- |
| Stage A gates | Passed, including 337 kernel tests, 20 surface checks, carry, R0, house rules, and line budgets. |
| Erasure regressions | Four pairs identical; all four differ with the carried evaluator; proof-shape control identical. |
| Opaque environment tests | Six tests cover direct proofs, aliases, proof functions, inherited scope, runtime reduction, classifier errors, and a poisoned proof body. |
| Erasure CLI | Six checks passed, including usage/input errors, check errors, and a checked but unsupported layout returning exit 2. |
| Initial Lean twins | F2 and Acc sources elaborate with Lean 4.33.1 under `-DwarningAsError=true` with empty logs; LEAN-TOOLCHAIN compares the lean that ran with `lean-toolchain`; a token guard rejects `by`, `sorry`, `admit` and `native_decide` outside comments; LEAN-AXIOMS prints the axioms of every enumerated declaration and allows only `F2Fixture.opaqueProof` and `AccFixture.R`. The Acc eliminator is noncomputable. |
| Erasure mutations | All five caught after successful builds in isolated copies, including the Lean `sorry` row. |
| Dune runtest | Passed, including the new erasure test executable. |
| Stage A mutations | Not rerun against the updated tree; the Stage A record is a historical snapshot. |

`python3 -P dev/erasure-gates.py --record` regenerates
`validation/erasure.json` and its logs with implementation hashes.
`python3 -P dev/erasure-mutations.py --record` regenerates mutation evidence.
The Stage A record remains a historical snapshot of its original tree.

Stage B remains OPEN. The concrete Acc seed is refused at its Nat index:
`index above universe: the index x of Acc lives at 1 and Acc is declared at 0`.
The Lean twin accepts the corresponding Prop family. The carried singleton
large-elimination criterion also excludes recursive families, so relaxing
the index check alone will not implement the planned Acc row. The full
24 ACCEPT / 12 REFUSE twin corpus and Acc erasure/mutation gates are not
claimed. `dev/gates.sh TRACE-ERASURE` fails explicitly on this frontier.
The existing carry pin and kernel budgets remain binding for the next step.

This entry records local implementation review and executable validation.
No independent review agent or Stage B completion is claimed.

## 2026-09-22: Bend 2 evaluator pilot

Added an optional evaluator subset under `pilot/bend2/` to test both proposed
migration benefits. The production kernel remains OCaml. Bend is pinned to
2.0.25, commit `ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b`.

The dependent scope and environment representation checks four laws, rejects
three invalid programs, and catches two mutations through failed proofs.
All 128 generated programs agree with attest's checked evaluator across
Bend native, Bend JavaScript, and the matched OCaml implementation.

The final seven paired measurements gave median fresh native builds of
508.83 ms for Bend versus 298.39 ms for OCaml (1.71 times longer), and
edited builds of 569.23 ms versus 237.64 ms (2.40 times longer). The
predeclared adoption gate required at least a 10% improvement in both.
The stronger scope guarantees passed; the build-speed gate failed.
Keep OCaml for the production evaluator under this toolchain.

`python3 -P pilot/bend2/run.py --bend-root PATH --record` regenerates
`dev/validation/bend-pilot.json` and its logs. The record pins compiler,
pilot, and oracle sources and retains all paired samples. See the pilot
README for the subset boundary, trusted components, and reproduction steps.
This experiment does not close the existing Stage B Acc frontier.

### 2026-09-22 (review fix F3: inline proof positions pinned as open)

The carried `lib/erase.ml` stays verbatim. Its let arm evaluates a
Prop-typed binding to its value and a case on an inline proof reduces, so a
proof written inside a runtime-typed definition keeps its body and selects
the erased layout. SPEC.md 1.1 names both positions as open. Four fixtures
(`let-proof`, `scrutinee-proof` and their `-opaque` twins) and the
`ERASURE-OPEN` rows of `dev/erasure-gates.py` pin the difference; the rows
fail when the frontier closes, which is the signal to move them into
`ROWS`. `dev/validation/erasure.json` is re-recorded with the new rows.
