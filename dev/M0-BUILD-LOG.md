# M0 build log

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
