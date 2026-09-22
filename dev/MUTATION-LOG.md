# Mutation log

## 2026-09-22: Stage A

A fresh positive gate run passed before all 13 scratch-copy probes. Each probe required both a nonzero exit and its expected diagnostic. The scratch trees were removed after the run. Scratch outputs are under `.gatework/mutations/` (not tracked). The kept probe logs are under [validation/mutations/](validation/mutations/); hashes and exact observed diagnostics are recorded in [validation/stage-a.json](validation/stage-a.json). Regenerate both with `MUTATIONS_RECORD=1 zsh -f dev/mutations.sh` from the repository root.

| probe | changed path | exit | observed failure |
| --- | --- | --- | --- |
| PIN | `dev/PIN` | 1 | `PIN eebe37e00ecb7fdce739c49f50a6dd49c45022b0 FAIL expected=eebe37e00ecb7fdce739c49f50a6dd49c45022b1` |
| CARRY | `lib/quantity.ml` | 1 | `CARRY FAIL path=lib/quantity.ml` |
| CARRY-unlisted | `lib/unlisted.ml` | 1 | `CARRY files=594 diff=0 unlisted=1 FAIL` |
| CARRY-origin | `dev/carry-manifest.json` | 1 | `CARRY FAIL: unknown carry origin: unknown` |
| BUILD | `lib/quantity.ml` | 1 | `E lib/quantity.ml:160:20  unused-var  unused variable unused.` |
| SUITE-KERNEL | `test/golden/a01-fun-app.checked` | 1 | `SUITE-KERNEL FAIL` |
| R0-former-count | `lib/term.ml` | 1 | `R0-COUNT FAIL: spec-count exit=1: attest: spec-count: expected two formers and five shapes` |
| R0-third-constructor | `lib/term.ml` | 1 | `E lib/term.ml:102:4  partial-match  this pattern-matching is not exhaustive. Here is an example of a case that is not matched: KHost (_, _)` |
| R0-shape | `lib/shape.ml` | 1 | `SPEC.md: KHost of lib/shape.ml has no refusal row` |
| R0-walk-order | `lib/shape.ml` | 1 | `R0-DIFF FAIL row=shape.ml` |
| R0-reference | `dev/r0-diff/term.ml` | 1 | `R0-DIFF FAIL row=term.ml: reference checksum` |
| AXIOMS | `corpus/id.att` | 1 | `AXIOM smuggled` |
| kernel-growth | `lib/check.ml` | 1 | `TRUSTED-LINES kernel=4197/4100 lower=0/1100 encoder=0/800 harness=0/100 FAIL` |

The former checks use two bounded probes: extending the former inventory after a successful rebuild exercises R0-COUNT; adding a term constructor exercises exhaustive-match rejection at BUILD. This does not claim a fully routed third former. The shape probe adds a declared constructor without its refusal citation. The axiom probe adds a well-typed postulate of Type 0 to the ACCEPT example. These are the concrete probes used for the corresponding plan rows.
