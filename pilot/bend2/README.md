# Bend 2 evaluator pilot

The pilot tests the proposed migration's two benefits together: stronger
implementation guarantees and shorter builds. The recorded result supports
the scope guarantees and fails the native build speed requirement. Keep
the production evaluator in OCaml with this toolchain.

The final seven paired samples on 2026-09-22 gave these medians:

| Measurement | Bend 2 | OCaml | Bend / OCaml |
| --- | ---: | ---: | ---: |
| Native build, fresh artifacts | 508.83 ms | 298.39 ms | 1.71 |
| Native rebuild after an edit | 569.23 ms | 237.64 ms | 2.40 |
| Native workload, including process startup | 7.44 ms | 6.69 ms | 1.11 |

Bend's separate `--check-only` median was 162.14 ms. This does not produce
an executable and does not count as a native build improvement. Absolute
times varied between runs; Bend was slower in every cold and edited pair
in the final record. The small runtime workload does not establish a
whole-compiler throughput result.

[The evidence JSON](../../dev/validation/bend-pilot.json) contains raw samples,
commands, tool versions, source hashes, log hashes, and the explicit
`both_benefits_demonstrated: false` verdict. Logs are alongside it in
`dev/validation/bend-pilot/`. Log lines omit trailing whitespace; raw
output hashes are also retained. This is an optional experiment, outside the
normal Stage A and erasure gates. Stage B remains open.

## What the port proves

`core.bend` implements a fuel-bounded abstract machine for attest's
`Lit`, `Var`, `Let`, and `Ann` evaluation subset. Literal payloads are
restricted to U32; attest's unbounded Nat representation is not ported.
The OCaml model uses the same machine, fuel transitions, and workload.

The term's scope length indexes `Term<n>`. Each variable must carry
`Bound(n, index)`, and an evaluation job pairs its term with an `Env(n)`
of exactly that length. An empty environment cannot admit a variable.
Let continuations extend the scope and environment together. Fuel
exhaustion is an explicit result. There are no `@unsafe` definitions or
proof holes in the pilot.

Four checked laws establish head lookup, lookup through an extended
environment, impossibility of a closed variable, and evaluation of
`let x = value in x`. Three invalid scope/environment programs must fail
with the expected type diagnostics. Two mutations change lookup and
binding behavior; both must fail at their associated proof declarations.

These are stronger enforced scope guarantees than the existing
`Var of int` plus environment list implementation. This is not a claim
that OCaml cannot express indexed invariants with GADTs. The laws also
do not constitute a general semantic preservation theorem. Bend's type
checker and code generators remain trusted.

The differential corpus contains 128 deterministic closed programs,
including nested bindings, shadowing, annotations, and U32 boundaries.
`oracle.ml` first checks each program with attest's actual elaborator,
then evaluates and quotes it with the existing kernel. Bend native,
Bend JavaScript, and the OCaml model must all produce the same answers.
This subset does not cover universes, Kan constructs, global unfolding,
erasure, or the full attest acceptance/refusal corpus.

## Measurement contract

Before measuring, the adoption threshold was set to at least 10% lower
median time for both fresh native builds and native rebuilds after a
source edit, with at least seven paired samples. Language order alternates.
Fresh builds use new artifact directories; filesystem caches are not
flushed. Edit builds reuse their directories and change a workload
constant. A changed executable hash and the new expected output are
required after every edit.

Bend measurements use a compiled Bun CLI from the pinned source and
include checking, C generation, Clang optimization, and native linking.
OCaml uses Dune native builds with `-O3` in an isolated project. The
runner verifies that Dune actually produced an executable. Toolchain
bootstrap, source generation, and correctness runs are outside build
timers. Runtime runs use a dynamic input seed, one CPU thread, no GPU,
2,500 programs, and 24 nested lets per program. Every run checks a
checksum and zero exhaustion failures.

The comparison is between equivalent small evaluator implementations.
It does not compare with Rust, estimate a full port's build time, or
measure the JavaScript development build loop. Upstream documents
[one C file per program and no incremental native builds](https://github.com/bendlang/bend/blob/ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b/README.md#limitations).
That limitation is consistent with the measured edit cost.

## Reproduce

Use a 64-bit OCaml installation and the normal attest build dependencies,
plus Bun, Node, and Clang. The recorded versions were OCaml 5.2.1,
Dune 3.24.2, Bun 1.3.11, Node 23.10.0, and Apple Clang 21.0.0 on arm64.
The toolchain pin is Bend 2.0.25 at
`ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b`.

```sh
git clone --filter=blob:none https://github.com/bendlang/bend /tmp/attest-bend-toolchain
git -C /tmp/attest-bend-toolchain checkout --detach ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b
(cd /tmp/attest-bend-toolchain && bun build bend2/main.ts --compile --outfile bin/bend)
python3 -P pilot/bend2/run.py --bend-root /tmp/attest-bend-toolchain
```

The runner checks the checkout, source cleanliness, and CLI version. It
disables Bend telemetry and uses a local package directory. No package
download or global installation is needed by the pilot itself. Ordinary
runs write under `.gatework/bend-pilot/`; `--record` replaces the checked-in
evidence. Exit zero means the experiment completed, including all
correctness checks. The JSON verdict separately reports whether both
migration benefits passed. A failed benefit must not be treated as
permission to replace the production evaluator.

For an individual checker invocation:

```sh
ATTEST_BEND_ROOT=/tmp/attest-bend-toolchain sh pilot/bend2/bend.sh pilot/bend2/smoke.bend --check-only
```
