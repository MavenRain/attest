# Bend 2 implementation

The production compiler uses Bend 2.0.25 at
`ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b`. The default output is JavaScript,
run with Bun because the pinned Bend file library uses `bun:ffi`. Source files
are read as bytes, preserving the previous treatment of invalid UTF-8 and
byte-based source offsets. Python and shell remain build and validation tools.

```sh
sh dev/setup-bend.sh
make build
make test
python3 -P dev/build.py --check
```

`ATTEST_BEND_ROOT` selects an existing pinned checkout. The build rejects a
different revision or modified tracked compiler sources. It caches each target
using transitive source hashes, compiler identity and build options, checks the
output hash before reuse, and rejects source changes during compilation.

The source modules cover the shared data and arbitrary-precision arithmetic
(`lib/foundation.bend`), kernel checking and evaluation (`lib/kernel*.bend`),
surface syntax and elaboration (`surface/*.bend`), and typed erasure
(`lib/erasure.bend`, `erase/*.bend`). The CLI is `bin/attest.bend`.
Checking and erasure thread finite budgets explicitly, including budget consumed
by classification failures that are deliberately handled by opacity preparation.

Scoped `@unsafe` definitions express unbounded semantic recursion where Bend's
termination checker cannot establish the required decrease. They introduce no
numeric fuel limit. Bend type, affine-use and exhaustiveness checks still run.
The named sites and catch-all patterns are recorded in `dev/bend-policy.json`;
changing that registry requires reviewing the corresponding source changes.

## Reference and gates

`dev/validation/ocaml-reference.json` records all four CLI modes for 234 original
source files, plus five CLI edge cases: 941 cases in total. It includes the
original revision, executable hash, source hashes, stdout, stderr and exit codes.
The original executable is unnecessary for replaying the comparison:

```sh
python3 -P dev/migration-differential.py compare \
  --root . --driver _build/default/bin/attest.exe \
  --manifest dev/validation/ocaml-reference.json \
  --report .gatework/differential.json
```

The eight-group suite retains the original parse round trips, checked and raw
erasure goldens, exact refusal messages, kernel negatives, recursive-value
checks and required migration fixtures. `make test` also runs the Bend kernel,
arithmetic, map, erasure representation, budget and refusal regressions. Large
file reader checks are available with `ATTEST_TEST_LARGE_IO=1`.

The historical carry manifest and R0 source checksums are retained. The new
`dev/bend-migration.json` maps each removed source or build file to its replacement
or an explicit retirement reason, and pins the Bend sources. `CARRY` verifies
the old provenance and current inventory. `R0-DIFF` now verifies this provenance
chain; cross-language source bytes are not claimed equal. `R0-COUNT` retains the
same CLI schema counts, and `R0-AUDIT` retains the shape-owner boundary.

HOUSE retains pure kernel state, explicit errors, registered catch-alls and
semantic recursion, no loop keywords, nonzero literal divisors and the prose
character rule. Bend's Result file boundary replaces the OCaml exception catch
site. Bend typechecking, including Boolean matches, replaces the old syntax
rule against OCaml Boolean patterns. The checker runs during HOUSE.

The Bend trusted-source count includes shared types and explicit interpreter
continuations. Its kernel limit is 6000 physical lines, compared with the
historical 4100-line OCaml subset. Every `lib/kernel*.bend` module is counted
except printing and schema-reporting modules, together with all of foundation.
The lowerer, encoder and external harness bounds are unchanged. This is an
explicit language-specific budget change; it is not a claim of source-size
equivalence. The 6000-line Bend ceiling was explicitly accepted on 2026-09-23.

The unbuilt assembly, EVM and Keccak test modules were excluded by the original
Dune test module list. They are retired, with their disposition recorded. The
existing checked and erased golden files remain covered. The early evaluator
pilot's OCaml oracle is superseded by the full compiler reference corpus.

`TRACE-ERASURE` retains its existing nonzero result until the Stage B trace
comparison exists. The Acc frontier and recursive-singleton restrictions are
unchanged by this migration.

## Native builds

Native output can be requested explicitly:

```sh
python3 -P dev/build.py --backend native foundation order
```

The small arithmetic and structural-checking programs have run natively. Full
compiler native generation is not validated: optimized compilation caused heavy
memory pressure, and an unoptimized full kernel attempt failed in Clang with
`live register clobbered by inserted prologue instructions`. Use the JavaScript
backend for the CLI. `ATTEST_C_OPT` selects an optional native optimization level
and `ATTEST_CC` selects its C compiler; neither changes the default backend.
