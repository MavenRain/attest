# attest specification, M0 Stage A and the erasure increment

Stage A carries the assay kernel at `eebe37e00ecb7fdce739c49f50a6dd49c45022b1`.
The binding design and remaining stages are in
[the M0 plan](design/attest-m0/M0-PLAN.md).

## 1 Implemented surface

`attest check FILE.att` parses, elaborates, and checks a source file, then prints
`CHECK FILE defs=N ok`. Definitions exclude postulates and primitive entries.
Inherited `.kan` fixtures remain accepted. Other suffixes are usage errors.

`attest check --print FILE.att` also prints the checked kernel terms.
`attest check --axioms FILE.att` prints each declared postulate as `AXIOM NAME`,
followed by `AXIOMS FILE count=N`. A failed check never prints a success row.
`attest spec-count` prints the inherited R0 block and rejects counts other than
two formers and five declared shapes.

`attest build --erase FILE.att` checks the whole file and prints its erased
term. Proof globals become typed postulates for every erasure evaluation,
including globals inherited from the checked environment and declarations
reinserted while walking the file. It writes no ELF or output file.

Exit 0 means success, 1 means a parse, elaboration, type, or R0-count failure,
2 means an erasure refusal, and 64 means invalid arguments or an unreadable
input. The shared `Sys_io`
module converts standard-library file errors into results. There is one
source catch site, inherited in `test/sys_io.ml` and reused by the driver
through a Dune copy rule.

ELF production, execution, external-host disclosure, and compiler-walk
disclosure arrive in subsequent stages. Their commands are not advertised
by the executable.

### 1.1 Proof opacity and the current frontier

The carried global record has no quantity field. `erase/opaque.ml` classifies
definitions whose declared type lives in `Prop` at the checking boundary,
then supplies their types without their bodies to the carried eraser.
Classification uses the original checked environment. The API takes the
final globals and declaration rows returned together by `Elab.check_in`.

`erase/inline.ml` also seals inline proofs in ordinary entries when their
type is available from an annotation, let type, or syntactic expected function
type, or inferred independently for a closed term. It tracks the types of function, let,
and type-former binders. Each local proof becomes a closed postulate whose
parameters are all erased, applied to the locals in their original order.
Original domain and codomain syntax preserves declared universes; normalized
empty products alone cannot distinguish runtime types from propositions.
Scope checks include type syntax, shape payloads, and motives.
Fresh typed postulates replace these proof terms before the
erasure evaluator runs. Their names avoid existing globals and families;
they are internal to erasure and add no source declarations or axiom
disclosures. Declaration rows use the rewritten environment, including
entries inherited from earlier checking. The inductive family table is
preserved. Runtime computations remain executable.

The four global F2 pairs cover a runtime function, a pair constructor,
proof aliases, and proof-valued functions. They produce byte-identical
erased terms. Seventeen inline pairs cover let-bound proofs, direct case
scrutinees, both pair projections, a lambda-bound proof, and a proof under
let and case binders, local Nat indices, dependent local types, local lets, let-bound type aliases,
type-former diagrams, runtime calls returning proof-computed types, and
proof lets whose value a local proof type reduces, directly or through
the value of any later let: a proof let alias chain, a type family, or a
let typed by a universe alias.
A proof let keeps its value only when its variable occurs in its body in an
annotation, a let type, the value of a later let, a motive, a shape payload
or a type former. A proof let that a dependent large elimination reads only
as its scrutinee is still sealed, and erasure then refuses the program
(`build --erase` exits 2). The same limit is at commit `c26c41a`.
The runtime output of each inline pair is identical
after removing `erased NAME` declaration notices. The gate reproduces a
runtime difference with the carried eraser for every pair. Thirty-one semantic
tests cover poisoned proof bodies at known types, inherited entries, name
collisions, runtime lets, local type annotations, and rewritten rows. They also
check closed postulate types, dependent argument order, original universes,
inherited local proofs, local hypotheses, proof lets needed by a local proof
type, and scope isolation at unknown branch binders.
This is regression evidence; a general erasure theorem and ELF comparisons
remain later work.

Opaque, proof-computed types can still cause a named erasure refusal.
`fixtures/erasure/opaque-layout-refusal.att` checks but exits 2 because its
tuple's type no longer reduces to a right former. No partial erased program
is printed on that failure.

Proofs depending on constructor branch or motive binders remain open.
The `branch-local-proof.att` pair pins a runtime difference for a proof indexed
by a constructor field. No row pins the motive binder case. Lambda bodies without a syntactic expected function
type also remain conservative; closed subterms can still be sealed. Local
proofs without source type syntax are left intact because inferred readback
can lose the universe of a runtime result type.
Unannotated introductions without an independently inferable type and
inline proofs in family metadata are also outside this increment.

Stage B remains open: `acc.att` fails the erased-binder runtime read check,
although its family and constructor check in `acc-family.att`.
`acc-runtime-proof.att` reaches the recursive singleton elimination refusal.
`TRACE-ERASURE` continues to exit 1. The separate LEAN-TWIN checking corpus
passes 24 ACCEPT and 12 REFUSE pairs in the shared fragment. This increment
changes no checker rule, carry pin, term constructor, shape, or count.

## 2 Kernel

`Lan` and `Ran` are the only type formers. Universes, variables, substitution,
and literals remain the inherited ambient framework. No host effect is a
former or a shape. `lib/term.ml`, `lib/shape.ml`, and `lib/spec_count.ml`
are byte-identical to kanon `2c2e6e6831a0b2cf3107fa4aad392606109a2bcf`.

`lib/check.ml` permits a Prop family's erased indices to live in any universe.
An index type must still be well formed and its binder must have quantity
zero. Constructor fields retain the family universe bound, with one exception
in Prop: an erased field may exceed it when a result index is exactly that
field variable, optionally annotated. The check uses the variable's index
under the complete field telescope. Constant or computed result indices do
not qualify. Result indices still undergo their ordinary type checks.
Type families retain both universe bounds. Positivity and the existing
singleton elimination criterion are unchanged.

`erase/test/prop_index.ml` covers eleven accepted and seventeen refused programs,
including dependent and reordered indices, high universes, ill-formed
indices, hidden fields, result-index type checking, and singleton elimination.
It runs in `runtest` and the erasure gate.

### 2.1 Shapes, lib/shape.ml

| constructor | milestone | refused by |
| --- | --- | --- |
| `SPi of Quantity.t * string * 'a` | M0 | admitted |
| `SColl of int` | M0 | admitted |
| `SPar of 'a * 'a` | M2 | rules.ml |
| `SMu of string * 'a list` | M0 | admitted |
| `SNu of string * 'a list` | M3 | rules.ml |

The milestone column uses attest's schedule. The carried refusal diagnostics
retain their upstream milestone wording. `R0-AUDIT` checks every declared
shape against this table and requires a concrete refusing module for each
deferred shape. The parser source and the term, shape and count definitions
remain unchanged; lib/check.ml carries the section 2 checker adaptation,
pinned by adapted_sha256 in dev/carry-manifest.json.

## 3 Trusted code and validation

`TRUSTED-LINES` counts physical source lines in the 12 kernel files specified
by plan section 4.3, bounded by 4,100. It counts every OCaml source/interface
under `lower/` against 1,100 and `elf/` against 800, and every Rust source under
`harness/` against 100. Absent later-stage directories print zero. Whole-lib
size is informational. Tests and the timing helper are outside the kernel.

`dev/gates.sh` builds before running the carry, R0, house, driver, kernel,
surface, axiom, budget, and timing checks. It then runs the erasure regression,
CLI, initial Lean checks, and the complete LEAN-TWIN checking corpus.
`STAGE-A`, `ERASURE`, and `LEAN-TWIN` select each group;
`TRACE-ERASURE` exits 1 while the Acc frontier is open. Gates stop on a failed
command and keep leg output under `.gatework/stage-a/` and `.gatework/erasure/`.
Kernel timing uses
one warm-up and seven measured runs. Rung 1 reports parse and combined
elaboration/check timings for the named, hashed Stage A example. The inherited
frontend couples elaboration and checking, so they are reported together.
Rungs 2 and 3 remain open until the Stage 0 denominator freeze.

The R0 counts block below is inherited verbatim from the assay pin.

## R0 counts

Inherited unchanged from kanon `2c2e6e6`.  Assay M0 adds no kernel former,
shape, rule or trusted kernel line.

`assay spec-count` prints this block.  dev/r0-count.sh diffs the two.  A
count that grows fails the R0-COUNT gate leg.

```
formers 2: Lan Ran
schema constructors 4: In Elim Sec Out
shapes declared 5: SPi SColl SPar SMu SNu
shapes admitted 3: SPi SColl SMu
named rules declared 3: proof-irrelevance subsingleton-large-elimination literal-fast-path
named rules present 3: proof-irrelevance subsingleton-large-elimination literal-fast-path
eta rows 3: Ran-SPi Lan-SPi Ran-SColl
no eta 3: Lan-SColl Ran-SMu Lan-SMu
```

Every number in the block is the length of the list printed after it.
lib/spec_count.ml reads the shape lists from Shape and the former and
schema lists from Term.
<!-- inherited-r0-counts -->
