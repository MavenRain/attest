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
input. `surface/io.bend` converts file-operation failures into explicit results
and closes each opened input before returning.

ELF production, execution, external-host disclosure, and compiler-walk
disclosure arrive in subsequent stages. Their commands are not advertised
by the executable.

### 1.1 Proof opacity and the current frontier

The carried global record has no quantity field. `erase/opaque.bend` classifies
definitions whose declared type lives in `Prop` at the checking boundary,
then supplies their types without their bodies to the carried eraser.
Classification uses the original checked environment. The API takes the
final globals and declaration rows returned together by `Elab.check_in`.

`erase/inline.bend` also seals inline proofs in ordinary entries when their
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
erased terms. Twenty-one inline pairs cover let-bound proofs, direct case
scrutinees, both pair projections, a lambda-bound proof, and a proof under
let and case binders, local Nat indices, dependent local types, local lets, let-bound type aliases,
type-former diagrams, runtime calls returning proof-computed types, and
proof lets whose value a local proof type reduces, directly or through
the value of any later let: a proof let alias chain, a type family, or a
let typed by a universe alias. They also cover proofs that depend on
constructor fields, including dependent fields, nested branches and
several constructors.
A proof let keeps its value only when its variable occurs in its body in an
annotation, a let type, the value of a later let, a motive, a shape payload
or a type former. A proof let that a dependent large elimination reads only
as its scrutinee is still sealed, and erasure then refuses the program
(`build --erase` exits 2). The same limit is at commit `c26c41a`.
The runtime output of each inline pair is identical
after removing `erased NAME` declaration notices. The gate reproduces a
runtime difference with the carried eraser for those twenty-one pairs. Eight
parameterized branch pairs require runtime equality, but the carried eraser
gives equal outputs for them too, so these runtime rows do not discriminate.
Fourteen motive pairs also have equal carried runtime outputs; their semantic
rows require exactly one sealed proof and recheck the generated proposition.
The gate requires that carried equality. Sealing for these pairs is checked
only in the semantic suite, and the gate requires the suite copies in
`erase/test/parameter_fixtures.bend` and `erase/test/motive_fixtures.bend` to
equal the `.att` files byte for byte.
Sixty-six semantic
tests cover poisoned proof bodies at known types, inherited entries, name
collisions, runtime lets, local type annotations, and rewritten rows. They also
check closed postulate types, dependent argument order, original universes,
inherited local proofs, local hypotheses, proof lets needed by a local proof
type, dependent constructor fields, nested branch scopes, and conservative
fallback for missing family metadata or unavailable parameter syntax. They also check that a
branch takes the fields of its own constructor, not the first constructor of
its family, and that an alias-typed lambda leg under an outer binder starts
from the root scope. Branch contexts require
the exact constructor binder count and quantities, and field types closed over
earlier fields and family parameters. Parameterized branches recover the source
type from an annotated scrutinee, a global declaration, or a typed local binder,
including lets. They require matching family shapes, closed parameter arguments,
and an exact parameter count. Capture-avoiding source substitution specializes
field types under their earlier fields and preserves universe syntax.
Named inductive motives also recover a local context. Their family name and
index count must match the elimination shape, and their binder names must
match the family index telescope in number. Original index domains are
specialized with the same source parameter arguments used by branches.
The self type uses fresh indices in declaration order, with parameters
shifted beneath those indices. Every index and the self binder has quantity
zero, independently of the quantity in the family telescope. Missing metadata,
unavailable parameter syntax, wrong counts, and free parameter arguments or index domains fall back
to the root scope. The five named motive pairs cover an index, self, dependent
indices at a higher universe, a parameter from an enclosing lambda, and a
parameter shifted beneath two indices.
Unnamed motives recover only self, with quantity zero, from the scrutinee's
source type. An annotation, a global declaration, or a typed local binder
(including a let) provides that type. A function application recursively
recovers its head's source type and substitutes the argument into a syntactic
point-function codomain. Substitution removes the function binder, preserves
outer variables, and shifts the argument beneath nested binders. No semantic
readback or type alias unfolding is used. Missing function types, nonpoint
formers, nonpoint addresses, free codomains, and free arguments are refused.
Four `motive-application-*` pairs cover global, dependent, local, and curried
calls; direct tests cover capture avoidance and each refusal.
The resulting source type must be closed in the current
context. An unnamed motive with index binders, an inductive shape, or no
recoverable source type falls back to the root scope. Five `motive-plain-*`
pairs cover each source form and a sum type dependent on an outer type binder.
The guard and quantity tests also check missing globals and locals, free
type variables, and preservation of the source domain.
The gate requires the motive fixture strings to equal their files. For each
parameterized branch and motive pair, the body of `Suite.cases` must hold
exactly one case line with the row name, and that line must call the exact
fixture pair and sealing count. A copy of the line in other code or in a
comment does not count.
Quotation opens the motive, branches and point keys of a stuck elimination
on fresh variables in its captured environment, so it reads only the
environment entries that these bodies use.
This is regression evidence; a general erasure theorem and ELF comparisons
remain later work.

Opaque, proof-computed types can still cause a named erasure refusal.
`fixtures/erasure/opaque-layout-refusal.att` checks but exits 2 because its
tuple's type no longer reduces to a right former. No partial erased program
is printed on that failure.

The `branch-local-proof.att`, `branch-dependent.att`, `branch-nested.att`, and
`branch-multi-ctor.att` pairs cover proofs depending on fields of constructors without family
parameters. For `branch-local-proof.att`, `build --erase` keeps `keep` as the
runtime identity, and the frozen OCaml reference erases `keep`. The migration
differential allows only this named divergence, which
`dev/validation/differential-divergences.json` pins. The eight `branch-parameter*`
pairs cover concrete and dependent parameters, function fields, annotations,
lets, globals, same-shape constructors, and a proof field at a universe. Unnamed
motives without a source scrutinee type, and scrutinee types needing further
normalization or inference, remain open. Lambda bodies without a syntactic expected function
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
changes no checker rule, carry pin, term constructor, shape, or R0 count.

## 2 Kernel

`Lan` and `Ran` are the only type formers. Universes, variables, substitution,
and literals remain the inherited ambient framework. No host effect is a
former or a shape. The original term, shape, and count definitions came from
kanon `2c2e6e6831a0b2cf3107fa4aad392606109a2bcf`. Their historical checksums
and Bend replacements are recorded in `dev/bend-migration.json`.

`lib/kernel_declarations.bend` permits a Prop family's erased indices to live in any universe.
An index type must still be well formed and its binder must have quantity
zero. Constructor fields retain the family universe bound, with one exception
in Prop: an erased field may exceed it when a result index is exactly that
field variable, optionally annotated. The check uses the variable's index
under the complete field telescope. Constant or computed result indices do
not qualify. Result indices still undergo their ordinary type checks.
Type families retain both universe bounds. Positivity and the existing
singleton elimination criterion are unchanged.

`erase/test/prop_index.bend` covers eleven accepted and seventeen refused programs,
including dependent and reordered indices, high universes, ill-formed
indices, hidden fields, result-index type checking, and singleton elimination.
It runs in `make test` and the erasure gate.

### 2.1 Shapes, lib/foundation.bend

| constructor | milestone | refused by |
| --- | --- | --- |
| `SPi { Quantity.t, String, A }` | M0 | admitted |
| `SColl { Nat }` | M0 | admitted |
| `SPar { A, A }` | M2 | kernel_rules.bend |
| `SMu { String, List<A> }` | M0 | admitted |
| `SNu { String, List<A> }` | M3 | kernel_rules.bend |

The milestone column uses attest's schedule. The carried refusal diagnostics
retain their upstream milestone wording. `R0-AUDIT` checks every declared
shape against this table and requires a concrete refusing module for each
deferred shape. The Bend migration preserves these declarations and the section 2
checker adaptation. `dev/carry-manifest.json` pins the historical OCaml sources;
`dev/bend-migration.json` records their disposition and pins the Bend sources.

## 3 Trusted code and validation

`TRUSTED-LINES` counts `lib/foundation.bend` and every `lib/kernel_*.bend` file
except printing and metadata, bounded by 6,000 physical lines. This replaces
the historical 4,100-line budget for twelve OCaml files; it changes both the
language and the counted set. The migration does not establish an equivalent
complexity bound. Every Bend source under `lower/` is bounded by 1,100 and
`elf/` by 800; every Rust source under `harness/` is bounded by 100. Absent
later-stage directories print zero. Whole-lib size is informational. Tests
and the timing helper are outside the kernel.

`dev/gates.sh` builds before running the carry, R0, house, driver, kernel,
surface, axiom, budget, and timing checks. It then runs the erasure regression,
CLI, initial Lean checks, and the complete LEAN-TWIN checking corpus.
`STAGE-A`, `ERASURE`, and `LEAN-TWIN` select each group;
`TRACE-ERASURE` exits 1 while the Acc frontier is open. Gates stop on a failed
command and keep leg output under `.gatework/stage-a/` and `.gatework/erasure/`.
Kernel timing uses
one warm-up and seven measured runs, each batching 100 operations with a
millisecond clock. Rung 1 reports per-operation parse and combined
elaboration/check timings for the named, hashed Stage A example. The inherited
frontend couples elaboration and checking, so they are reported together.
Rungs 2 and 3 remain open until the Stage 0 denominator freeze.

The R0 counts block below is inherited verbatim from the assay pin.

## R0 counts

The counts are inherited unchanged from kanon `2c2e6e6`. The historical
Assay M0 stage added no kernel former, shape, rule, or trusted kernel line.

`attest spec-count` prints this block. `dev/r0-count.sh` diffs the two. A
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
`lib/kernel_metadata.bend` reads the shape, former, and schema lists from
`lib/foundation.bend`.
<!-- inherited-r0-counts -->
