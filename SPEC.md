# attest specification, M0 Stage A

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

Exit 0 means success, 1 means a parse, elaboration, type, or R0-count failure,
and 64 means invalid arguments or an unreadable input. The shared `Sys_io`
module converts standard-library file errors into results. There is one
source catch site, inherited in `test/sys_io.ml` and reused by the driver
through a Dune copy rule.

ELF production, execution, external-host disclosure, and compiler-walk
disclosure arrive in subsequent stages. Their commands are not advertised
by the Stage A executable.

## 2 Kernel

`Lan` and `Ran` are the only type formers. Universes, variables, substitution,
and literals remain the inherited ambient framework. No host effect is a
former or a shape. `lib/term.ml`, `lib/shape.ml`, and `lib/spec_count.ml`
are byte-identical to kanon `2c2e6e6831a0b2cf3107fa4aad392606109a2bcf`.

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
deferred shape. The kernel and parser source remain unchanged.

## 3 Trusted code and validation

`TRUSTED-LINES` counts physical source lines in the 12 kernel files specified
by plan section 4.3, bounded by 4,100. It counts every OCaml source/interface
under `lower/` against 1,100 and `elf/` against 800, and every Rust source under
`harness/` against 100. Absent later-stage directories print zero. Whole-lib
size is informational. Tests and the timing helper are outside the kernel.

`dev/gates.sh` builds before running the carry, R0, house, driver, kernel,
surface, axiom, budget, and timing checks. It stops on a failed command and
keeps complete leg output under `.gatework/stage-a/`. Kernel timing uses
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
