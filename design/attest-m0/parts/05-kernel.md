## 5 The kernel term at M0

M0 adds no former and no shape constructor.  The kernel term is kanon R0: the type formers are exactly `Lan_s` and `Ran_s` along a closed shape grammar of five shapes (brief:38-47, VERIFIED).  In OCaml the two formers are `Lan of t Shape.t * t` and `Ran of t Shape.t * t` beside `Univ` in `Term.t` (A/lib/term.ml:48-50 by P1:13, VERIFIED at P1:13), and `Shape.t` is the closed variant `SPi of Quantity.t * string * 'a`, `SColl of int`, `SPar of 'a * 'a`, `SMu of string * 'a list`, `SNu of string * 'a list` (A/lib/shape.ml:11-15 by P1:14, VERIFIED at P1:14).  The term walk a reader reruns is `rg -n "^  \| " lib/term.ml` in the assay pin;  it lists 13 constructors, and only `Univ`, `Lan` and `Ran` produce types (P1:19, VERIFIED at P1:19).  The constructs of the template section 5 (tpl:153-161) are EVM namings that attest drops (verdict:106);  this section keeps the template's rule that a naming carries a refusal citation in SPEC.md and that dev/r0-audit.sh fails on a naming with no citation (tpl:161, VERIFIED).

### 5.1 The five shapes and their M0 standing

| shape (A/lib/shape.ml:11-15) | `Lan_s` gives | `Ran_s` gives | Lean 4 feature | standing at M0 |
| --- | --- | --- | --- | --- |
| `SPi`, weakening by A (brief:43) | Sigma | Pi | dependent pairs, dependent functions | admitted, construction (verdict:34) |
| `SColl`, finite discrete collapse (brief:44) | variants | records | enumerations, structures | admitted, construction (verdict:34) |
| `SPar`, parallel pair collapse (brief:45) | `Quot` | equalizer subtypes | `Quot`, subtypes | declared, not admitted;  M2 (verdict:100, verdict:120) |
| `SMu`, polynomial P (brief:46) | initial algebras, W types | none | inductive types and families | admitted, construction (verdict:34) |
| `SNu`, polynomial P (brief:47) | none | terminal coalgebras | coinductives | declared, not admitted;  M3 (verdict:100, verdict:121) |

The assay pin's own schedule admits `SPar` at M1 and `SNu` at M2 (A/lib/rules.ml:20-23 by verdict:36);  attest's milestones move them to M2 and M3 (verdict:120-121, VERIFIED), and the milestone list wins for this plan.  Rows 1 to 3 are constructions in the kernel;  rows 4 and 5 are the algebra and coalgebra universal properties in the kernel, Kan by an omega-chain theorem outside it (P1:80, BELIEVED, settled by Riehl chapter 6 as P1:70 states).  Universes, contexts, substitution and literal accelerators are the ambient framework (brief:55-56);  definitional eta holds only for functions and structures (brief:58);  a surface macro over a Pi, Sigma or inductive kernel fails R0 (brief:57);  ZK is not a former and not a shape (brief:61-64).  VERIFIED at brief:49-64.

### 5.2 The M0 constructs, construction or naming

Each row names one M0 construct, its kernel standing and the gate that catches a divergence.  No row is a former.

- Word32: the library global `Lan_SPi Nat (fun n => n < 2^32)` with the second component at quantity 0, erased by its Prop type (verdict:101, P1:80).  The TYPE is a naming over `SPi`;  the REPRESENTATION is an erase row, `RWord` in eterm (verdict:98).  Word64, U256 and Bytes follow the same form (P1:80).  Their literals extend `Literal.t` behind `Lit of Literal.t` (A/lib/term.ml:58 by P1:16), and the check rules of those literal kinds are what the OQ4 kernel headroom of 103 lines pays for (verdict:150).  Gates: TRACE-ERASURE, EXEC-DIFF (P1:74).
- Host: the library sum `Lan (SColl n)`, a naming over `SColl` (verdict:103).  Under OQ5, n is 3 at Stage D (Read, Commit, Halt) and 6 at Stage E (Keccak, Sha256, U256Mul), and no M0 file names Bn254 or Secp256k1 (00-bindings:19, VERIFIED);  the verdict's `SColl 8` is the M2 roster (verdict:103, verdict:120).  Gates: HOST-ROSTER, EXTERN-ROSTER (verdict:104, verdict:23).
- Prog: the free monad `Lan_SMu` over `1 + Sigma (h : Host) (Resp h -> X)`, a construction through the admitted `SMu` row (verdict:103).  Its `In` nodes lower to ecalls, which is an emission row and not a kernel rule (verdict:103).  Gates: EXEC-DIFF, PUBVAL-DIGEST (verdict:117).
- Bound proofs: quantity-0 inhabitants of `Ran_pi` types into Prop, a naming over an existing former (P1:16).  Gate: TRACE-ERASURE in the OQ7 form (brief:541).
- Ambient Prop, proof irrelevance and subsingleton large elimination: named rules present at the pin, with literal-fast-path (verdict:34, verdict:102).  `Quot.sound` arrives at M2 as the only tracked axiom (verdict:102, verdict:120).  Gate: AXIOMS empty at M0 (verdict:118).
- Precompile postulates: the extern kind tracked by `--externs` beside `--axioms`, a naming (P1:16, verdict:23).  Gate: EXTERN-ROSTER at Stage E.
- Cycles, the allocator and the calling convention: framework facts printed by the executor and checked by ENC-XCHECK and EXEC-DIFF, never kernel (P1:16).

### 5.3 The R0 gates at Stage A

Stage A runs R0-COUNT, R0-AUDIT and R0-DIFF on the carried tree (verdict:117, VERIFIED), and every later stage exit runs them again.

| gate | command, from the attest root | pass rule | source |
| --- | --- | --- | --- |
| R0-COUNT | `zsh -f dev/r0-count.sh` | the fenced block under "## R0 counts" in SPEC.md diffs empty against `attest spec-count`;  prints `R0-COUNT OK`, exit 0;  else prints the diff and `R0-COUNT FAIL`, exit 1 | assay dev/r0-count.sh:3-5 (VERIFIED by cat);  brief:59 |
| R0-AUDIT | `zsh -f dev/r0-audit.sh`, which is `exec python3 -P dev/r0-audit.py <root>` | the walk of the term sum finds no third former and every naming carries a SPEC.md citation;  prints `R0-AUDIT OK`, exit 0 | assay dev/r0-audit.sh:3 (VERIFIED by cat);  brief:60;  tpl:161 |
| R0-DIFF | `diff -q dev/r0-diff/term.ml lib/term.ml && diff -q dev/r0-diff/shape.ml lib/shape.ml && diff -q dev/r0-diff/spec_count.ml lib/spec_count.ml` | all three diffs empty at every stage exit;  dev/r0-diff/ holds the three files as `git show 2c2e6e6:lib/<name>.ml` from kanon, with their sha256 in dev/r0-diff/SHA256 | verdict:96;  P1:14 |

The R0-COUNT and R0-AUDIT rows print OK on the assay pin today (verdict:33-34, VERIFIED on the peer tree by the verdict's probe 4;  the pin rules forbid a build in the pin, so this unit did not rerun them).  The R0-DIFF row is a plan decision: the reference copy under dev/r0-diff/ is BELIEVED until Stage A vendors it from kanon 2c2e6e6, and the kanon tree is outside this unit's read set.  The R0-COUNT pass value is `formers 2: Lan Ran` (P1:13, VERIFIED at P1:13).

### 5.4 The base identity and the borrowed overlay

The base is assay at eebe37e: `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin rev-parse --short HEAD` prints `eebe37e` and `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin rev-parse --short HEAD` prints `1e4f371` (VERIFIED by those commands on 2026-09-22).  The veil submodule is checked out: `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule status` prints ` a7534cedeac82d396de8e23058ee6bc990560f65 vendor/veil (a7534ce)` (VERIFIED by that command;  brief:543 records the same checkout).  The term sum of the base is byte-identical to veil's: `diff -q /Users/oobi/Documents/kan-sp1-lang-assay-pin/lib/term.ml /Users/oobi/Documents/kan-sp1-lang-mech-pin/vendor/veil/lib/term.ml` exits 0 with no output (VERIFIED by that command, read-only, on 2026-09-22;  verdict:30 records the same).  The shape grammars differ: veil adds `SZk`, `SFhc` and `SMpc` at V/lib/shape.ml:16-19 (verdict:29, VERIFIED at verdict:29), which is the counterexample R0 refuses (brief:61-64), so R0-DIFF pins shape.ml against kanon and never against veil.  The mech pin has no lib/term.ml and no lib/shape.ml of its own (verdict:31);  its kernel is veil's plus a level overlay, and its lib/ is check.ml 643, conv.ml 404, eval.ml 314, level_eq.ml 144, level_scope.ml 32, level_var.ml 53, level.ml 36, rules_lvl.ml 2 and rules.ml 2,116, total 3,744 over 9 files (VERIFIED by `wc -l /Users/oobi/Documents/kan-sp1-lang-mech-pin/lib/*.ml`;  verdict:32 records 3,744 in 9).

The overlay borrowed from mechanism-lang for the R1 import oracle (brief:77-81 by 00-bindings:29) has four measured pieces, none of them merged at M0 (OQ3, brief:541;  00-bindings:15):

| piece | path under the mech pin | lines | when attest takes it |
| --- | --- | --- | --- |
| level overlay | lib/level_eq.ml, lib/level_scope.ml, lib/level_var.ml, lib/level.ml, lib/rules_lvl.ml | 144 + 32 + 53 + 36 + 2 = 267 | M1, into the kernel bucket (verdict:150;  P1:59) |
| importer | import/*.ml, 10 files | 1,543 (with the 8 .mli files, 1,748) | M1, as the sibling M/import (verdict:106) |
| PRELUDE-CHECKED driver | dev/prelude-gates.py | 89 | M1, count mode then ratchet (OQ3, brief:541) |
| prelude map | map/prelude.map.tsv and map/NEVER.tsv | 2,478 + 186 = 2,664 rows | M1, with the map (verdict:23) |

All four counts are VERIFIED by `wc -l` on the mech pin on 2026-09-22, read-only.  The 267-line level overlay matches P1:59 and verdict:150;  the 1,543-line importer matches verdict:106.  The estimate of about 480 lines in this unit's brief matches no measured piece;  the measured rows above bind and the estimate is retired.  The mech pin's own gates name PRELUDE-CHECKED at its Stage D (mech dev/gates.sh:370, VERIFIED by rg).

### 5.5 The flip rule of OQ6 and its M0 moment

The ruling, verbatim from the brief's section 10: "OQ6: the kernel base is assay;  the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures, and flips only under 211 ms (this replaces Q0)." (brief:541, VERIFIED).  The threshold is the 2x line: the assay side is pinned at 421.774 ms median over 7 runs on the 77 fixtures present in both trees (P1:58, VERIFIED at P1:58), and 421.774 divided by 2 is 210.887, so a median under 211 ms means mechanism-lang is at least twice as fast.

The second half of USER step 5 is the trigger and stays a USER step: `zsh -f dev/dunecho.sh build` in the mech pin, then `RUNS=7 zsh -f dev/bench.sh SUITE-KERNEL '_build/default/test/main.exe vendor/veil/test'` with the paths made absolute (brief:543, VERIFIED).  The first half, the veil checkout, is done (brief:543;  the submodule status above).  M0 checks the flip at two moments.  (1) Stage A entry: the CARRY gate reads dev/FLIP.md, which records the median or the word OPEN;  a median under 211 ms turns Stage A into a re-carry from the mech pin 1e4f371 with veil a7534ce, and a median at or over 211 ms or OPEN carries assay eebe37e (00-bindings:21).  (2) The M0-EXIT stamp: the stamp copies the dev/FLIP.md line, and a median printed after Stage A closed does not reopen M0;  it is an M1 decision.  Both moments are plan decisions, BELIEVED until the user prints the median;  the assay carry is the default under the ruling (brief:541).
