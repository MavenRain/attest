# kan-sp1-lang attack 3: P3 attest

A3, 2026-09-21.  A, M, V, P3 as in P3 line 3.  P1 ABSENT at run time (VERIFIED ls), P2 read.  Probe log: /private/tmp/claude/kan-sp1-lang-panel/probe3.log.

## Findings, ranked by lethality

### F1 R1-UNADMITTED-SHAPES.  FATAL.  The M0 ACCEPT corpus needs two shapes the carried kernel refuses.
- P3:34 puts `Quot`, `Quot.lift`, `Quot.sound` and a subtype in the M0 ACCEPT corpus.  P3:32 and P3:78 map coinductives to Ran over SNu.  P3:129 makes TWIN-LEAN (48 rows) the Stage A exit gate.
- VERIFIED rg A/lib/rules.ml:20 `"SPar arrives at M1"`, :23 `"SNu arrives at M2"`.  VERIFIED S1:104 `shapes admitted 3: SPi SColl SMu` on the built pin (P2 section 1 cites it too).
- P3:80 marks that count BELIEVED where S1:104 is VERIFIED.  P3:141 bounds the kernel at "A/lib plus the overlay" with no line for a SPar or SNu rule.  R0 table rows 3 and 5 are mapped by name only.
- Fix: move the Quot, subtype and coinductive rows to the milestone that lands the rule, or budget the SPar rule in Stage A inside the kernel bound.  Make R0-COUNT print `shapes admitted` and TWIN-LEAN read it.

### F2 R2-SPEED.  FATAL.  More checker work on a 1.956 kernel, no lever on the check walk, no denominator.
- Walks: P3 section 3 counts five (elaborate, check, erase, lower, encode), VERIFIED S1:142 and S1:140, and folds the level scope check into elaboration.
- The overlay P3 ports at Stage A (P3:105, P3:129) runs `Level_scope.check` on every checked term at M/lib/check.ml:43 and a level solver at :265, :448, :527 (VERIFIED rg).  The solver calls stay in the check walk and replace `type t = int` (A/lib/level.ml:2) with level_eq.ml, 144 lines.  Folding :43 into elaboration drops level scoping from the trusted checker.
- The 1.956 is assay's checker without the overlay (A/README.md:3, VERIFIED rg).  The Q6 M0 levers (P3:121) act on lower and encode, not on the check walk.  The M1 levers are named, not costed.
- Denominator: P3 section 3 names `bend check TWIN.bend` plus the C-emission subcommand, both BELIEVED at S2:215, and bend is absent (brief line 236), so rungs 2 to 5 of P3:135 have no measured right side.
- Comparability: Bend 2's Term has no universe levels and no Quot (S3 section 2, bend.lean:197), so the eight twins of rung 1 cannot hold the `Quot` and `Param 0` ACCEPT rows line for line.
- Reachability: assay median 421.774 ms on 77 fixtures (S1:52), Bend 2 none, and P3:136 commits rung 5 at most 1.0 at M1 with no arithmetic from 1.956 to 1.0.
- Fix: keep the overlay at M1 with check mode (P3:30), print WALKS with a per-walk median, freeze one Bend 2 number at Stage 0c before rung 1, bench hashconsing on the 77-fixture suite before rung 5 binds.

### F3 R0-SMUGGLE.  SURVIVABLE.  `Prog` is a type former by postulate and the extern kind contradicts assay's axiom rule.
- Term walk (VERIFIED awk A/lib/term.ml:46-59): Var, Univ, Lan, Ran, In, Elim, Sec, Out, Let, Ann, Global, Lit, Auto, two formers.  Shapes (A/lib/shape.ml:11-15): SPi, SColl, SPar, SMu, SNu.  V/lib/shape.ml:16, :18, :19 SZk, SFhc, SMpc stay out (VERIFIED rg).  A third former would be a new constructor of `t` with a shape and a body, such as `Cod of t Shape.t * t`.  P3 adds none.
- The smuggle is at the type level.  P3:16 types each Host constructor as `Commit : Bytes -> Prog Unit`.  `Prog` occurs once in P3 (VERIFIED rg) with no construction from Lan or Ran.  A bodiless type constant whose sequencing lives only in erase (P3:17) is a type former by postulate.
- assay refuses the extern reading: A/lib/global.ml:33-38, an Axiom "has no def" and is checked "at quantity mode w, so an axiom can never reach erased output" (VERIFIED rg).  Host externs must reach erased output as ecalls.  P3 needs a new global kind at quantity One, absent from the 480-line accounting (P3:62).
- R0 table: rows 1 and 2 are constructions with rules on the pin, rows 3 and 5 are declared and refused (F1), rows 4 and 5 are "Kan by naming plus universal property" (P3:26), decorations.  Cycles, allocator, calling convention, `Lit` (term.ml:58) and quantity-0 bound proofs pass the walk.  ZK is absent from A.
- Fix: build `Prog` as `Lan (SMu ...)`, the free monad over the Host signature, so each constructor is an `In` node and erase maps `In` nodes to ecalls.  Add an `Extern` global kind at quantity One, count it in the bound, print it in R0-AUDIT.

### F4 STAGE-E-PRELUDE-COUNT.  SURVIVABLE.  The count-mode gate fails on 2,292 of 2,477 names today.
- VERIFIED `cut -f3 M/map/prelude.map.tsv | sort | uniq -c`: 2273 UNMAPPED, 185 NEVER, 19 NAME_ONLY, 0 NAME_AND_TYPE.  Covered = 185 / 2477 = 7.5 percent.
- P3:30: count mode fails when NAME_ONLY or UNMAPPED is above zero.  P3:133 makes it the Stage E exit gate.  No stage in P3:128 to 134 budgets 2,292 mappings.
- Fix: print the four counts and the covered percentage at M0 as informational, keep fail-closed at M1 per the Q5 default (brief lines 503 to 504), mark the M0 form REOPENED.

### F5 TRACE-ERASURE-LEG.  SURVIVABLE.  The second leg is a REFUSE program on the rows that matter.
- P3 section 5 argues from erase.ml:102-104, quantity.ml:7-22 and eterm.ml:24-38 (VERIFIED S1:127 to 129), sound for the term and silent on the type.  Brief lines 306 to 307 and 312 to 313 pick `Word32` and the bare instruction when a bound proof is in scope, so the instruction depends on the TYPE of a quantity-0 binder.  P3:34 has "a Word32 literal with a bound proof" in ACCEPT and P3:35 to 37 "an unproved Word32 addition" in REFUSE, so the program "without its proof terms" (brief lines 114 to 116) is refused on every bound-proof row and the gate has no second ELF there.
- Fix: define the second leg as each proof term replaced by a quantity-0 postulate of the same type (A/lib/global.ml:33-38), state the theorem as "erase output is a function of the quantity-1 skeleton and the binder types", print the compared row list.

### F6 OVERLAY-PORT-ACCOUNTING.  SURVIVABLE.  The patched files are not shared byte for byte.
- P3:62: "a 212-line delta over files assay and veil share byte for byte".  VERIFIED diff A/lib against V/lib, changed lines: check 37, conv 0, eval 0, rules 662.  S1:155 cut the overlay delta against veil (check 102, rules 53), so the rules patch lands on a file that differs by 662 lines.
- "Overlay ported" (P3:129) is a merge over rules.ml, not a 480-line patch.  P3:141 moves the kernel bound to 7,000 in the paragraph that says a moved bound is a finding.
- Fix: state the port as check 37 plus rules 662 lines of merge context, mark the 7,000 bound REOPENED, schedule the port at M1 (F2 fix).

### F7 R3-BELIEVED-ROWS.  SURVIVABLE.  Target facts cited from BELIEVED rows.
- Right: fd 13 (S2:88, VERIFIED), and the codes in P3:87 to 94 follow S2.  BELIEVED used as fact: RV32 unsupported on v6.1.0 (S2:27), 8-byte pointer alignment (P3:84), the UINT256_MUL layout (P3:92), twin cycle parity with `total_instruction_count()` (P3:109, no ecall cycle rule).  ENCODE-DIFF (P3:131) needs the Homebrew clang (S2 section 8), no path named.
- Fix: mark each row BELIEVED with its settle step, pin the clang path and the ecall cycle rule before EXEC-DIFF binds.

## Verdict
P3 concedes the flip, which is honest, but its parity spine stands on two shapes the carried kernel refuses and a count-mode gate that fails on 2,292 names, and its R2 answer adds a level solver to a 1.956 checker with no measured denominator.  NOT READY as written: F3 to F7 close with edits, F1 and F2 need a budgeted SPar rule at Stage A and a costed walk lever before rung 5 binds.
