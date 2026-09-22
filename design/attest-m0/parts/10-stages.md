## 10 Stages and the build workflow shape

Six stages after Stage 0, A to F, in dependency order (verdict:117, VERIFIED).  Each stage is one Workflow run that opens on the user's "use a workflow" opt-in (brief:541 tail, VERIFIED;  the per-stage opt-in is a plan decision by delta from tpl2:177, BELIEVED until the user rules a standing opt-in as at tpl:288).  Every agent prompt in every stage carries the string "(7 findings max, 56 agents max)" (tpl:218 and brief:371, VERIFIED).  Each stage has builders that write code in chunks of at most 8 KB per tool call, a verifier that runs the stage gates and the stage mutants and returns at most 7 findings, one fix round, and a review-kit close that ends in a printed commit command (tpl2:177, VERIFIED as the house shape).  No agent commits at any stage;  the user commits after every stage (tpl:218 and brief:368-369, VERIFIED).

### Tiers

Builder units run on Fable at xhigh effort.  Verifier units run on Fable at max effort.  Closer units run on Opus at medium effort.  Finder units of the review kit run at the builder tier.  The tiers are the caller's roster for this workflow (the task text of this plan's writers, VERIFIED as that text);  each stage brief repeats them in its roster.

### Handoff files

Every unit writes its handoff file as its FIRST tool call, three lines: goal, inputs, output paths.  The unit appends one progress line after every file write, so a cut-off unit leaves a trail.  The handoff directory is /Users/oobi/Documents/attest-m0/handoff/stage-X/ with one file per unit, UNIT.md (plan decision by delta from this plan's own /Users/oobi/Documents/kan-sp1-lang-m0-handoff/, BELIEVED until the Stage A brief pins it).  A unit whose prompt starts with a RETRY marker reads its handoff file and the files it names first and continues;  it does not restart.

### Dead-unit rule

A null builder or verifier, a unit that returns no result, retries ONCE on opus with a RETRY marker in its prompt;  a second null halts the stage, and the stage reports both request ids.  A null finder or closer is reported as unmet;  the stage does not retry it and the close prints UNMET on that row.  The rule is the caller's, quoted from the task text of this plan's writers (VERIFIED as that text).

### Review-kit close

The close of each stage is a review kit over the staged tree: finders return at most 7 findings each, one fix round applies them, a verify-final reruns every gate leg of the stage on the staged tree and refuses any finding still open, then the closer writes the dated entry in dev/M0-BUILD-LOG.md, the mutation rows in dev/MUTATION-LOG.md, stages the tree and prints one commit command of this form and stops (tpl:229-233 and tpl2:177, VERIFIED as the two forms;  the attest paths are this plan's).

```
git -C /Users/oobi/Documents/attest commit -s -F /Users/oobi/Documents/attest-m0/stage-A-commit-msg.txt
```

Stage F opens only after A to E are committed by the user (tpl:229, VERIFIED as the assay rule;  the attest form is a plan decision).

### Stages A to F

Each stage below names its units with one-line briefs, its gate ids from verdict:117 (VERIFIED) and what it waits on (part 2).  The unit split is a plan decision (BELIEVED until each stage brief pins it).  Every unit name is STAGE plus a number;  the verifier, the fixer and the close are the last three units of every stage.

Stage A, carry.  Units: A1 builder, clone lib/, surface/ and test/ verbatim from the assay pin eebe37e into /Users/oobi/Documents/attest and write CARRIED.md, dev/PIN, dune-project, LICENSE-MIT, LICENSE-APACHE, README.md and SPEC.md with the R0 block marked inherited;  A2 builder, copy dev/dunecho.sh from the mech pin and dev/gates.sh, carry-check.sh, r0-count.sh, r0-audit.sh, trusted-lines.sh, house.sh and bench.sh from the assay pin, write dev/r0-diff.sh, and make TRUSTED-LINES print the four OQ4 rows;  A3 verifier, run BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS-empty and TRUSTED-LINES rung 1 and the Stage A mutants of section 9;  A4 fixer, one round;  A5 review-kit close.  Gate ids: BUILD CARRY R0-COUNT R0-AUDIT R0-DIFF SUITE-KERNEL AXIOMS-empty TRUSTED-LINES rung 1.  Waits on no open USER step (part 2).  Commit message: /Users/oobi/Documents/attest-m0/stage-A-commit-msg.txt.

Stage B, erase.  Units: B1 builder, erase/ with the opaque-proof evaluator that never unfolds a quantity-0 global (brief:541 OQ7, VERIFIED);  B2 builder, fixtures/ with the two A1 F2 fixtures of USER step 8 and the Acc fixture, and twin/ with the Lean twin sources;  B3 builder, the TRACE-ERASURE and LEAN-TWIN legs in dev/gates.sh;  B4 verifier, TRACE-ERASURE on every corpus row present and LEAN-TWIN 24/24 12/12 and the Stage B mutants;  B5 fixer;  B6 review-kit close.  Gate ids: TRACE-ERASURE LEAN-TWIN.  Waits on USER step 8 for the green TRACE-ERASURE row (part 2, verdict:136).  Commit message: stage-B-commit-msg.txt beside the Stage A one.

Stage C, lower and encode.  Units: C1 builder, lower/ from the erased term to RV64IM at most 1,100 lines (brief:541 OQ1 and OQ4, VERIFIED);  C2 builder, elf/ the ELF64 encoder at most 800 lines, with no LLVM, no rustc, no external assembler and no linker (brief:94-98, VERIFIED);  C3 builder, the ENC-XCHECK and ELF-ACCEPTED legs;  C4 verifier, ELF-ACCEPTED on a halt-only ELF64 through the SP1 v6.1.0 executor and ENC-XCHECK on every emitted instruction and the Stage C mutants;  C5 fixer;  C6 review-kit close.  Gate ids: ENC-XCHECK ELF-ACCEPTED.  Starts without any open step;  ENC-XCHECK waits on USER step 3 (part 2).

Stage D, emulator and harness.  Units: D1 builder, emu/ the OCaml RV64IM emulator twin (brief:541 OQ1, VERIFIED);  D2 builder, host/ with Read, Commit and Halt and the SHA-256 commit path of Halt (brief:541 OQ5 and verdict:151, VERIFIED);  D3 builder, harness/ the pinned Rust harness on sp1-sdk 6.1.0 at most 100 lines under the Rust rules of section 11;  D4 builder, the EXEC-DIFF, HOST-ROSTER and PUBVAL-DIGEST legs;  D5 verifier, EXEC-DIFF row for row on every corpus row present, HOST-ROSTER, PUBVAL-DIGEST and the Stage D mutants;  D6 fixer;  D7 review-kit close.  Gate ids: EXEC-DIFF HOST-ROSTER PUBVAL-DIGEST.  Starts after Stage C;  the `cargo fetch` of sp1-sdk 6.1.0 is USER step 6 (brief:543, VERIFIED).

Stage E, effects.  Units: E1 builder, Keccak, Sha256 and U256Mul as Host constructors, U256Mul at syscall 0x0001011D, and their software twins in emu/ (brief:541 OQ5, VERIFIED);  E2 builder, the GUARD-TWIN and LOWER-REFUSE legs;  E3 verifier, GUARD-TWIN and LOWER-REFUSE green with EXEC-DIFF and TRACE-ERASURE still green over the six-constructor roster and the Stage E mutants;  E4 fixer;  E5 review-kit close.  Gate ids: GUARD-TWIN LOWER-REFUSE.  Waits on Stage D and on no open step (part 2).  Bn254 and Secp256k1 stay out until M2 (brief:541 OQ5, VERIFIED).

Stage F, freeze.  Units: F1 builder, corpus/ frozen at 16 EXEC-DIFF rows with CYCLE-BUDGET pinned per program;  F2 builder, dev/denominator.sh, dev/denominators.json and DENOMINATORS.sha256 read from the USER step 7 freeze, M0-TIME, rung 2 and rung 3 at most 2.0 informational, PASSES and the hashconsing bench;  F3 builder, PROVE-ONCE on the smallest row, done or OPEN;  F4 verifier, the whole battery of section 8 and every mutant of section 9;  F5 fixer;  F6 review-kit close, which also writes the MEASURE table of dev/M0-BUILD-LOG.md.  Gate ids: CYCLE-BUDGET M0-TIME DENOMINATORS PASSES PROVE-ONCE and the M0 gate of verdict:118.  Starts after Stage E;  M0-RATIO and rung 3 print and do not gate (brief:541 OQ2, VERIFIED);  DENOMINATORS prints OPEN while `bend` is not on PATH (brief:543, VERIFIED).

Order: A, B, C, D, E, F in sequence, each on the user's opt-in.  Each brief quotes this plan's section numbers and the verdict's lines, and every builder reads the assay pin for the seam it carries (tpl2:186, VERIFIED as the form).  If USER step 5 prints a mechanism-lang median under 211 ms before Stage A closes, Stage A reopens as a re-carry from the mech pin 1e4f371 (brief:541 OQ6, VERIFIED;  the re-carry rule is BELIEVED until the median prints).
