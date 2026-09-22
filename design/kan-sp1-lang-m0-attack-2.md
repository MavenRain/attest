# kan-sp1-lang M0 plan attack K2: gate and budget feasibility

Date: 2026-09-22.  Lens: K2 (gate and budget feasibility).  Plan: /Users/oobi/Documents/attest-m0/M0-PLAN.md.

Sources: /Users/oobi/Documents/kan-sp1-lang-design-verdict.md:115-137; /Users/oobi/Documents/kan-sp1-lang-design-brief.md:337-356 and 537-543; /Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md (syscall and ELF spans).

## Findings (ranked)

Path key: plan = /Users/oobi/Documents/attest-m0/M0-PLAN.md;  verdict = /Users/oobi/Documents/kan-sp1-lang-design-verdict.md;  brief = /Users/oobi/Documents/kan-sp1-lang-design-brief.md;  tool = /Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md.

### K2-1  section 10 Stages A to F, section 8 Stage C rows  BLOCKING
Claim: ELF-ACCEPTED is a Stage C gate that unit C4 runs at the Stage C close, but its command is the harness that unit D3 writes at Stage D, so Stage C cannot close as written.  VERIFIED.
Evidence: plan:426 (`cargo run -p attest-harness -- execute corpus/ROW.elf`);  plan:567 (C4 runs ELF-ACCEPTED;  Stage C starts without any open step and names only the step 3 wait);  plan:126 and plan:569 (harness/ is a Stage D artifact, unit D3);  plan:93 (section 2 says ELF-ACCEPTED waits on step 6 and the harness).
Fix: move unit D3 (harness/) into Stage C before the ELF-ACCEPTED leg and add "ELF-ACCEPTED waits on step 6 and the user's harness build" at plan:567;  or move ELF-ACCEPTED to the Stage D gate ids at plan:569 and plan:428 and delete it from plan:567.

### K2-2  section 4.3 The TRUSTED-LINES arithmetic  MAJOR
Claim: the encoder and harness rows walk folders that the layout never creates, and an absent folder prints 0/<bound> with no FAIL, so the OQ4 bounds 800 and 100 never bind at M0.  VERIFIED.
Evidence: plan:187 (`("encoder", 800, "encode", ...)`, `("harness", 100, "sp1-exec-harness", ...)`, "A row whose folder is absent prints 0/<bound> and does not fail");  plan:122 (the encoder lives in elf/);  plan:126 (the harness lives in harness/);  plan:453 (the crate is attest-harness);  brief:541 OQ4 (encoder 800, harness 100).
Fix: at plan:187 write `("encoder", 800, "elf", (...))` and `("harness", 100, "harness", ("src/main.rs",))`;  make an absent folder FAIL from the stage that first measures it (plan:151-152);  use one harness name at plan:152, plan:187 and plan:453;  keep the walk rooted at the folder so emu/rv64im.ml (plan:143) never joins the encoder count.

### K2-3  section 8 Stage F rows and Count  MAJOR
Claim: DENOMINATORS is binding in section 8, yet sections 2 and 10 make it print OPEN while bend is absent;  a binding row has only PASS or FAIL and the Count requires PASS, so M0-EXIT waits on Bend 2 against OQ2.  VERIFIED.
Evidence: plan:450 (status binding);  plan:395 (binding: FAIL blocks M0-EXIT);  plan:463 ("every other binding row must also print PASS";  PROVE-ONCE is the only OPEN-printing gate);  plan:96 ("DENOMINATORS row waits on steps 2 and 7 and prints OPEN without them");  plan:573 ("DENOMINATORS prints OPEN while bend is not on PATH");  brief:543 ("the M0 plan does not wait on Bend 2").
Fix: at plan:450 set the status to OPEN-printing, line `DENOMINATORS OPEN reason=bend-absent` until step 7 and PASS on the hash match after it;  at plan:463 write 19 binding and 2 OPEN-printing;  or keep binding and rewrite plan:96 and plan:573 to "prints PASS on the hash match with the Bend 2 row inside denominators.json as the word OPEN".

### K2-4  section 5.2 The M0 constructs, section 8 Count  MAJOR
Claim: section 5 names EXTERN-ROSTER as the Stage E gate on precompile postulates, but section 8 has no row for it, the Count omits it, section 9 has no mutant for it and verdict:117 does not name it.  VERIFIED.
Evidence: plan:226 ("Gates: HOST-ROSTER, EXTERN-ROSTER");  plan:230 ("Gate: EXTERN-ROSTER at Stage E");  plan:196 (the --externs disclosure row names it);  plan:463 (24 gates, none is EXTERN-ROSTER);  plan:440-441 and plan:515-518 (Stage E rows and mutants name only GUARD-TWIN and LOWER-REFUSE);  verdict:117 (Stage E: GUARD-TWIN, LOWER-REFUSE).
Fix: add a Stage E row after plan:441: EXTERN-ROSTER, `attest check --externs corpus/ROW` per row, PASS when the printed extern set equals the row's Keccak Sha256 U256Mul uses and nothing else, binding;  add the mutant "extern name" after plan:518;  add one to the Count at plan:463;  or delete the name at plan:196, plan:226 and plan:230 and fold the check into HOST-ROSTER.

### K2-5  section 9 Stage F mutants  MAJOR
Claim: the "cycle pin" mutant expects CYCLE-BUDGET to fail, but CYCLE-BUDGET is informational and prints INFO drift and no FAIL at M0;  the section 9 rule makes a gate whose mutant does not fail vacuous and blocks its stage, so Stage F blocks itself.  VERIFIED on the rule and the status;  the expected text cell of plan:526 is BELIEVED (settle: read plan:526 in full).
Evidence: plan:526 (mutant cycle pin, gate CYCLE-BUDGET);  plan:447 ("a drift against the pin prints INFO drift and no FAIL", informational);  plan:396 (informational never fails the run at M0);  plan:466 ("A gate whose mutant does not fail is vacuous and blocks its stage").
Fix: at plan:466 add "an informational row passes its mutant when it prints the expected INFO line";  at plan:526 set the expected text to `CYCLE-BUDGET row=R cycles=N syscalls=M INFO drift`.

### K2-6  section 10 Stages A to F  MINOR
Claim: the Stage F gate id list omits M0-RATIO and HASHCONS-BENCH, which the milestone line names for Stage F and section 8 defines.  VERIFIED.
Evidence: plan:573 ("Gate ids: CYCLE-BUDGET M0-TIME DENOMINATORS PASSES PROVE-ONCE");  verdict:117 ("rung 2 and rung 3 at most 2.0 informational", "hashconsing bench");  plan:449 and plan:452 (the two rows).
Fix: at plan:573 write "Gate ids: CYCLE-BUDGET M0-TIME M0-RATIO DENOMINATORS PASSES HASHCONS-BENCH PROVE-ONCE and the M0 gate of verdict:118".

### K2-7  section 9 Stage F mutants  MINOR
Claim: the "missing line" mutant names "the run itself" as its gate;  no row of the 24 in section 8 carries that name, so no section 8 gate catches it and the mutation log has no FAIL line to cite.  VERIFIED.
Evidence: plan:528 (gate column "the run itself");  plan:463 (the 24 gate names);  plan:466 (every row names the gate that must catch it and the expected failure text).
Fix: give the check a row after plan:453: GATES-COMPLETE, `zsh dev/gates.sh COUNT`, `GATES-COMPLETE expected=24 printed=N`, FAIL on any missing line, binding;  add one to the Count at plan:463 and cite GATES-COMPLETE at plan:528.

## Verdict

Not OK: one blocking finding (K2-1, Stage C closes on a Stage D binary) and four major ones (two OQ4 budgets that never bind, a DENOMINATORS status no gate can hold, a gate with no row, a Stage F mutant rule that blocks itself);  every finding cites plan lines and a source line and none rests on a peer tree.
Fix K2-1 to K2-5 before the plan is ruled;  K2-6 and K2-7 are one-line edits that ride the same round.
