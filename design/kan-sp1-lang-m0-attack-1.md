# kan-sp1-lang M0 plan: attack K1 (consistency with the rulings and the pins)

Date: 2026-09-22.  Lens: K1, contradiction or silent amendment of OQ1 to OQ7, R0 to R4, the milestone line and the Stage 0 status.  Plan: /Users/oobi/Documents/attest-m0/M0-PLAN.md.

## Findings (ranked)

Checks that passed (VERIFIED): the seven OQ quotes at M0-PLAN.md:11-23 match brief:541 word for word (Read of both);  the milestone stages A to F and their gate ids at M0-PLAN.md:563-573 match verdict:117 (Read);  the name attest, the extension .att and the driver word at M0-PLAN.md:340 match verdict:140 (Read);  the pins print eebe37e, 1e4f371 and a7534ce (`git -C <pin> rev-parse --short HEAD` and `git -C <mech-pin> submodule status`, read only, 2026-09-22).

### K1-1  Section 8 Gates  major

Claim: four gate commands use driver verbs or flags that verdict:140 and section 7 do not define, so the gates exit 64 as written.  VERIFIED.
Evidence: /Users/oobi/Documents/attest-m0/M0-PLAN.md:411 `attest axioms corpus/`;  :441 `attest lower corpus/refuse/ROW`;  :447 `attest cycles corpus/`;  :451 `attest build --count-passes corpus/`.  The driver line at /Users/oobi/Documents/kan-sp1-lang-design-verdict.md:140 lists check, build, run, --axioms, --externs, --passes and spec-count only.  The plan moves axioms to a flag of check at M0-PLAN.md:340, names `--passes` at :378 and makes an unknown verb or flag exit 64 at :353.  Command: `rg -n -o 'attest (lower|cycles|axioms|build --count-passes)' M0-PLAN.md`.
Fix: rewrite the four commands with section 7 forms.  AXIOMS: `attest check --axioms FILE` per row.  LOWER-REFUSE: `attest build corpus/refuse/ROW -o OUT` with exit 2 expected.  CYCLE-BUDGET: `attest run ROW.elf` per row through dev/cycles.sh.  PASSES: `attest build --passes FILE -o OUT` with the line of :378.

### K1-2  Section 8 Gates, Count, and Section 10 Stage F  major

Claim: DENOMINATORS is counted binding, yet two lines say it prints OPEN while bend is absent;  under the plan's own statuses a binding row must print PASS, so M0-EXIT waits on Bend 2 against brief:543 and OQ2.  VERIFIED.
Evidence: /Users/oobi/Documents/attest-m0/M0-PLAN.md:463 (20 binding rows include DENOMINATORS;  every binding row must print PASS);  :573 and :108 (DENOMINATORS prints OPEN until USER steps 2 and 7);  :395-397 (binding FAIL blocks M0-EXIT;  OPEN-printing is a separate status);  :450 (the shasum rule passes with the Bend 2 row written as OPEN).  /Users/oobi/Documents/kan-sp1-lang-design-brief.md:543 "the M0 plan does not wait on Bend 2";  brief:541 OQ2.
Fix: keep the :450 rule as the only form: DENOMINATORS binds on `shasum -a 256 -c` with the Bend 2 row inside denominators.json written as OPEN.  Delete "prints OPEN" at :108 and :573.  Or move DENOMINATORS to OPEN-printing at :463 and recount 19 binding, 3 informational, 2 OPEN-printing.

### K1-3  Section 10 Stages A to F, Order  major

Claim: line 575 adds "before Stage A closes" to the OQ6 flip trigger and marks it VERIFIED at brief:541;  the ruling keeps the flip open until USER step 5 prints, with no stage deadline, as lines 21, 264 and 671 state.  VERIFIED.
Evidence: /Users/oobi/Documents/attest-m0/M0-PLAN.md:575 against /Users/oobi/Documents/kan-sp1-lang-design-brief.md:541 OQ6 ("the flip stays open until USER step 5 prints a mechanism-lang median on the 77 fixtures, and flips only under 211 ms") and M0-PLAN.md:21, :264, :671.  Command: `rg -n -o '.{0,70}211 ms.{0,90}' M0-PLAN.md`.
Fix: delete the clause "before Stage A closes" at :575 so the sentence reads as :671.  If a deadline is wanted, record it on the section 12 decision sheet as a plan decision, BELIEVED, for a USER ruling;  do not cite brief:541 for it.

### K1-4  Section 2 Stage 0 and Section 10 Stage D  major

Claim: section 2 marks step 1 DONE though its 30 GiB target is unmet at 21 GiB;  section 11 gates every cargo build on that floor, and Stage D names no floor wait for the D3 harness build that EXEC-DIFF needs.  VERIFIED.
Evidence: /Users/oobi/Documents/attest-m0/M0-PLAN.md:71 and :87 ("Status DONE, the floor stays open"), :667 ("Step 1 ... done"), :593 (cargo "only when the disk floor allows a build"), :569 (Stage D waits: only USER step 6).  /Users/oobi/Documents/kan-sp1-lang-design-verdict.md:129 ("diskfree --apply to 30 GiB");  /Users/oobi/Documents/kan-sp1-lang-design-brief.md:541 ("Stage 0 USER steps stay open: diskfree --apply (21 GiB free on 09-22)") and :543 ("free space stays at 21 GiB, under the 30 GiB floor").
Fix: at :71, :87 and :667 write step 1 as "ran, target unmet, OPEN at 21 GiB".  At :569 add "D3 waits on step 1 (30 GiB free)".  At :573 name the same wait for PROVE-ONCE.  Keep :593 as it stands.

### K1-5  Section 7.2 Verbs  minor

Claim: three output forms for one verb: 7.2 prints `R0-COUNT formers=<n> shapes=<n>`, 5.3 diffs the SPEC.md fenced block and names `formers 2: Lan Ran`, 4.2 records the assay form;  R0-COUNT under R0 prints the former count from SPEC.md.  VERIFIED.
Evidence: /Users/oobi/Documents/attest-m0/M0-PLAN.md:362, :239, :243, :161;  /Users/oobi/Documents/kan-sp1-lang-design-brief.md:59.
Fix: pin one output line at :362 equal to the SPEC.md fenced block that :239 diffs, and make :243 quote that same line.

## Verdict

NOT OK: four major findings (K1-1 to K1-4) stand on the plan's own lines against verdict:140, brief:541 and brief:543;  the OQ quotes, the milestone line, the name and the pin shas hold.
The plan can pass K1 after the five edits above;  none needs a new USER ruling unless the K1-3 deadline is kept.
