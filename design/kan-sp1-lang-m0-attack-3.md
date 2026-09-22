# kan-sp1-lang M0 plan attack K3: executability and house form

Date: 2026-09-22.  Lens: K3 (stage order, unit briefs, dropped sibling conventions, house form).  Plan: /Users/oobi/Documents/attest-m0/M0-PLAN.md.

## Findings, ranked

### K3-1  section 10 Stages A to F, Stage B  blocking

Claim: Stage B runs TRACE-ERASURE, a gate that compares two ELFs per row, before lower/, elf/ and corpus/ exist.  VERIFIED.
Evidence: plan:418 (`attest build --erase` on corpus/ then `cmp` per row, the ELF with proof bodies is byte-identical to the ELF with opaque proofs, binding);  plan:565 (B4 runs TRACE-ERASURE, gate ids TRACE-ERASURE LEAN-TWIN);  plan:567 (C1 lower/ and C2 elf/ land at Stage C);  plan:571 (corpus/ is frozen at 16 rows at Stage F);  plan:551 (verify-final reruns every leg and refuses an open finding);  plan:395 (a binding FAIL prints GATES-FAIL);  plan:23 (OQ7 compares ELFs).
Fix: at Stage B define TRACE-ERASURE over the erased terms of the seed fixtures (an erased-term print per row, `cmp` per row, rows = the fixtures/ count) and move the ELF form of plan:418 to Stage C as a second leg after C2;  or move the gate id to Stage C and let B4 run LEAN-TWIN only.

### K3-2  section 10 Stages A to F, Stage C  blocking

Claim: Stage C runs ELF-ACCEPTED through the crate attest-harness, and D3 writes that crate at Stage D.  VERIFIED.
Evidence: plan:426 (`cargo run -p attest-harness -- execute corpus/ROW.elf`, binding);  plan:567 (C4 runs ELF-ACCEPTED, gate ids ENC-XCHECK ELF-ACCEPTED);  plan:569 (D3 builder writes harness/ on sp1-sdk 6.1.0);  plan:93 (ELF-ACCEPTED waits on step 6 because the executor call runs through the harness, BELIEVED there);  plan:557 and plan:669 (the stages run in order and each ends in a commit).
Fix: move D3 into Stage C as the unit before C4, with USER step 6 and the harness compile as its waits;  or move ELF-ACCEPTED to the Stage D gate ids and let C4 run ENC-XCHECK only.

### K3-3  section 8 Gates and section 2 Stage 0  major

Claim: three gate commands run `cargo run`, a cargo compile in an agent's hands at every gate run, which the plan bans under the open floor;  the harness compile is a USER action with no step number, no command and no output path.  VERIFIED.
Evidence: plan:426 and plan:453 (`cargo run -p attest-harness`);  plan:432 (EXEC-DIFF runs the harness `execute`);  plan:104 and plan:603 (no cargo, forge or opam build in an agent's hands while the floor is open, no cargo install);  plan:71 (the floor stays open);  plan:81 and plan:94 (a harness compile the user runs, plan decision, BELIEVED);  brief:373-374 (`-j 2`, cargocho over raw cargo);  tpl:247 (the same ban under the floor).
Fix: add USER step 9 to section 2, `cargocho build -- --release -j 2 --manifest-path harness/Cargo.toml`, recorded in dev/TOOLCHAIN.md;  rewrite plan:426, plan:432 and plan:453 to call `harness/target/release/attest-harness`;  make D5, F3 and F4 wait on step 9.

### K3-4  section 8 Gates against section 7 Driver  major

Claim: gate commands call six driver verbs that section 7 does not define, and R0-DIFF has three different commands.  VERIFIED.
Evidence: plan:127 (driver: check | build | run | spec-count);  plan:355-371 (the 7.2 verb table;  `rg -n 'r0-diff|emu|enc-xcheck|host-roster'` over that window matched only `attest run`);  plan:399 (the verb names are BELIEVED until part 7 fixes them);  plan:409 (`attest r0-diff`), plan:411 (`attest axioms`), plan:425 (`attest enc-xcheck`), plan:432 (`attest emu`), plan:433 (`attest host-roster`), plan:441 (`attest lower`);  plan:241 (R0-DIFF is `diff -q dev/r0-diff/*.ml lib/*.ml`);  plan:563 (A2 writes dev/r0-diff.sh).
Fix: add one 7.2 row per verb the gates call, or rewrite each gate command as a dev/*.sh script over the four verbs;  pin R0-DIFF to `zsh dev/r0-diff.sh`, which prints `R0-DIFF vs=2c2e6e6 rows=3 diff=0`, and delete the two other forms.

### K3-5  section 12 M0-EXIT against section 10  major

Claim: dev/TOOLCHAIN.md is an M0-EXIT criterion and a layout entry, and no unit of any stage writes it.  VERIFIED.
Evidence: plan:623 (USER steps 1 to 8 recorded in dev/TOOLCHAIN.md);  plan:134 (the layout row);  plan:563 (A1 writes CARRIED.md, dev/PIN, dune-project, the licenses, README.md and SPEC.md;  A2 writes dev/r0-diff.sh);  plan:551 (closers write dev/M0-BUILD-LOG.md and dev/MUTATION-LOG.md);  plan:565-571 (no B to F unit names it);  `rg -n 'TOOLCHAIN\.md'` on the plan hits only lines 134, 623 and 657.
Fix: add to A1 at plan:563 "write dev/TOOLCHAIN.md with the eight USER steps of section 2 and their status" and to the closer at plan:551 "refresh the status column of dev/TOOLCHAIN.md";  or drop the file from plan:623.

### K3-6  section 3 Repository layout and section 10, A2  minor

Claim: the plan holds dev/dunecho.sh and dev/dune.sh as BELIEVED one script under two names;  the diff settles it, they differ.  VERIFIED.
Evidence: plan:104 (BELIEVED, settled by diff at Stage A);  `diff /Users/oobi/Documents/kan-sp1-lang-mech-pin/dev/dunecho.sh /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev/dune.sh` printed `2,30c2,8` (mech: MECH_OPAM_SWITCH, the zxcaml-p1 switch and `exec dunecho`;  assay: a dune-on-PATH check);  plan:563 (A2 copies dev/dunecho.sh from the mech pin);  assay dev/pin-dune.sh and 20 dev/*-test.py scripts call dev/dune.sh (`rg -c 'dune\.sh'`).
Fix: rewrite plan:104 as VERIFIED, the two differ;  A2 copies the mech script and renames MECH_OPAM_SWITCH to ATTEST_OPAM_SWITCH;  A2 states that it does not carry the dev/*-test.py scripts.

### K3-7  whole plan, section 11 Prose  minor

Claim: 25 clauses exceed 40 words;  ASD-STE100 caps a descriptive sentence at 25 words and section 11 asks for short sentences.  VERIFIED.
Evidence: `python3 -P` split on `.  ` and `;  ` over the plan: plan:551 at 79 words, plan:42 at 75, plan:207 at 68, plan:11 at 65, plan:23 at 64, plan:106 at 59, plan:54 at 58, plan:667 at 57;  plan:611 (short declarative sentences, one instruction per sentence);  brief:370.
Fix: split each clause over 25 words at its semicolons and its "and" joins;  one claim per sentence with its own VERIFIED tag.

## Form checks that passed

Em dashes 0, en dashes 0, non-ASCII 0 (`python3 -P` count with chr(8212) and chr(8211), VERIFIED).  `rg -n '[.] [A-Z]'` and `rg -n '; [A-Za-z]'` printed nothing (VERIFIED).  PENDING is absent (VERIFIED).  Never commit stands at plan:607 in section 11 (VERIFIED).  The cap text at plan:535, the tiers at plan:539, the handoff files at plan:543, the dead-unit rule at plan:547, the review-kit close at plan:551 and dunecho at plan:104 and plan:563 are all present (VERIFIED).

## Verdict

The plan cannot run as written: Stage B and Stage C each gate on an artifact a later stage builds, and section 8 calls driver verbs and a harness binary that no unit or USER step provides (K3-1, K3-2, K3-3, K3-4).  House form is clean on dashes, spacing, PENDING and never commit;  the sentence length rule of section 11 is the one form miss (K3-7).
