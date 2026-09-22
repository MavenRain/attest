export const meta = {
  name: 'kan-sp1-lang-m0-plan',
  description: 'kan-sp1-lang M0 plan for attest by copy then delta from the assay M0 plan: 1 skeleton, 4 concurrent section writers, 1 assembler, 3 attacks, 1 adjudicator, 1 fixer, 1 closer; every unit leaves a handoff file and a dead unit retries once on opus then halts (7 findings max, 56 agents max)',
  phases: [
    { title: 'Skeleton', detail: 'mkdir the attest-m0 tree and the handoff directory, write parts 00 to 03: bindings, scope, Stage 0, layout (7 findings max, 56 agents max)' },
    { title: 'Sections', detail: 'four concurrent section writers through pipeline: G1 budgets and kernel, G2 emission and driver, G3 gates and mutants, G4 stages, house rules, exit and next (7 findings max, 56 agents max)' },
    { title: 'Assemble', detail: 'cat the 14 part files in name order into M0-PLAN.md and count the headings, the dashes and the word PENDING' },
    { title: 'Attack', detail: 'three parallel attacks on the assembled plan: K1 rulings and pins, K2 gates and budgets, K3 executability and house form (7 findings max, 56 agents max)' },
    { title: 'Adjudicate', detail: 'merge the three reports, re-read every cited line, at most 7 CONFIRMED findings with exact edits (7 findings max, 56 agents max)' },
    { title: 'Fix', detail: 'apply the confirmed edits with the Edit tool in chunks under 8 KB and append a dated corrections block to section 12' },
    { title: 'Close', detail: 'verify the plan and the four report files on disk and return the record' },
  ],
}

const D = '/Users/oobi/Documents'
const BRIEF = '/Users/oobi/Documents/kan-sp1-lang-design-brief.md'
const VERDICT = '/Users/oobi/Documents/kan-sp1-lang-design-verdict.md'
const P1 = '/Users/oobi/Documents/kan-sp1-lang-proposal-1.md'
const TOOL = '/Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md'
const TPL = '/Users/oobi/Documents/assay-m0/M0-PLAN.md'
const TPL2 = '/Users/oobi/Documents/mechanism-lang-m0/M0-PLAN.md'
const OUT = '/Users/oobi/Documents/attest-m0'
const PARTS = '/Users/oobi/Documents/attest-m0/parts'
const PLAN = '/Users/oobi/Documents/attest-m0/M0-PLAN.md'
const HANDOFF = '/Users/oobi/Documents/kan-sp1-lang-m0-handoff'
const ASSAY_PIN = '/Users/oobi/Documents/kan-sp1-lang-assay-pin'
const MECH_PIN = '/Users/oobi/Documents/kan-sp1-lang-mech-pin'
const SCRATCH = '/private/tmp/claude/kan-sp1-lang-m0-plan'
const DATE = (typeof args === 'object' && args && args.date) ? args.date : '2026-09-22'
const ATTACKS = ['/Users/oobi/Documents/kan-sp1-lang-m0-attack-1.md', '/Users/oobi/Documents/kan-sp1-lang-m0-attack-2.md', '/Users/oobi/Documents/kan-sp1-lang-m0-attack-3.md']
const ADJ = '/Users/oobi/Documents/kan-sp1-lang-m0-adjudication.md'
const PART_NAMES = ['00-bindings.md', '01-scope.md', '02-stage0.md', '03-layout.md', '04-budgets.md', '05-kernel.md', '06-emission.md', '07-driver.md', '08-gates.md', '09-mutants.md', '10-stages.md', '11-house.md', '12-exit.md', '13-next.md']
const PART = (n) => PARTS + '/' + n
const RETRY = '[RETRY after a cut-off: read the handoff file and the part file first, continue from them, do not restart]'

const BRIEF_MAP = 'brief line map (543 lines): 2 pins 31-131 (R0 36-65, R1 66-82, R2 83-104, R3 105-126, R4 127-131); 4.2 boundary 287-301; 4.3 runtime 302-314; 4.4 pipeline 315-330; 4.6 gates 337-356; 5 house rules 357-377; 9 questions 457-536 (Stage 0 user steps 517-526, pin removal 527-536); 10 rulings 537-543 (the 2026-09-21 paragraph, the 2026-09-22 ratify-all paragraph with OQ1 to OQ7, the 2026-09-22 Stage 0 status paragraph at the tail)'
const VERDICT_MAP = 'verdict line map (155 lines): Ratification 5, Scores 9, Winner 21, Probes 25, Per-proposal 59, Findings 73, The synthesized design 94, Milestones M0 to M3 115-122, Trusted lines 123-126, Stage 0 USER steps 127-137, Name 138-144, Open questions 145-155'
const TPL_MAP = 'assay M0 plan section map (288 lines, the copy-then-delta template for the document): 0 Bindings 21, 1 M0 scope 38, 2 Stage 0 75, 3 Repository layout 102, 4 Trusted base and budgets 136, 5 The kernel term at M0 151, 6 Emission 163, 7 Driver 173, 8 Gates 179, 9 Mutants 205, 10 Stages and the build workflow shape 216, 11 House rules 235, 12 M0-EXIT stamp, decisions, corrections 249, 13 What happens next 279'
const TPL2_MAP = 'mechanism-lang M0 plan section map (223 lines, the second reference for sections 10 and 11): 9 Gates and denominators 147-174, 10 Stages and the build workflow shape 175-187, 11 House rules and the trusted base 188-195, 12 M0-EXIT stamp and decision sheet 196-217, 13 What happens next 218-223'

const STYLE = `
WRITING RULES for every file you write: short declarative sentences in ASD-STE100 form (one instruction per sentence, active voice, simple approved words).  TWO spaces after every sentence-ending period and after every semicolon (a hook enforces this on .md files).  No em-dashes and no en-dashes, in files and in your return text.  No filler.  ASCII only.  Every claim carries VERIFIED (with the command, the path:line or the URL that proves it) or BELIEVED (with what would settle it).  Cite source evidence as path:line in every claim.  The word PENDING never appears in a part file, in the plan or in a report.
FILE RULES: write new files ONLY with Bash heredocs (cat > PATH <<'EOF' for the first chunk, cat >> PATH <<'EOF' for later chunks), at most 8 KB per Bash call; write each part file early with its heading and its first paragraph, then extend it in chunks under 8 KB.  Append the literal marker ' # [skip-disk]' to the end of EVERY Bash command line you run (a disk floor interlock holds any command without it); for a heredoc the marker goes at the end of the cat line, after <<'EOF', and the body follows on the next lines.  Use absolute paths in every command; your shell cwd resets between calls.  Scratch files go under ${SCRATCH}; create it once with mkdir -p.  Never commit and never push, in any tree.
HANDOFF RULE: your FIRST tool call writes your handoff file under ${HANDOFF} (three lines: goal, inputs, output paths), and you append one progress line to it after every file write, so a cut-off unit leaves a trail.  If your prompt starts with a RETRY marker, read the handoff file and the part files or report it names first and continue from them; do not restart.
READ RULES: the Read tool caps one window at 12,000 characters: read every source with offset and limit in windows of at most 110 lines (a hook may cap a window lower and print the next window; follow it), and read each named range ONCE.  Do not read the whole design brief (543 lines): read only the line ranges your prompt names, and locate headings first with rg -n '^#' FILE.  Never read MEMORY.md, any INDEX-*.md file, or anything under /Users/oobi/.claude/projects.  Prefer rg -n spans, head and tail over whole-file reads.
PIN RULES: assay is read ONLY at ${ASSAY_PIN} (a worktree pinned detached at eebe37e) and mechanism-lang ONLY at ${MECH_PIN} (a worktree pinned detached at 1e4f371, veil submodule at a7534ce).  Never build there, never run a git command that writes, never install a tool: no brew, sp1up, cabal, rustup, cargo install or opam install; those are USER Stage 0 steps you record.  Never read, build in or touch ${D}/assay, ${D}/mechanism-lang, ${D}/veil, ${D}/kanon or ${D}/attest; they are trees peer sessions own.
TOOLS: rg not grep, sd not sed (a hook denies grep and sed).  fd not find.  python3 -P for any Python.
CAPS: (7 findings max, 56 agents max) bind every unit of this workflow.
Your final text is a return value, not a message: return only the StructuredOutput.`

const PART_SCHEMA = { type: 'object', required: ['ok', 'paths', 'lines', 'summary'], properties: { ok: { type: 'boolean' }, paths: { type: 'array', items: { type: 'string' } }, lines: { type: 'integer', description: 'total lines over the part files written' }, summary: { type: 'string', description: 'at most 60 words' } } }
const COUNT_SCHEMA = { type: 'object', required: ['ok', 'path', 'lines', 'headings', 'dashes', 'pending'], properties: { ok: { type: 'boolean' }, path: { type: 'string' }, lines: { type: 'integer' }, headings: { type: 'integer', description: 'lines that start with two hashes and a space; expect 14' }, dashes: { type: 'integer', description: 'em-dashes plus en-dashes; expect 0' }, pending: { type: 'integer', description: 'occurrences of the word PENDING; expect 0' } } }
const ATTACK_SCHEMA = { type: 'object', required: ['ok', 'path', 'findings'], properties: { ok: { type: 'boolean' }, path: { type: 'string' }, findings: { type: 'array', maxItems: 7, items: { type: 'object', required: ['id', 'section', 'severity', 'claim', 'evidence', 'fix'], properties: { id: { type: 'string', description: 'K1-1, K2-3, K3-2 and so on' }, section: { type: 'string', description: 'the plan section number and heading' }, severity: { type: 'string', enum: ['blocking', 'major', 'minor'] }, claim: { type: 'string', description: 'at most 40 words' }, evidence: { type: 'string', description: 'path:line pairs, at most 40 words' }, fix: { type: 'string', description: 'the exact edit, at most 60 words' } } } } } }
const ADJ_SCHEMA = { type: 'object', required: ['ok', 'path', 'confirmed', 'refuted'], properties: { ok: { type: 'boolean' }, path: { type: 'string' }, confirmed: { type: 'array', maxItems: 7, items: { type: 'object', required: ['id', 'section', 'from', 'to'], properties: { id: { type: 'string' }, section: { type: 'string' }, from: { type: 'string', description: 'the exact plan text to replace, at most 80 words' }, to: { type: 'string', description: 'the exact replacement text, at most 120 words' } } } }, refuted: { type: 'array', items: { type: 'string', description: 'id and a one-line reason' } } } }
const FIX_SCHEMA = { type: 'object', required: ['ok', 'applied', 'skipped', 'lines'], properties: { ok: { type: 'boolean' }, applied: { type: 'integer' }, skipped: { type: 'integer' }, lines: { type: 'integer', description: 'wc -l of the plan after the fixes' }, note: { type: 'string', description: 'at most 40 words' } } }
const CLOSE_SCHEMA = { type: 'object', required: ['plan', 'lines', 'headings', 'dashes', 'pending', 'attacks', 'confirmed', 'fixed', 'unmet'], properties: { plan: { type: 'string' }, lines: { type: 'integer' }, headings: { type: 'integer' }, dashes: { type: 'integer' }, pending: { type: 'integer' }, attacks: { type: 'array', items: { type: 'object', required: ['file', 'findings', 'lines'], properties: { file: { type: 'string' }, findings: { type: 'integer' }, lines: { type: 'integer' } } } }, confirmed: { type: 'integer' }, fixed: { type: 'integer' }, unmet: { type: 'array', items: { type: 'string' } } } }

const skeletonPrompt = () => `You are the skeleton writer of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/skeleton.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
First tool call, one Bash line: mkdir -p ${OUT} ${PARTS} ${HANDOFF} ${SCRATCH} and write the handoff file (goal, inputs, output paths) with a heredoc in the same call.
Read once, in windows: ${VERDICT} lines 115 to 144 (${VERDICT_MAP}); ${BRIEF} lines 31 to 131 (the R0 to R4 pins) and lines 537 to 543 (section 10: the seven OQ rulings and the 2026-09-22 Stage 0 status paragraph at the tail; ${BRIEF_MAP}); ${TPL} lines 1 to 135 (the header and sections 0 to 3; ${TPL_MAP}); ${TPL2} lines 188 to 195 (the dev/dunecho.sh row; ${TPL2_MAP}).
Write four part files by COPY THEN DELTA from TPL sections 0 to 3.  Each part starts with exactly one heading line of the form '## N Title' and carries no other line that starts with '## '.  The plan is dated ${DATE}; part 00 starts with the plan title line '# attest M0 plan' above its '## 0 Bindings' heading, and every other part starts at its own '## ' heading.
${PART('00-bindings.md')} '## 0 Bindings': the seven rulings OQ1 to OQ7 quoted verbatim from BRIEF section 10 as dated bindings of 2026-09-22 (one paragraph per ruling, the OQ id first), then the R0 to R4 pins of BRIEF section 2, each in one paragraph with its brief line span.
${PART('01-scope.md')} '## 1 M0 scope': the verdict M0 milestone line (Stage A carry, B erase, C lower and encode, D emulator and harness, E effects, F freeze) and the M0 gate line, both quoted from VERDICT 115 to 122, then one paragraph per stage that says what the stage delivers and which gate closes it.
${PART('02-stage0.md')} '## 2 Stage 0': the eight USER steps of VERDICT 127 to 137, each marked USER with its number, with the 2026-09-22 status from the BRIEF tail paragraph: step 1 diskfree --apply reclaimed 0K at 21 GiB free (DONE, the floor stays open), the veil submodule DONE at a7534ce, bend NOT installed; open: steps 2, 3, 4, the second half of 5, 6, 7, 8.  Say which open step each M0 stage waits on and which stages start without it.
${PART('03-layout.md')} '## 3 Repository layout': the name attest, the extension .att, the driver verbs of VERDICT 138 to 144, the repository ${D}/attest created at Stage A and not by this plan, dev/dunecho.sh as in TPL2 section 11, the pins kept through M0 (assay pin eebe37e at ${ASSAY_PIN}, mech pin 1e4f371 at ${MECH_PIN} with veil a7534ce), and M0-RATIO informational at M0 so M0 does not wait on Bend 2.  Mirror the TPL section 3 tree listing with the attest names.
Each part at most 90 lines.  Write each part early with its heading and first paragraph, extend it in chunks under 8 KB, and append a progress line to the handoff file after every write.  Return ok, the four paths, the total line count and a summary.
Under 24 tool calls.${STYLE}`

const GROUPS = [
  { key: 'G1', parts: ['04-budgets.md', '05-kernel.md'],
    reads: `${VERDICT} lines 94 to 126 (the synthesized design, the milestones, the trusted lines probe 4 rows; ${VERDICT_MAP}); ${BRIEF} lines 36 to 65 (R0) and 537 to 543 (the rulings; ${BRIEF_MAP}); ${TPL} lines 136 to 162 (sections 4 and 5; ${TPL_MAP}); ${P1} headings by rg -n '^#' then its kernel and trusted-base sections only (at most 60 lines of the 140).`,
    text: `Group G1 of the section writers (7 findings max, 56 agents max): parts 04 and 05.
Write ${PART('04-budgets.md')} '## 4 Trusted base and budgets' by delta from TPL section 4: the OQ4 bounds, kernel at most 4,100 lines at M0 and 4,400 at M1, lower 1,100, encoder 800, harness 100; the probe 4 rows of VERDICT 123 to 126 as the measured baseline with their commands; whole-lib 6,193 lines informational; the TRUSTED-LINES arithmetic row by row so a reader can re-add the sum; the disclosure commands (--axioms, --externs, --passes, TRUSTED-LINES, DENOMINATORS).
Write ${PART('05-kernel.md')} '## 5 The kernel term at M0' by delta from TPL section 5: kanon R0, Lan and Ran along the closed shape grammar are the only type formers (BRIEF 36 to 65); the gates R0-COUNT, R0-AUDIT and R0-DIFF with their commands and pass rules; the assay base with lib/term.ml byte-identical to veil (state the diff command against the veil submodule under ${MECH_PIN} at a7534ce, mark the result VERIFIED if you ran it read-only or BELIEVED); the overlay of about 480 lines (import/ and PRELUDE-CHECKED borrowed from mechanism-lang for the R1 oracle, wc -l it read-only under ${MECH_PIN} and mark VERIFIED or BELIEVED); the flip rule of OQ6 quoted from BRIEF section 10 with the M0 moment it is checked.` },
  { key: 'G2', parts: ['06-emission.md', '07-driver.md'],
    reads: `${VERDICT} lines 94 to 114 and 138 to 144 (${VERDICT_MAP}); ${BRIEF} lines 287 to 330 (4.2 boundary, 4.3 runtime, 4.4 pipeline) and 537 to 543 (OQ1 RV64IM and ELF64, OQ7 erasure; ${BRIEF_MAP}); ${TOOL} in full in windows (284 lines: the SP1 v6.1.0 facts, the syscall codes, the ELF layout, the RV64IM W-form facts, the Bend 2 install row 210); ${TPL} lines 163 to 178 (sections 6 and 7; ${TPL_MAP}).`,
    text: `Group G2 of the section writers (7 findings max, 56 agents max): parts 06 and 07.
Write ${PART('06-emission.md')} '## 6 Emission' by delta from TPL section 6: erase through the evaluator that never unfolds a quantity-0 global per OQ7; lower to a small RV64IM IR (list its instruction set in one table); encode ELF64 for the installed SP1 v6.1.0 executor per OQ1 (the ELF layout rows from TOOL with their TOOL lines); ENC-XCHECK against clang --target=riscv64-unknown-elf -march=rv64im -c on every encoder row; ELF-ACCEPTED on a HALT program; the W-form instruction facts of TOOL (the 32-bit result ops of RV64IM and the sign extension rule) and the syscall codes of TOOL, each with its TOOL line.
Write ${PART('07-driver.md')} '## 7 Driver' by delta from TPL section 7: the verbs attest check, attest build, attest run, and the flags --axioms, --externs, --passes and spec-count, each with its input, its one-line output form and its exit code; the driver never installs and never proves.` },
  { key: 'G3', parts: ['08-gates.md', '09-mutants.md'],
    reads: `${VERDICT} lines 115 to 126 (${VERDICT_MAP}); ${BRIEF} lines 337 to 356 (4.6 gates) and 537 to 543 (the rulings; ${BRIEF_MAP}); ${TPL} lines 179 to 215 (sections 8 and 9; ${TPL_MAP}); ${TPL2} lines 147 to 174 (section 9 gates and denominators; ${TPL2_MAP}); ${TOOL} syscall spans located with rg -n 'UINT256_MUL|HALT|WRITE|COMMIT|0x0001' ${TOOL} then read as short windows.`,
    text: `Group G3 of the section writers (7 findings max, 56 agents max): parts 08 and 09.
Write ${PART('08-gates.md')} '## 8 Gates' by delta from TPL section 8: every gate of the M0 milestone line (VERDICT 115 to 122) as one row with its command, its pass rule and its M0 status, one of binding, informational or OPEN-printing: M0-RATIO rungs 1 to 3 informational with rung 3 at most 2.0, and bend check as the like-for-like row once bend --help is recorded (a Stage 0 step still open); PRELUDE-CHECKED deferred to M1; TRACE-ERASURE per OQ7 with GUARD-TWIN; HOST-ROSTER with Read, Commit and Halt at Stage D and Keccak, Sha256 and U256Mul at Stage E with UINT256_MUL 0x0001011D (cite the TOOL line); EXEC-DIFF on 16 rows; LEAN-TWIN 24 ACCEPT and 12 REFUSE; AXIOMS empty; PROVE-ONCE on the smallest row or a printed OPEN; CYCLE-BUDGET pinned and informational; M0-TIME; DENOMINATORS; PASSES.  End with the gate count and the count per status.
Write ${PART('09-mutants.md')} '## 9 Mutants' by delta from TPL section 9: the F2 seed, the Acc fixture, the R0 smuggling mutant, the encoder mutants and the host-roster mutants, each as a row with the mutation, the gate that must catch it and the expected failure text.` },
  { key: 'G4', parts: ['10-stages.md', '11-house.md', '12-exit.md', '13-next.md'],
    reads: `${TPL} lines 216 to 288 (sections 10 to 13; ${TPL_MAP}); ${TPL2} lines 175 to 223 (sections 10 to 13; ${TPL2_MAP}); ${BRIEF} lines 357 to 377 (house rules) and 537 to 543 (the rulings; ${BRIEF_MAP}); ${VERDICT} lines 115 to 122 and 145 to 155 (${VERDICT_MAP}).`,
    text: `Group G4 of the section writers (7 findings max, 56 agents max): parts 10, 11, 12 and 13.
Write ${PART('10-stages.md')} '## 10 Stages and the build workflow shape' by delta from TPL section 10 and TPL2 section 10: per stage A to F the units with one-line briefs, the tiers (builder Fable xhigh, verifier Fable max, closer Opus medium), the handoff files (every unit writes its handoff file first), the review-kit close per stage, the cap text (7 findings max, 56 agents max) verbatim, and the dead-unit rule (a null builder or verifier retries ONCE on opus with a RETRY marker, then the stage halts and reports; a null finder or closer is reported as unmet).
Write ${PART('11-house.md')} '## 11 House rules' from TPL section 11 and TPL2 section 11: dev/dunecho.sh for every dune verb, no OCaml exceptions (no raise, failwith or assert), total combinators only for indexing and division, kanoncho over raw kanon, never commit and never push, pin a commit never a tree, no em or en dashes, ASD-STE100 prose with two spaces after each sentence period.
Write ${PART('12-exit.md')} '## 12 M0-EXIT stamp, decisions, corrections' by delta from TPL section 12: the M0-EXIT stamp placeholder (the stamp fields with the value 'to be stamped at M0 exit', never the word PENDING), the decision sheet with the seven ratified rulings as dated decisions of 2026-09-22 (OQ1 to OQ7, one row each with the ruling text in one line), and an empty corrections list under a '### Corrections' heading with the single line 'None yet.' that the fixer extends.
Write ${PART('13-next.md')} '## 13 What happens next' by delta from TPL section 13: M1 (rung 4 at most 1.0 binding with a printed OPEN exit, the PRELUDE-CHECKED ratchet, kernel at most 4,400, the overlay merge), then M2 and M3 in one line each from VERDICT 115 to 122.` },
]

const sectionPrompt = (g) => `You are section writer ${g.key} of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/sections-${g.key}.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
You write ONLY these part files: ${g.parts.map(PART).join(' and ')}.  Other writers own the other parts; never touch them.  The skeleton already wrote parts 00 to 03 under ${PARTS}: ls them and read ${PART('00-bindings.md')} in one window so your text agrees with the bindings.
Read once, in windows: ${g.reads}
Each part starts with exactly one heading line of the form '## N Title' and carries no other line that starts with '## '; sub-headings use '### '.
${g.text}
Each part at most 110 lines.  Write each part early with its heading and first paragraph, extend it in chunks under 8 KB, and append a progress line to the handoff file after every write.  Return ok, the paths, the total line count and a summary.
Under 28 tool calls.${STYLE}`

const assemblePrompt = () => `You are the assembler of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/assemble.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
Second tool call, ONE Bash call: ls ${PARTS}, then cat the 14 part files in name order (${PART_NAMES.join(', ')}) into ${PLAN}, then print the counts: wc -l ${PLAN}; rg -c '^## ' ${PLAN} (expect 14); python3 -P -c with the file read as UTF-8 that prints t.count(chr(8212)) plus t.count(chr(8211)) as the dash count (expect 0) and t.count('PENDING') as the pending count (expect 0).  A part file that is missing is an error: list it in the summary and still assemble the rest.
Do not edit any part file and do not edit the plan.  Append one progress line to the handoff file.  Return ok, the plan path and the four counts as integers.
Under 4 tool calls.${STYLE}`

const KS = [
  { n: 1, id: 'K1', name: 'consistency with the rulings and the pins',
    reads: `${BRIEF} lines 31 to 131 (the R0 to R4 pins) and 537 to 543 (the seven OQ rulings and the Stage 0 status; ${BRIEF_MAP}); ${VERDICT} lines 115 to 144 (the milestone line, the trusted lines, the Stage 0 steps, the name; ${VERDICT_MAP}).`,
    text: 'Lens K1 (7 findings max, 56 agents max): attack the plan for any contradiction or silent amendment of OQ1 to OQ7, R0 to R4, the milestone line or the Stage 0 status: a ruling quoted with a changed number or word, a pin softened, a gate moved between binding and informational without the ruling that moves it, a stage added or dropped from the milestone line, a name, extension or driver verb that differs from the verdict, a pin sha or path that differs from the pins.' },
  { n: 2, id: 'K2', name: 'gate and budget feasibility',
    reads: `${VERDICT} lines 115 to 137 (the milestone line, the probe 4 rows, the Stage 0 steps; ${VERDICT_MAP}); ${BRIEF} lines 337 to 356 (4.6 gates) and 537 to 543 (the rulings; ${BRIEF_MAP}); ${TOOL} syscall and ELF spans located with rg -n 'UINT256_MUL|HALT|WRITE|COMMIT|ELF|0x0001' ${TOOL} then read as short windows.`,
    text: 'Lens K2 (7 findings max, 56 agents max): attack the plan for TRUSTED-LINES arithmetic that does not re-add against the probe 4 rows and the OQ4 bounds, a gate of the M0 milestone line that section 8 omits or a section 8 gate the line does not name, a status (binding, informational, OPEN-printing) that a gate cannot hold at M0, a Stage 0 dependency a stage needs that section 2 leaves open without a wait rule, a row count (EXEC-DIFF 16, LEAN-TWIN 24 and 12, HOST-ROSTER six constructors) that differs between sections, a syscall code or ELF fact that differs from TOOL, and a mutant of section 9 that no gate of section 8 catches.' },
  { n: 3, id: 'K3', name: 'executability and house form',
    reads: `${TPL} lines 216 to 288 (sections 10 to 13; ${TPL_MAP}); ${TPL2} lines 175 to 223 (sections 10 to 13; ${TPL2_MAP}); ${BRIEF} lines 357 to 377 (house rules; ${BRIEF_MAP}).`,
    text: 'Lens K3 (7 findings max, 56 agents max): attack the plan for stage order that cannot run (a stage that needs an artifact a later stage makes), a unit brief a builder cannot act on (no inputs, no output path, no gate), a section 10 or section 11 convention of the sibling plans that the plan drops without saying so (dunecho.sh, the tiers, the handoff files, the review-kit close, the cap text, the dead-unit rule, never commit), and house form: ASD-STE100 sentences, zero em or en dashes (count them with python3 -P and chr(8212) and chr(8211)), two spaces after every sentence period (probe with rg -n on the pattern of a period, one space and an uppercase letter, written as the bracket class pattern [.] [A-Z]), the word PENDING absent, never commit stated in section 11.' },
]

const attackPrompt = (k) => `You are adversary ${k.id} (${k.name}) of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/attack-${k.id}.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
First tool call, ONE Bash call: write your handoff file AND the header of your report ${ATTACKS[k.n - 1]} (title, date ${DATE}, lens, the plan path) so the report exists from the first call; extend the report after every finding.
Read once, in windows: the plan ${PLAN} in full (locate its 14 headings with rg -n '^## ' ${PLAN} first, then read it in windows of at most 110 lines); the sources ${k.reads}
${k.text}
Every finding cites the plan section and line and the source path:line that contradicts it; a finding with no source line is BELIEVED and ranks last.  Rank by severity: blocking (the plan cannot run or contradicts a ruling), major (a gate or budget cannot hold), minor (form).  At most 7 findings; fewer is better than padded.  You have read-only file tools: write the report through Bash heredocs only, at most 130 lines: the ranked findings list (id, section, severity, claim, evidence, fix) then a two-line overall verdict.  Return the findings in the StructuredOutput too.
Under 20 tool calls.${STYLE}`

const adjudicatePrompt = (rows) => `You are the adjudicator of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/adjudicate.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
Read once, in windows: the three reports ${rows.map(r => r.a.path).join(', ')} in full (${rows.map(r => r.k.id + ' returned ' + r.a.findings.length + ' findings').join('; ')}); the plan ${PLAN} in windows located with rg -n '^## ' ${PLAN}.
Merge duplicate findings across the reports (same section and same claim) into one, keeping every id.  Re-read every cited plan line and every cited source line (${BRIEF}, ${VERDICT}, ${TOOL}, ${TPL}, ${TPL2}; read only the cited lines, in short windows) before you rule; a finding whose cited line does not say what the finding claims is REFUTED with the reason.  A finding that asks the plan to change a ruling OQ1 to OQ7 or a pin R0 to R4 is REFUTED: rulings bind, and the plan may only quote them.
Return at most 7 CONFIRMED findings, each with the exact plan text to replace (from, verbatim from the plan) and the exact replacement (to), in severity order; the fixer applies them with the Edit tool, so from must match one place in the plan exactly.  List every refuted id with a one-line reason.
You have read-only file tools: write ${ADJ} through Bash heredocs only, at most 120 lines: the confirmed list with from and to blocks, the refuted list, then a two-line verdict.  Append a progress line to the handoff file after the write.
Under 24 tool calls.${STYLE}`

const fixPrompt = (adj) => `You are the fixer of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/fix.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
The adjudicator confirmed ${adj.confirmed.length} findings; the list follows as JSON (id, section, from, to): ${JSON.stringify(adj.confirmed)}
Read ${ADJ} in one window, then locate each section in the plan with rg -n '^## ' ${PLAN} and read only the lines around each from text.  Apply every confirmed edit to ${PLAN} with the Edit tool (old_string = from, new_string = to, each edit under 8 KB); when a from text does not match exactly, rg -n -F for its first six words, read that span, and apply the edit to the text as it stands; when it still does not match, skip it and record the id in the note.  Never edit the part files under ${PARTS} and never edit a report.
Then append a corrections block to section 12 of the plan with the Edit tool: replace the single line 'None yet.' under '### Corrections' with one row per applied edit, dated ${DATE}, of the form 'C-n (${DATE}) id: section: one-line summary of the change'; when no edit was applied, replace it with 'None (${DATE}): the adjudicator confirmed no finding.'  Keep every other line of the plan.
Then one Bash call: wc -l ${PLAN}; rg -c '^## ' ${PLAN} (expect 14); the python3 -P dash and PENDING counts with chr(8212) and chr(8211) (expect 0 and 0).  Append a progress line to the handoff file after every edit.  Return ok, applied, skipped, the line count and a note.
Under 30 tool calls.${STYLE}`

const closePrompt = (rows, adj, fixed) => `You are the closer of the kan-sp1-lang M0 plan workflow (7 findings max, 56 agents max).  Your handoff file is ${HANDOFF}/close.md; write it as your FIRST tool call.  Every Bash command line you run ends with the literal marker ' # [skip-disk]'.
Verify on disk, in ONE Bash call after the handoff write: wc -l ${PLAN}; rg -c '^## ' ${PLAN} (expect 14); python3 -P counts of chr(8212) plus chr(8211) (expect 0) and of the word PENDING (expect 0) in ${PLAN}; wc -l on each of ${ATTACKS.join(', ')} and ${ADJ}; ls ${HANDOFF}.
Attack findings as returned: ${rows.map(r => r.k.id + ' ' + r.a.path + ' ' + r.a.findings.length + ' findings').join('; ') || 'none returned'}.  Adjudicator: ${adj.confirmed.length} confirmed, ${adj.refuted.length} refuted, report ${adj.path}.  Fixer: applied ${fixed.applied}, skipped ${fixed.skipped}, plan at ${fixed.lines} lines.
Return the record: plan, lines, headings, dashes, pending, attacks (one row per report file that exists on disk: file, findings from the list above, lines from wc -l), confirmed, fixed (the applied count), unmet (every expectation that the disk does not meet: a heading count other than 14, a dash count or a PENDING count above 0, a report file missing, a skipped edit above 0, an attack that returned nothing; an empty list when all hold).  Write nothing except the handoff file.  Never commit and never push.
Under 4 tool calls.${STYLE}`

const run = async (prompt, opts) => {
  const first = await agent(prompt, opts)
  if (first) return first
  log('unit ' + opts.label + ' returned null; one retry on opus with the RETRY marker')
  const second = await agent(RETRY + '\n' + prompt, Object.assign({}, opts, { model: 'opus', label: opts.label + '-retry' }))
  if (!second) log('unit ' + opts.label + ' returned null again on opus; no further retry')
  return second || null
}
const halt = (unit) => { log('HALT: unit ' + unit + ' returned nothing after one retry'); return { halted: true, unit } }

phase('Skeleton')
const skeleton = await run(skeletonPrompt(), { label: 'skeleton', phase: 'Skeleton', schema: PART_SCHEMA, agentType: 'wf-builder', model: 'fable', effort: 'xhigh' })
if (!skeleton) return halt('skeleton')
log('skeleton: ok=' + skeleton.ok + ' ' + skeleton.paths.length + ' parts, ' + skeleton.lines + ' lines')

phase('Sections')
const sections = (await pipeline(GROUPS,
  (g) => run(sectionPrompt(g), { label: 'sections-' + g.key, phase: 'Sections', schema: PART_SCHEMA, agentType: 'wf-builder', model: 'fable', effort: 'xhigh' }),
  (r, g) => ({ group: g, result: r || null })
)).filter(Boolean)
const missing = GROUPS.filter(g => !sections.some(s => s.group.key === g.key && s.result))
if (missing.length > 0) return halt('sections-' + missing[0].key)
log('sections: ' + sections.map(s => s.group.key + ' ok=' + s.result.ok + ' ' + s.result.lines + ' lines').join('; '))

phase('Assemble')
const assembled = await run(assemblePrompt(), { label: 'assemble', phase: 'Assemble', schema: COUNT_SCHEMA, agentType: 'wf-mechanical', model: 'opus', effort: 'low' })
if (!assembled) return halt('assemble')
log('assembled: ' + assembled.lines + ' lines, headings=' + assembled.headings + ' dashes=' + assembled.dashes + ' pending=' + assembled.pending)

phase('Attack')
const attackRaw = await parallel(KS.map(k => () => run(attackPrompt(k), { label: 'attack-' + k.id, phase: 'Attack', schema: ATTACK_SCHEMA, agentType: 'wf-verifier', model: 'fable', effort: 'max' })))
const rows = KS.map((k, i) => ({ k, a: attackRaw[i] || null })).filter(x => {
  if (!x.a) log('attack ' + x.k.id + ' returned nothing after one retry; logged and skipped')
  return Boolean(x.a)
})
log('attacks: ' + (rows.map(r => r.k.id + ' ' + r.a.findings.length + ' findings').join('; ') || 'none'))

phase('Adjudicate')
const adj = await run(adjudicatePrompt(rows), { label: 'adjudicate', phase: 'Adjudicate', schema: ADJ_SCHEMA, agentType: 'wf-verifier', model: 'fable', effort: 'max' })
if (!adj) return halt('adjudicate')
log('adjudicated: ' + adj.confirmed.length + ' confirmed, ' + adj.refuted.length + ' refuted')

phase('Fix')
const fixed = await run(fixPrompt(adj), { label: 'fix', phase: 'Fix', schema: FIX_SCHEMA, agentType: 'wf-builder', model: 'fable', effort: 'xhigh' })
if (!fixed) return halt('fix')
log('fixed: applied=' + fixed.applied + ' skipped=' + fixed.skipped + ' lines=' + fixed.lines)

phase('Close')
const closed = await run(closePrompt(rows, adj, fixed), { label: 'close', phase: 'Close', schema: CLOSE_SCHEMA, agentType: 'wf-closer', model: 'opus', effort: 'medium' })
const record = closed || {
  plan: PLAN, lines: fixed.lines, headings: assembled.headings, dashes: assembled.dashes, pending: assembled.pending,
  attacks: rows.map(r => ({ file: r.a.path, findings: r.a.findings.length, lines: 0 })),
  confirmed: adj.confirmed.length, fixed: fixed.applied,
  unmet: ['close unit returned nothing after one retry; the counts above are the fixer and assembler returns, verify the plan on disk by hand'],
}
return { plan: PLAN, record, halted: false }
