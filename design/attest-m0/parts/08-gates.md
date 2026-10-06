## 8 Gates

This part is section 8 of the assay M0 plan (tpl:179-203) rewritten for attest, with the leg list of the mechanism-lang plan as the second reference (tpl2:147-173).  dev/gates.sh prints one line per gate under a watchdog tier that is a hang ceiling and never a performance budget, then a MEASURE block, then GATES-OK or GATES-FAIL with exit 1 on any FAIL (tpl2:149, VERIFIED).  Every gate names its command and its printed line (tpl:181, VERIFIED), and every gate has a non-vacuity mutant in part 9.  The gate names come from the M0 milestone line at verdict:117 and the M0 exit line at verdict:118;  the user ratified both on 2026-09-22 (brief:541, VERIFIED).  A gate whose expected line is missing from the run prints `GATES-FAIL missing=NAME`, so an informational gate that prints nothing still fails the run.

### The three statuses

- binding: a FAIL line makes the run print GATES-FAIL and blocks M0-EXIT.
- informational: the line prints INFO with its numbers;  it never fails the run at M0;  the row becomes binding at the milestone the verdict names.
- OPEN-printing: the gate passes or prints OPEN with a reason;  OPEN does not fail the run at M0;  part 12 records every OPEN on the decision sheet.

The status words follow verdict:118 ("PROVE-ONCE done or OPEN") and brief:541 OQ2 ("informational at M0 with rung 3 at most 2.0 and binding at M1 with a printed OPEN exit"), VERIFIED.  Command paths are relative to the repo root of part 3.  `attest` is the driver of part 7;  its verb names in this part are BELIEVED until part 7 fixes them (settle: read part 7).  The harness crate name `attest-harness` is BELIEVED for the same reason.

### Stage A rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| BUILD | `zsh -f dev/dunecho.sh build` | exit 0 with warnings as errors;  a failure ends the run before any other leg (brief:341 and tpl2:151, VERIFIED) | binding |
| CARRY | `zsh dev/carry-check.sh` | `CARRY files=N diff=0 unlisted=0` then `PIN eebe37e`;  every carried file equals `git show eebe37e:PATH` in the assay pin and dev/PIN reads eebe37e (brief:342 and tpl:200-201 for the form, VERIFIED;  the sha from 00-bindings OQ6, VERIFIED) | binding |
| R0-COUNT | `zsh dev/r0-count.sh` | `R0-COUNT formers=2 schema=N shapes=N admitted=N`;  SPEC.md prints two formers and every number is exact at the pin's count, any growth fails (brief:343 and tpl:198, VERIFIED) | binding |
| R0-AUDIT | `zsh dev/r0-audit.sh` | `R0-AUDIT ok`;  the term sum has no third former and every naming in SPEC.md carries its refusal citation (brief:344 and tpl:199, VERIFIED) | binding |
| R0-DIFF | `attest r0-diff` against the kanon tree at 2c2e6e6 | `R0-DIFF vs=2c2e6e6 rows=N diff=0`;  the R0 walk of the carried kernel agrees row for row with kanon 2c2e6e6 (verdict:96 and verdict:117, VERIFIED;  2c2e6e6 is the assay plan's own pin at tpl:200-201, VERIFIED) | binding |
| SUITE-KERNEL | `RUNS=7 zsh -f dev/bench.sh SUITE-KERNEL '_build/default/test/main.exe test'` | `SUITE-KERNEL pass=N fail=0 median_ms=M`;  the carried kernel suite runs green through the attest tree, timed (brief:345 and tpl2:156, VERIFIED;  the bench form from brief:543, VERIFIED) | binding on fail=0;  the median is a MEASURE row |
| AXIOMS | `attest axioms corpus/` | `AXIOMS rows=N axioms=`;  the printed axiom set is empty on every ACCEPT row (verdict:118, VERIFIED);  brief:350 names exactly `Quot.sound`, which is the M2 form at verdict:120, and the ratified milestone line wins (00-bindings, VERIFIED) | binding |
| TRUSTED-LINES | `zsh dev/trusted-lines.sh` | `TRUSTED-LINES kernel=N/4100 lower=N/1100 encoder=N/800 harness=N/100 OK` then `TRUSTED-LINES whole_lib=N/6193 INFO`;  the four OQ4 bounds bind from Stage A and the lower, encoder and harness rows print 0 until their stage (brief:541 OQ4, verdict:126 and 00-bindings, VERIFIED) | binding on the four rows;  the whole-lib row is informational |

### Stage B rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| TRACE-ERASURE | `zsh dev/gates.sh TRACE-ERASURE`, which runs `attest build --erase` on corpus/ and on the opaque twin corpus, then `cmp` per row | `TRACE-ERASURE rows=16 identical=16`;  the ELF built from a row with proof bodies is byte-identical to the ELF built from the same row with every proof replaced by an opaque postulate, both erased through the evaluator that never unfolds a quantity-0 global (brief:541 OQ7 and brief:348, VERIFIED);  16 rows at M0 (verdict:118, VERIFIED);  the seed is the two A1 F2 fixtures and the Acc fixture of part 9 | binding |
| LEAN-TWIN | `zsh dev/lean-twin.sh`, which runs `lake env lean lean/Corpus/ROW.lean` per row | `LEAN-TWIN accept=24/24 refuse=12/12`;  every ACCEPT row elaborates in Lean and in attest, every REFUSE row is refused by both at the same site (verdict:111 and verdict:118, VERIFIED);  a missing `lake` prints FAIL and never SKIP because verdict:118 binds the counts;  `lake` is on PATH today (VERIFIED by `command -v lake` on 2026-09-22) | binding |

### Stage C rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| ENC-XCHECK | `attest enc-xcheck corpus/ref/` | `ENC-XCHECK rows=14 objects=N mismatch=0`;  every instruction the lowering emits matches the 14-row reference encoding plus one rv64 reference object per W form, assembled once and pinned;  no C extension (verdict:107, VERIFIED);  `llvm-readelf` is present under /opt/homebrew/opt/llvm/bin (VERIFIED 2026-10-06);  the 27 reference objects are assembled by clang and pinned under corpus/ref/ with manifest.json (unit C2, 2026-10-06) | binding |
| ELF-ACCEPTED | `cargo run -p attest-harness -- execute corpus/ROW.elf` per row | `ELF-ACCEPTED rows=N exit0=N`;  the SP1 v6.1.0 executor loads every corpus ELF64 and halts with exit 0 (brief:346, VERIFIED), starting with the 96-byte HALT fixture (verdict:107 and dossier:253, VERIFIED);  pc_base is at least 32 and a multiple of 4 (dossier:101, VERIFIED) | binding |

### Stage D rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| EXEC-DIFF | `zsh dev/gates.sh EXEC-DIFF`, which runs the harness `execute` and `attest emu` per row | `EXEC-DIFF rows=16 pubval=16 cycles=16`;  executor and emulator agree on public values and cycle counts for every corpus program (brief:347, VERIFIED) on 16 rows (verdict:118, VERIFIED) | binding |
| HOST-ROSTER | `attest host-roster corpus/ROW.elf` | `HOST-ROSTER ecalls=N roster=3 unknown=0` at Stage D and `roster=6` at Stage E;  the gate scans the t0 immediate before every ecall (verdict:104, VERIFIED) and admits only the roster codes.  Halt = HALT 0x00000000 (dossier:44, VERIFIED).  Commit = WRITE 0x00000002 on fd 13, then 8 COMMIT 0x00000010 and 8 COMMIT_DEFERRED_PROOFS 0x0000001A (dossier:45, dossier:58-59 and dossier:102, VERIFIED).  Read = HINT_LEN then HINT_READ (dossier:103, VERIFIED;  their codes BELIEVED, settle: `rg -n -e HINT_LEN -e HINT_READ /Users/oobi/Documents/kan-sp1-lang-dossier-toolchain.md`).  Keccak = KECCAK_PERMUTE 0x00010109 (dossier:52, VERIFIED).  Sha256 = SHA_COMPRESS 0x00010106 (dossier:49, VERIFIED) with SHA_EXTEND (code BELIEVED, settle: the dossier table).  U256Mul = UINT256_MUL 0x0001011D, the TOOL line `\| UINT256_MUL \| 0x0001011D \| 128 \| 108 \|` (dossier:64, VERIFIED;  brief:541 OQ5, VERIFIED) | binding |
| PUBVAL-DIGEST | `zsh dev/gates.sh PUBVAL-DIGEST` | `PUBVAL-DIGEST rows=N match=N`;  the bytes the guest writes to fd 13 hash by SHA-256 to the 8 COMMIT words, and the harness's public values equal the emulator's (dossier:88 and dossier:102, VERIFIED;  the executor-side digest check is BELIEVED there, settle: crates/core/executor/src/minimal/ecall.rs) | binding |

### Stage E rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| GUARD-TWIN | `zsh dev/gates.sh GUARD-TWIN` | `GUARD-TWIN calls=N twin_agree=N guard_insns=0`;  for every Keccak, Sha256 and U256Mul call in the corpus the emulator's software twin returns the words the executor's precompile returns, and the guard proof on the call erases to zero instructions (brief:541 OQ7 and verdict:117, VERIFIED;  the exact statement of the twin is BELIEVED, settle: verdict:65 and the section 4.6 text that OQ7 replaces) | binding |
| LOWER-REFUSE | `attest lower corpus/refuse/ROW` per row | `LOWER-REFUSE rows=12 refused=12`;  one site per REFUSE row, the lowering refuses Word32 without proof and the pure Host call, and prints the row's expected text (verdict:86, VERIFIED) | binding |

### Stage F rows

| gate | command | printed line and pass rule | M0 status |
| --- | --- | --- | --- |
| CYCLE-BUDGET | `attest cycles corpus/` | `CYCLE-BUDGET row=R cycles=N syscalls=M` per row, pinned in dev/cycles.json;  cycle counts printed and pinned, informational at M0 (brief:349, VERIFIED;  cycles and syscalls per verdict:23, VERIFIED);  binding at M1 (verdict:119, VERIFIED);  a drift against the pin prints `INFO drift` and no FAIL | informational |
| M0-TIME | `RUNS=5 zsh -f dev/bench.sh M0-TIME 'attest build corpus/'` | `M0-TIME median_ms=M bound_ms=B`;  the corpus compiles under a fixed wall-clock bound (brief:351, VERIFIED);  Stage F pins B in dev/denominators.json as the first median times 1.5 (the factor is BELIEVED, settle: the Stage F decision sheet of part 12) | binding from the pin onward |
| M0-RATIO | `zsh dev/ratio.sh` | rung 1 `M0-RATIO rung=1 pass=P ms=N` per pass, the numerator's per-pass split, printed from Stage A (verdict:77, VERIFIED);  rung 2 `M0-RATIO rung=2 denominator_ms=D sha=H`, the Bend 2 denominator plus its hash from USER step 7 (verdict:77, VERIFIED);  rung 3 `M0-RATIO rung=3 ratio=R bound=2.0`, WARN above 2.0 and never FAIL (brief:541 OQ2, VERIFIED);  the like-for-like row runs `bend check` on the matched corpus once `bend --help` is recorded into dev/bend-cli.txt and shows no compile subcommand (brief:541 OQ2, VERIFIED);  `bend` is absent today (VERIFIED by `command -v bend` on 2026-09-22 and brief:543), so rung 2, rung 3 and the like-for-like row print `M0-RATIO rung=N OPEN reason=bend-absent` until USER steps 2 and 7 close | informational;  rungs 1 to 3 |
| DENOMINATORS | `shasum -a 256 -c dev/DENOMINATORS.sha256` | the frozen dev/denominators.json matches its hash before any ratio prints (brief:354 and tpl:203, VERIFIED);  Stage F freezes the rows it has (corpus sha, kernel suite median, cycle pins, M0-TIME bound) with the Bend 2 row written as the word OPEN until USER step 7, and the sha moves with that step (brief:543, VERIFIED) | binding |
| PASSES | `attest build --count-passes corpus/` | `PASSES walks=5 reentries=N`;  the pipeline walks the term exactly five times and prints every re-entry (verdict:75 and verdict:112, VERIFIED) | binding on walks=5;  reentries is a MEASURE row |
| HASHCONS-BENCH | `RUNS=7 zsh -f dev/bench.sh HASHCONS` | `HASHCONS-BENCH fixtures=77 plain_ms=A hashconsed_ms=B`;  the hashconsing bench on the 77 fixtures picks the M1 lever, memoised conversion over hashconsed terms first on proof_free and runtime_ty (verdict:112, VERIFIED) | informational |
| PROVE-ONCE | `cargo run -p attest-harness -- prove corpus/ROW.elf` then `verify`, on the smallest row, once at M0-EXIT only | `PROVE-ONCE row=R proof_bytes=N verify=ok` or `PROVE-ONCE OPEN reason=TEXT`;  the resource guard prints OPEN when free disk is under the 30 GiB floor or the prover is absent (verdict:23 and brief:543, VERIFIED);  the row is the smallest corpus program (brief:355 and verdict:117, VERIFIED) | OPEN-printing |

### Deferred to M1

| gate | M1 form | M0 status |
| --- | --- | --- |
| PRELUDE-CHECKED | a ratchet at M1 (NEVER named, at least 40 percent NAME_AND_TYPE), fail-closed at M2 on NAME_ONLY = 0 and UNMAPPED = 0 (brief:541 OQ3, VERIFIED);  M1 borrows the lean4export importer from the mech pin (00-bindings OQ3, VERIFIED);  the "count mode M0" words of verdict:111 are superseded by OQ3 and the ruling wins (00-bindings, VERIFIED) | not run at M0;  no line prints and the row is outside the M0 count |

### Count

24 M0 gates.  20 binding: BUILD, CARRY, R0-COUNT, R0-AUDIT, R0-DIFF, SUITE-KERNEL, AXIOMS, TRUSTED-LINES, TRACE-ERASURE, LEAN-TWIN, ENC-XCHECK, ELF-ACCEPTED, EXEC-DIFF, HOST-ROSTER, PUBVAL-DIGEST, GUARD-TWIN, LOWER-REFUSE, M0-TIME, DENOMINATORS, PASSES.  3 informational: CYCLE-BUDGET, M0-RATIO, HASHCONS-BENCH.  1 OPEN-printing: PROVE-ONCE.  PRELUDE-CHECKED is deferred and not counted.  The M0 exit reads EXEC-DIFF and TRACE-ERASURE on 16 rows, LEAN-TWIN 24/24 and 12/12, AXIOMS empty and PROVE-ONCE done or OPEN (verdict:118, VERIFIED);  every other binding row must also print PASS because GATES-FAIL blocks the stamp of part 12.
