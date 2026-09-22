## 9 Mutants

This part is section 9 of the assay M0 plan (tpl:205-214) rewritten for attest.  One row per mutant in dev/MUTATION-LOG.md, each with the stage, the mutation, the gate that must catch it and the expected failure text (tpl:207, VERIFIED for the form).  A mutant is a one-site edit on a scratch copy of the tree;  the gate runs on the copy, the log records the printed FAIL line, and the copy is discarded.  A gate whose mutant does not fail is vacuous and blocks its stage (tpl:181, VERIFIED).  The erasure rule of the assay plan carries over: an erasure mutant changes the SHAPE of a proof term or the evaluator, never a second proof of a one-constructor family (tpl:195, VERIFIED).  Every expected failure text is the printed line of part 8 with the failing numbers;  the exact spelling settles when dev/gates.sh exists at Stage A (BELIEVED until then, settle: run the mutant on the Stage A tree).  N stands for the count the pinned run prints.

### Stage A

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| PIN | change one character of dev/PIN | CARRY | `PIN eebe37f FAIL expected=eebe37e` (tpl:209, VERIFIED for the form;  the assay pin's own dev/PIN reads 2c2e6e6, VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin show HEAD:dev/PIN` on 2026-09-22, so attest's dev/PIN carries eebe37e and its CARRIED.md names 2c2e6e6 as the kanon inside it) |
| CARRY | edit one carried line outside the one edit CARRIED.md lists | CARRY | `CARRY files=N diff=1 unlisted=0 FAIL path=PATH` (tpl:209, VERIFIED for the form) |
| BUILD | add one unused binding to a carried module | BUILD | the dune error text with `Error (warning 26 [unused-var])`, then the run stops (tpl2:151, VERIFIED for the stop rule) |
| SUITE-KERNEL | flip the expected verdict of one carried kernel test | SUITE-KERNEL | `SUITE-KERNEL pass=N-1 fail=1 median_ms=M FAIL` (brief:345) |
| R0 smuggling, former | add a third constructor to the term sum, a KHost former that carries an effect as a term, and route it through the checker | R0-COUNT | `R0-COUNT formers=3 expected=2 FAIL` (brief:343 and tpl:198, VERIFIED for the rule) |
| R0 smuggling, shape | keep two formers and add the effect as a new shape name inside the rules dispatch with no line in SPEC.md | R0-AUDIT | `R0-AUDIT FAIL name=KHost site=PATH:LINE citation=none` (brief:344 and tpl:199, VERIFIED for the rule) |
| R0 walk order | swap two children in the R0 walk | R0-DIFF | `R0-DIFF vs=2c2e6e6 rows=N diff=1 FAIL row=R` (verdict:96) |
| axiom | add `axiom smuggled : False` to one ACCEPT row | AXIOMS | `AXIOMS rows=N axioms=smuggled FAIL row=R` (verdict:118) |
| kernel growth | append 200 non-blank lines to the kernel | TRUSTED-LINES | `TRUSTED-LINES kernel=N+200/4100 FAIL` with N+200 above 4,100 (brief:541 OQ4) |

### Stage B: the F2 seed and the Acc fixture

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| F2 seed, evaluator | delete the quantity guard at its one site so the evaluator unfolds a quantity-0 global | TRACE-ERASURE | `TRACE-ERASURE rows=16 identical=14 FAIL row=f2-a first_diff=OFFSET` on the two A1 F2 fixtures of USER step 8 (parts/01-scope.md:17 and parts/03-layout.md:33, VERIFIED by rg on 2026-09-22, both citing verdict:136) |
| F2 seed, shape | replace the proof body of fixture f2-a by a proof of a different shape, an extra case split, and keep the guard | TRACE-ERASURE | no FAIL, `TRACE-ERASURE rows=16 identical=16`;  this control row proves the ELF does not move when only the proof shape moves (tpl:195, VERIFIED for the rule);  a FAIL here is a Stage B defect, not a caught mutant |
| Acc fixture, evaluator | mark Acc.rec as quantity 1 in the mutant evaluator so it unfolds the accessibility proof of a well-founded recursion | TRACE-ERASURE | `TRACE-ERASURE rows=16 identical=15 FAIL row=acc unfolded=Acc.rec`, or `TRACE-ERASURE row=acc WATCHDOG FAIL` when the opaque twin has no body to unfold and the mutant evaluator stalls (tpl2:149 for the watchdog, VERIFIED) |
| Acc fixture, twin | move the Acc row from corpus/accept/ to corpus/refuse/ with no other change | LEAN-TWIN | `LEAN-TWIN accept=23/24 refuse=12/13 FAIL row=acc lean=accepted attest=accepted` (verdict:111) |
| LEAN-TWIN | move one REFUSE row into corpus/accept/ with no other change | LEAN-TWIN | `LEAN-TWIN accept=24/25 refuse=11/12 FAIL row=R lean=refused attest=refused` (verdict:118) |

### Stage C: the encoder mutants

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| funct3 | set bit 12 in the `addi` encoder | ENC-XCHECK | `ENC-XCHECK rows=14 mismatch=1 FAIL insn=addi ours=0x00001513 ref=0x00000513` (the reference word is `13 05 00 00` at dossier:253, VERIFIED) |
| immediate field | place the I-type immediate at bit 19 instead of bit 20 | ENC-XCHECK | `ENC-XCHECK rows=14 mismatch=1 FAIL insn=addi-neg ours=HEX ref=0xfff50513` (the reference is `addi a0, x0, -1`, BELIEVED for the hex, settle: the 14-row reference of verdict:107) |
| register fields | swap rs1 and rs2 in the R-type encoder | ENC-XCHECK | `ENC-XCHECK rows=14 mismatch=1 FAIL insn=add ours=HEX ref=HEX` (verdict:107) |
| compressed | emit a 16-bit `c.addi` for a small immediate | ENC-XCHECK | `ENC-XCHECK FAIL insn=c.addi width=16 allowed=32` (no C extension, verdict:107, VERIFIED) |
| W form object | drop the `addiw` reference object | ENC-XCHECK | `ENC-XCHECK rows=14 objects=N-1 FAIL missing=addiw` (one rv64 object per W form, verdict:107, VERIFIED) |
| entry alignment | set e_entry to 0x78000002 | ELF-ACCEPTED | `ELF-ACCEPTED rows=N exit0=N-1 FAIL row=halt96 error=TEXT`;  the executor rejects a pc_base that is not a multiple of 4 (dossier:101, VERIFIED;  the executor's text is BELIEVED, settle: run the mutant through the harness) |
| halt code | lower Halt with a0 = 1 | ELF-ACCEPTED | `ELF-ACCEPTED rows=N exit0=N-1 FAIL row=halt96 exit=1` (brief:346) |

### Stage D and Stage E: the host-roster mutants

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| roster D | lower Keccak at Stage D, t0 = 0x00010109 before an ecall | HOST-ROSTER | `HOST-ROSTER ecalls=N roster=3 unknown=1 FAIL t0=0x00010109` (KECCAK_PERMUTE at dossier:52, VERIFIED) |
| roster E | lower U256Mul with t0 = 0x00010131, UINT256_MUL_CARRY, instead of 0x0001011D | HOST-ROSTER | `HOST-ROSTER ecalls=N roster=6 unknown=1 FAIL t0=0x00010131` (dossier:84 and dossier:64, VERIFIED) |
| roster name | add Bn254 as a seventh Host constructor | HOST-ROSTER | `HOST-ROSTER roster=7 expected=6 FAIL` (00-bindings OQ5: no M0 file names Bn254 or Secp256k1, VERIFIED) |
| fd | write the public values to fd 12 | PUBVAL-DIGEST | `PUBVAL-DIGEST rows=N match=N-1 FAIL row=R fd=12 expected=13` (FD_PUBLIC_VALUES = 13 at dossier:88, VERIFIED) |
| commit count | emit 7 COMMIT ecalls | PUBVAL-DIGEST | `PUBVAL-DIGEST rows=N match=N-1 FAIL row=R commits=7 expected=8` (dossier:102, VERIFIED) |
| digest | commit the SHA-256 words in big-endian order | PUBVAL-DIGEST | `PUBVAL-DIGEST rows=N match=N-1 FAIL row=R word=0` (the entrypoint commits 32-bit words, dossier:102, VERIFIED;  the byte order is BELIEVED, settle: halt.rs:20-60) |
| cycles | insert one `nop` in the emulator's Halt path only | EXEC-DIFF | `EXEC-DIFF rows=16 pubval=16 cycles=15 FAIL row=R exec=N emu=N+1` (brief:347) |
| twin | make the U256Mul software twin return the low 128 bits | GUARD-TWIN | `GUARD-TWIN calls=N twin_agree=N-1 FAIL call=u256mul row=R` (brief:541 OQ7) |
| guard | let the lowering emit a runtime bounds check for a guard that carries a proof | GUARD-TWIN | `GUARD-TWIN calls=N twin_agree=N guard_insns=3 FAIL row=R` (brief:541 OQ7) |
| refuse | delete the Word32 proof check in the lowering | LOWER-REFUSE | `LOWER-REFUSE rows=12 refused=11 FAIL row=word32-no-proof accepted` (verdict:86) |
| pure host | let a Host call type as a pure term | LOWER-REFUSE | `LOWER-REFUSE rows=12 refused=11 FAIL row=pure-host accepted` (verdict:86) |

### Stage F

| mutant | mutation | gate | expected failure text |
| --- | --- | --- | --- |
| denominators | edit one byte of dev/denominators.json after the freeze | DENOMINATORS | `dev/denominators.json: FAILED` from shasum, then `DENOMINATORS FAIL` (tpl:214, VERIFIED for the form) |
| passes | add a sixth walk | PASSES | `PASSES walks=6 reentries=N FAIL expected=5` (verdict:75) |
| cycle pin | edit one pinned count in dev/cycles.json | CYCLE-BUDGET | `CYCLE-BUDGET row=R cycles=N pinned=N+1 INFO drift` and no FAIL at M0;  the same mutant prints FAIL at M1 (verdict:119) |
| time bound | halve bound_ms in dev/denominators.json and refreeze the sha | M0-TIME | `M0-TIME median_ms=M bound_ms=B/2 FAIL` (brief:351) |
| missing line | delete the M0-RATIO rung 1 print from dev/ratio.sh | the run itself | `GATES-FAIL missing=M0-RATIO` (part 8, the missing-line rule) |

### Count

37 rows: 9 at Stage A, 5 at Stage B, 7 at Stage C, 11 at Stage D and E, 5 at Stage F.  36 must print FAIL and one control row (F2 seed, shape) must not.  Every binding gate of part 8 has at least one row here;  the informational gates CYCLE-BUDGET and M0-RATIO carry a print-shape row each, and HASHCONS-BENCH and PROVE-ONCE carry none because an OPEN or INFO line is their pass form (part 8, the three statuses).  The R0 smuggling pair is the row the ratified pins protect: two formers at R0 (brief:343-344, VERIFIED) and no third former by name or by shape.
