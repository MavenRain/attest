## 7 Driver

bin/attest.ml is bin/assay.ml of the assay pin (221 lines) adapted with the flags --passes, --axioms and --externs and the verb spec-count (verdict:106, VERIFIED);  the two-speed pipeline of tpl:175 stays, check as the fast path and build as the full path.  The source extension is .att and the driver word is attest (verdict:140, VERIFIED).  The verbs are attest check, attest build and attest run;  the flags are --axioms, --externs and --passes;  spec-count is a verb with no file argument (verdict:113, verdict:140, VERIFIED).  The assay driver today parses `assay check [--print|--erased] FILE | axioms FILE | spec-count` (kan-sp1-lang-assay-pin/bin/assay.ml:9, VERIFIED by `rg -n` on 2026-09-22), so the delta moves axioms from a verb to a flag of check, adds --externs and --passes, replaces emit, trace and diff with build and run, and keeps spec-count.  Every verb prints one summary line on stdout, one row form per verb, so gate scripts parse it by the first token;  diagnostics go to stderr with the prefix `attest: <verb>: ` (the assay form at bin/assay.ml:75, VERIFIED).  R3 binds check through build and never a deploy or prove phase (00-bindings.md:33, tpl:175, VERIFIED).  The driver never installs and never proves (section 7.4).

### 7.1 Exit codes

The codes 0, 1, 2 and 64 are the assay codes carried as they stand (bin/assay.ml:3-4, :14, :44, :75, VERIFIED);  codes 3 and 5 are plan decisions, BELIEVED until Stage A lands bin/attest.ml and dev/driver-exit.sh pins every code on one fixture each.  The assay code 3 for a declared and unimplemented verb (bin/assay.ml:199) is not carried:  M0 declares no verb it does not implement, and tpl:175's deferred verbs (deploy, test) have no attest counterpart.

| Code | Meaning | Source |
|---|---|---|
| 0 | success | bin/assay.ml:44, tpl:175 |
| 1 | a parse, elaboration or check error;  the kernel error printed on stderr | bin/assay.ml:44, tpl:175 |
| 2 | an emission error, including the named refusal of a higher-order Pi and a Nat literal at or above 2^64 with no bound | bin/assay.ml:75, tpl:175 |
| 3 | the guest halted with a nonzero exit code or faulted under attest run | verdict:105, verdict:108 |
| 5 | a residual: stack or memory exhaustion of the driver, never proved away by a gate | tpl:177 |
| 64 | a usage error: unknown verb, unknown flag, missing or unreadable file, an output path that exists, a suffix other than .att | bin/assay.ml:4, :14, :28, :83 |

### 7.2 Verbs

| Verb | Input | Output line | Exit |
|---|---|---|---|
| `attest check FILE.att` | one .att source | `CHECK FILE defs=<n> ok` or `CHECK FILE FAIL <line>:<col> <message>` | 0, 1, 64 |
| `attest build FILE.att -o OUT.elf` | one .att source and a new output path | `BUILD FILE elf=OUT bytes=<n> text=<n> data=<n> hosts=<n>` | 0, 1, 2, 64 |
| `attest run OUT.elf [--stdin BYTES]` | one ELF64 and an optional hint byte file | `EXEC cycles=<n> syscalls=<n> pv=<hex> exit=<n>` | 0, 3, 64 |
| `attest spec-count` | SPEC.md of the tree | `R0-COUNT formers=<n> shapes=<n>` | 0, 1 |

attest check runs parse, elaborate and check (brief:318-323, VERIFIED): bidirectional elaboration with first-order pattern unification only, no instance search and no Auto at M0, then the Kan kernel of Stage A.  `defs=<n>` counts the top-level definitions the kernel accepted.  On the first kernel error the driver prints the FAIL row on stdout, the error text on stderr and exits 1;  it never continues past a failed definition.

attest build runs check, then erase, lower and encode of section 6, and writes OUT.elf as the only file;  an existing OUT is a usage error (the assay rule at bin/assay.ml:83, VERIFIED).  `bytes=<n>` is the file size, `text=<n>` and `data=<n>` the p_filesz of the two PT_LOAD segments, and `hosts=<n>` the ecall count that HOST-ROSTER reads back from the t0 immediates (verdict:104, VERIFIED).  The HALT fixture of section 6.3 prints `hosts=1`.

attest run drives the OCaml RV64IM emulator twin emu/rv64im.ml (verdict:106, VERIFIED) and prints the same EXEC line as sp1-exec-harness (verdict:108, VERIFIED), so dev/exec-diff.py compares the two lines and gate EXEC-DIFF passes on equality.  Exit 0 when the guest halts with exit 0;  exit 3 on a nonzero guest exit or a fault, with `exit=fault` on both sides (verdict:108, VERIFIED).  `--stdin BYTES` feeds one hint buffer that Read consumes through HINT_LEN and HINT_READ (tool:103, VERIFIED);  without it Read faults with `exit=fault`.  attest run never spawns the SP1 harness:  the harness is the Rust binary and dev/exec-diff.py runs both sides.

attest spec-count prints the former count from SPEC.md and the shape count, and exits 1 when formers is not 2 or shapes is not 5 (00-bindings.md:27, VERIFIED);  gate R0-COUNT reads the row.

### 7.3 Flags

| Flag | Verb | Input | Output lines | Exit |
|---|---|---|---|---|
| `--axioms` | check | one .att source | `AXIOM <name>` per tracked axiom the file reaches, then `AXIOMS FILE count=<n>` | 0, 1 |
| `--externs` | check | one .att source | `EXTERN <name>` per Host constructor and KPrim accelerator the file reaches, then `EXTERNS FILE count=<n>` | 0, 1 |
| `--passes` | build | one .att source and -o OUT | `PASS <def> walks=<n> reentries=<n>` per definition, then `PASSES FILE defs=<n> walks=<n> max=<n>` | 0, 1, 2 |

--axioms is the R1 disclosure: Quot.sound is a tracked axiom under --axioms (00-bindings.md:29, VERIFIED) and arrives at M2 (verdict:102, VERIFIED), so every M0 fixture with proof bodies prints `count=0`, and the opaque-postulate twin of TRACE-ERASURE prints one AXIOM row per postulate;  the two rows together show that erasure ignored the postulates (brief:541 OQ7, VERIFIED).  The assay form prints one axiom name per line (tpl:175, bin/assay.ml:58, VERIFIED);  the count tail is the delta.

--externs is the R3 disclosure of the trusted base list at verdict:113 (VERIFIED): every name outside the kernel that the emitted ELF depends on, the Host constructors of section 6.1 and the KPrim accelerators of the runtime.  The HALT fixture prints `EXTERN Halt` and `count=1`.  A name outside the OQ5 six is an emission error under build and a printed row under check, never a silent pass.

--passes is the R2 architecture row: the compiler prints the walks per definition, no optimizer pass, direct encoding (00-bindings.md:31, VERIFIED).  The M0 lever is WALKS 5 with reentries (verdict:112, VERIFIED), so `max=<n>` above 5 fails gate PASSES at Stage F (00-bindings.md:31, VERIFIED).  `reentries=<n>` counts the walks a definition re-enters through a thunk;  that column is a plan decision, BELIEVED until Stage C prints it on the corpus fixtures.

### 7.4 What the driver never does

The driver never installs: no sp1up, no cargo prove, no brew, no opam, no cabal, no curl;  every install is a USER Stage 0 step (brief:541-543, VERIFIED).  The driver never proves: no `client.prove` and no `client.verify`;  PROVE-ONCE runs once per milestone exit on the smallest row through dev/prove-once.sh under `/usr/bin/time -l`, skipped with a printed reason under 30 GiB of disk or 16 GiB of memory, and the milestone prints OPEN on that row (verdict:109, VERIFIED).  The driver never spawns clang, lld, llvm-objdump or llvm-readelf;  those are gate tools (tool:220, VERIFIED).  The driver never opens the network and never writes a file other than -o OUT.  The driver never calls sp1-exec-harness;  dev/exec-diff.py does.  Stack and memory exhaustion of the driver stay residual under exit 5 and no gate proves them away (tpl:177, VERIFIED).  bin/attest.ml is outside the four TRUSTED-LINES buckets kernel, lower, encoder and harness (00-bindings.md:17, VERIFIED at the bucket list);  that the driver is not counted is BELIEVED, settle: the row list of dev/trusted-lines.sh at Stage A.
