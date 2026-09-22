## 3 Repository layout

The name is attest, the source extension is .att and the driver is attest with the verbs attest check, attest build, attest run, attest --axioms, attest --externs, attest --passes and attest spec-count, from P1:7, the same word P3 proposed (verdict:140, VERIFIED).  The collision note is information only;  every row of it is BELIEVED because no registry host answered from the verdict's sandbox, and curl on https://crates.io/api/v1/crates/attest, https://pypi.org/pypi/attest/json, https://registry.npmjs.org/attest, https://formulae.brew.sh/api/formula/attest.json and https://api.github.com/search/repositories?q=attest settles it (verdict:141, VERIFIED as the verdict's text).  vouch is the runner-up word if the user prefers a rarer one (verdict:143, VERIFIED).

The repository is /Users/oobi/Documents/attest.  Stage A creates it;  this plan does not.  This unit did not read, build in or touch that path, because peer sessions own it today (the unit's pin rules;  BELIEVED, settled by the unit's call log).  The tree mirrors the assay M0 layout at tpl:104-130 with the attest names.  The EVM directories of the assay pin, abi/, asm/, emit/, evm/, keccak/ and reference/, are not carried (VERIFIED that the pin lists them, by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin` on 2026-09-22;  the carry list itself is BELIEVED until Stage A writes CARRIED.md).  keccak/ is a candidate carry for the Stage E software twin of the Keccak host (BELIEVED, settled at Stage E).

dev/dunecho.sh is the dune wrapper: dunecho for every dune verb and leancho for every lake verb (tpl2:190, VERIFIED), run as `zsh -f dev/dunecho.sh build` (verdict:133 and brief:543, VERIFIED).  The mech pin holds dev/dunecho.sh and the assay pin holds dev/dune.sh (both VERIFIED by `ls` of each pin's dev/ on 2026-09-22).  The attest tree names it dev/dunecho.sh;  the two wrappers are BELIEVED to be one script under two names, settled by `diff` of the two files at Stage A.  No cargo, forge or opam build runs in an agent's hands at any stage of M0 while the floor is open (tpl:100 for the assay form and brief:543 for the floor, VERIFIED).

The pins kept through M0: the assay pin at /Users/oobi/Documents/kan-sp1-lang-assay-pin, a worktree detached at eebe37e (VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-assay-pin rev-parse --short HEAD` on 2026-09-22), and the mech pin at /Users/oobi/Documents/kan-sp1-lang-mech-pin, a worktree detached at 1e4f371 with the veil submodule at a7534ce (VERIFIED by `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin rev-parse --short HEAD` and by `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule status` on 2026-09-22).  Every carry reads the assay pin only;  no unit builds in a pin and no unit runs a git command that writes there.  dev/carry-check.sh compares every carried file against the assay pin and fails on any difference that CARRIED.md does not name (tpl:134 for the assay form, VERIFIED;  the attest form is a Stage A deliverable).

M0-RATIO is informational at M0 with rung 3 at most 2.0, so M0 does not wait on Bend 2 (brief:541 OQ2 and brief:543, VERIFIED).  The DENOMINATORS row of Stage F prints OPEN until USER steps 2 and 7 land (plan decision, BELIEVED until the Stage F log).

The tree at the M0 exit, by copy then delta from tpl:104-130.  Each row names the stage that writes it;  the carried rows are Stage A.

```
attest/
  dune-project             (lang dune 3.24) (name attest)
  LICENSE-MIT LICENSE-APACHE README.md SPEC.md CARRIED.md
  dev/PIN                  eebe37e
  lib/                     library attest_lib, carried verbatim at eebe37e
  surface/                 library attest_surface, carried verbatim at eebe37e
  test/                    the kernel suite, carried verbatim at eebe37e, SUITE-KERNEL
  erase/                   library attest_erase, the opaque-proof evaluator, Stage B
  lower/                   library attest_lower, erased term to RV64IM, Stage C, at most 1,100 lines
  elf/                     library attest_elf, the ELF64 encoder, Stage C, at most 800 lines
  emu/                     library attest_emu, the RV64IM emulator twin, Stage D
  host/                    library attest_host, the Host sum type, Read Commit Halt at Stage D,
                           Keccak Sha256 U256Mul at Stage E
  harness/                 the pinned Rust harness on sp1-sdk 6.1.0, Stage D, at most 100 lines
  bin/attest.ml            driver: check | build | run | spec-count
                           | --axioms | --externs | --passes
  corpus/                  the ACCEPT and REFUSE corpora and the EXEC-DIFF rows, .att files
  fixtures/                the two A1 F2 fixtures and the Acc fixture, Stage B
  twin/                    the Lean twin sources for LEAN-TWIN, Stage B
  dev/                     gates.sh dunecho.sh bench.sh carry-check.sh r0-count.sh r0-audit.sh
                           r0-diff.sh trusted-lines.sh house.sh denominator.sh denominators.json
                           DENOMINATORS.sha256 bend-cli.txt TOOLCHAIN.md
                           M0-BUILD-LOG.md MUTATION-LOG.md
```

The directory names erase/, lower/, elf/, emu/, host/, harness/, fixtures/ and twin/ are plan decisions (BELIEVED until the stage briefs pin them).  The budgets on the lower/, elf/ and harness/ rows are the OQ4 numbers (brief:541, VERIFIED).  The driver verbs are the verdict's (verdict:140, VERIFIED).  The dev/ scripts gates.sh, bench.sh, carry-check.sh, r0-count.sh, r0-audit.sh, trusted-lines.sh, house.sh, denominator.sh, denominators.json and DENOMINATORS.sha256 exist in the assay pin's dev/ to copy from, and dunecho.sh exists in the mech pin's dev/ (VERIFIED by `ls` of each pin's dev/ on 2026-09-22);  r0-diff.sh, bend-cli.txt and TOOLCHAIN.md are new at M0 (BELIEVED, settled by the same `ls`, which lists none of them in the assay pin).

What the carried tree supplies: lib/ at 6,193 lines whole-lib, informational (verdict:125, VERIFIED), and surface/ with its elaborator and grammar (BELIEVED for the assay pin, settled by `wc -l` at Stage A).  attest writes no copy of either.  The kernel row of TRUSTED-LINES prints the carried count against the 4,100 bound from Stage A (brief:541 OQ4, VERIFIED).
