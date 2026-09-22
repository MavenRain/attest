## 2 Stage 0

Stage 0 is the user's.  The verdict lists eight USER steps at verdict:129-136 and its numbering binds;  the five-step list of brief section 9 is the older form (brief:543, VERIFIED).  No agent installs anything: no brew, no sp1up, no cabal, no rustup, no cargo install and no opam install, and no agent runs a git command that writes in a pin (tpl:77 and tpl:100 carry the same rule for assay, VERIFIED).  The status of each step on 2026-09-22 comes from the brief tail paragraph at brief:543.

USER step 1: `diskfree --apply` to 30 GiB, 21 GiB at the verdict (verdict:129, VERIFIED).  Status DONE, the floor stays open: the run reclaimed 0K of cold target dirs and 0K of cargo caches, 9.2 GiB of HOT-fresh target dirs under gpt3, gpt5 and gpt7 stay, free space stays at 21 GiB under the 30 GiB floor, and every Bash command keeps the `# [skip-disk]` marker (brief:543, VERIFIED).  `df -g /Users/oobi/Documents` printed 56 GiB available on 2026-09-22 (VERIFIED by that command);  the diskfree figure of 21 GiB is the floor measure and the two tools count differently (BELIEVED, settled by `diskfree` run beside `df -g`).

USER step 2: Bend 2 install by `curl -fsSL https://bend-lang.com/install.sh | sh`, then `bend --help` recorded into dev/bend-cli.txt (verdict:130, VERIFIED).  Status OPEN: `bend` is not on PATH (`zsh: command not found: bend`), Bend 2 is not installed, `bend --help` is not recorded, and the OQ2 like-for-like row is undecided (brief:543, VERIFIED;  `command -v bend` printed nothing on 2026-09-22, VERIFIED).  On PATH: ghc and stack;  not on PATH: cabal, ghcup and bend (brief:543, VERIFIED).

USER step 3: the MODIFIED toolchain present (probe 8), build hello guests for riscv64im and riscv32im, `llvm-readelf -h` on both, execute both (verdict:131, VERIFIED).  Status OPEN (brief:543, VERIFIED).  The riscv64im guest is the one that matches the OQ1 target;  the riscv32im guest is a toolchain probe only (brief:541, VERIFIED).

USER step 4: optional spike (verdict:132, VERIFIED).  Status OPEN and optional (brief:543, VERIFIED).  No M0 stage waits on it.

USER step 5: veil checkout (brief 216-217), then `zsh -f M/dev/dunecho.sh build` and `RUNS=7 zsh -f M/dev/bench.sh SUITE-KERNEL 'M/_build/default/test/main.exe M/vendor/veil/test'` with M the mech pin (verdict:133, VERIFIED).  Status: first half DONE, the veil submodule is checked out in the mech pin at a7534cedeac82d396de8e23058ee6bc990560f65, `git submodule status` shows a clean checkout and vendor/veil/test holds the fixtures (brief:543, VERIFIED;  `git -C /Users/oobi/Documents/kan-sp1-lang-mech-pin submodule status` printed ` a7534cedeac82d396de8e23058ee6bc990560f65 vendor/veil (a7534ce)` on 2026-09-22, VERIFIED).  Second half OPEN: the build and the RUNS=7 bench with absolute paths;  the flip to mechanism-lang needs a median under 211 ms (brief:541 OQ6 and brief:543, VERIFIED).  dev/dunecho.sh and dev/bench.sh exist in the mech pin (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-mech-pin/dev` on 2026-09-22).

USER step 6: ADDED `cargo fetch` of sp1-sdk 6.1.0 (verdict:134, VERIFIED).  Status OPEN (brief:543, VERIFIED).  A cargo fetch writes the cargo home and a harness build writes a target dir;  both run under the open floor, so the user runs them (plan decision, BELIEVED until the user rules on it).

USER step 7: ADDED Stage 0c denominator.sh freeze with DENOMINATORS.sha256 (verdict:135, VERIFIED).  Status OPEN;  it waits on step 2 (brief:543, VERIFIED).  The assay pin holds dev/denominator.sh, dev/denominators.json and dev/DENOMINATORS.sha256 as the recipe to copy (VERIFIED by `ls /Users/oobi/Documents/kan-sp1-lang-assay-pin/dev` on 2026-09-22).

USER step 8: ADDED round 2, write the two A1 F2 fixtures (refl body vs opaque postulate) and diff the erase output on the pin before Stage B (verdict:136, VERIFIED).  Status OPEN (brief:543, VERIFIED).

Open on 2026-09-22, in the verdict's numbering: steps 2, 3, 4, the second half of 5, 6, 7 and 8 (brief:543, VERIFIED).  DONE: step 1 with the floor open, and the first half of step 5 (brief:543, VERIFIED).

What each M0 stage waits on.  The rows below are plan decisions;  each is BELIEVED until the stage's build log records the step it read.

- Stage A waits on no open step.  It starts on the assay pin eebe37e today (brief:541 OQ6, VERIFIED).  The second half of step 5 is the flip trigger;  a median under 211 ms reopens Stage A as a re-carry from the mech pin 1e4f371, and a median at or above 211 ms closes the flip.
- Stage B waits on step 8, the two A1 F2 fixtures and the erase diff on the pin (verdict:136, VERIFIED).  The evaluator and the Acc fixture start without it;  TRACE-ERASURE does not print green before step 8 lands.
- Stage C starts its lowering and its encoder without any open step.  ENC-XCHECK waits on step 3, because the toolchain's hello guests and `llvm-readelf -h` are the reference bytes (BELIEVED, settled by the Stage C brief).  ELF-ACCEPTED on HALT waits on step 6, because the executor call runs through the sp1-sdk harness (BELIEVED, settled by the Stage C brief).
- Stage D starts the emulator twin without any open step.  The harness and EXEC-DIFF wait on step 6 (verdict:134, VERIFIED) and on a harness build the user runs under the open floor.
- Stage E waits on Stage D and on no open step.
- Stage F starts after Stage E.  Its DENOMINATORS row waits on steps 2 and 7 and prints OPEN without them;  M0-RATIO is informational at M0, so M0 does not wait on Bend 2 (brief:541 OQ2 and brief:543, VERIFIED).  PROVE-ONCE waits on step 6.
- Step 4 blocks nothing.
