## 11 House rules

House rules for every file an agent writes at M0, by delta from tpl:235-247 and tpl2:188-195 with the brief's section 5 (brief:357-377, VERIFIED).  dev/house.sh checks the OCaml rules and the verifier of every stage scans for each banned form with rg;  a hit is a finding (tpl2:190, VERIFIED as the form;  the attest script is a Stage A deliverable, part 3).

### OCaml

- Every dune verb runs through dev/dunecho.sh, as `zsh -f dev/dunecho.sh build` and `zsh -f dev/dunecho.sh test` (part 3, tpl2:190 and brief:373-374, VERIFIED).  No agent calls raw dune.
- No exceptions.  No `raise`, no `failwith`, no `assert`.  Every partial step returns a `result` (tpl:239 and brief:359, VERIFIED).
- Total combinators only for indexing and division.  No `List.nth`, no `arr.(i)`, no bare `/` or `mod` (tpl:240 and brief:361, VERIFIED).
- Option and Result through combinators, never a `match` on them (brief:359-360, VERIFIED).
- Exhaustive matches.  No `_` arm, so a new constructor of the term sum or of Host is a compile error in every pass (tpl:241, VERIFIED).
- No `match` on a bool.  Write if and else (tpl:242, VERIFIED).
- `match ()` with guards over an else-if chain of three or more (brief:362, VERIFIED).
- Fold and map, never a loop keyword, and no mutation of vectors (tpl:243 and brief:361-362, VERIFIED).

### Rust, the harness only

The harness under harness/ is the one Rust artifact at M0 (part 3).  Newtypes and sum types, no `unwrap`, `expect`, `panic` or `unsafe`, hand-rolled `Error` enums, MIT OR Apache-2.0 (brief:363-365, VERIFIED).  Every cargo verb runs through cargocho, OOM-safe at `-j 2` and one crate at a time (brief:373-374, VERIFIED), and only when the disk floor allows a build (brief:375-376 and brief:543, VERIFIED);  the Stage D brief records the `cargo fetch` of USER step 6 as the user's step.

### Lean, the twin

The Lean twin under twin/ uses kan-tactics only, no exceptions, and is a reusable lakefile dependency;  every lake verb runs through leancho (brief:366-367 and tpl2:190, VERIFIED).

### Drivers and pins

- kanoncho over raw kanon (brief:373-374, VERIFIED).  At M0 the carried kernel suite runs through the dune wrapper, and no agent calls a raw kanon or attest binary outside dev/gates.sh (plan decision, BELIEVED until the Stage A brief pins it).
- Pin a commit, never a tree.  Every probe of assay or mechanism-lang reads the detached worktree at /Users/oobi/Documents/kan-sp1-lang-assay-pin (eebe37e) or /Users/oobi/Documents/kan-sp1-lang-mech-pin (1e4f371, veil at a7534ce), never a main tree (brief:372 and part 3, VERIFIED).  No unit builds in a pin and no unit runs a git command that writes there.
- Never install a tool, never call brew, sp1up, cabal, rustup, cargo install or opam install, never start a daemon;  those are USER Stage 0 steps that the plan records (tpl:247 and brief:543, VERIFIED).

### Git

Never commit and never push, in any tree.  Every closer stages the tree and prints the commit command with `git commit -s` for DCO;  the user runs it (brief:368-369 and tpl:218, VERIFIED).

### Prose

- ASD-STE100 for repo-facing text: short declarative sentences, one instruction per sentence, active voice, two spaces after each sentence period and after each semicolon (tpl:247 and brief:370, VERIFIED).
- No em dashes and no en dashes, in files, in prompts and in return text;  ASCII only (brief:370, VERIFIED).
- No AI prose tells (brief:370, VERIFIED).
- An unstamped field reads "to be stamped at M0 exit";  no other placeholder word appears in a plan, a part or a report (the task text of this plan's writers, VERIFIED as that text).

### Caps and gates

- Every agent prompt carries "(7 findings max, 56 agents max)" (brief:371, VERIFIED).
- Every gate has a non-vacuity mutant in section 9 (tpl:247, VERIFIED as the form).
- Denominators are frozen as hashed artifacts before any ratio binds (tpl:247 and brief:87-93, VERIFIED);  at M0 no ratio binds (brief:541 OQ2, VERIFIED).
