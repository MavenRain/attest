# Lean checking corpus

`zsh -f dev/lean-twin.sh` checks the 24 ACCEPT and 12 REFUSE pairs listed in
`corpus.json`. The attest sources are in `fixtures/lean-twin/`, and the Lean
sources are in `lean/Corpus/`. The default `dev/gates.sh` run includes this
gate; `zsh -f dev/gates.sh LEAN-TWIN` selects it alone.

The accepted rows cover natural literals and arithmetic, functions,
polymorphism, dependent pairs, collection products and sums, empty
elimination, universes, lets, proof irrelevance, impredicativity, a positive
recursive family, and singleton proposition elimination. Refused rows cover
universe, argument, result, field, branch, application, projection, empty
elimination, positivity, and proposition large-elimination errors. Each
manifest row names its specific topic.

Every source is checked independently with the pinned Lean toolchain.
Accepted Lean rows use term proofs and must produce a complete, empty
`#print axioms` report for every declared definition, theorem, and inductive
type. Attest ACCEPT rows and refusal prefixes must disclose zero axioms.
The gate rejects `sorry`, tactics, new axioms, extra commands, missing
sources, and unexpected manifest counts. It reports failure if a tool is
missing or a compilation times out.

Each REFUSE source ends in one declaration marked `-- REFUSE: NAME`.
The gate first compiles the preceding declarations successfully in both
languages, then requires exit 1 and the row's expected diagnostic from the
complete programs. Every Lean error location must lie inside the marked
declaration. Attest does not report source locations, so the accepted
prefix and single final declaration establish its refusal site.

This is a comparison of checking outcomes in the shared fragment. It is
not a general translation proof or an erasure/runtime comparison. In
particular, `fixtures/erasure/acc.att` remains an explicitly documented
divergence from Lean and is outside this paired corpus. The Acc witness in
`twin/Acc.lean` remains in the separate ERASURE gate.

`zsh -f dev/lean-twin.sh --record` writes `dev/validation/lean-twin.json`
and compiler logs, with source, driver, toolchain, and log hashes.
`python3 -P dev/lean-twin-mutations.py --record` checks thirteen isolated
mutations against passing controls and records their evidence separately.
The mutation harness reuses the built driver and Lean library, changes only
copied corpus sources, and never modifies the working corpus.
