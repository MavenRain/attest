# Carried source

The original Stage A carried all tracked files in `lib/`, `surface/`, and `test/`, the
licenses, root Dune configuration, and selected development gates from assay
`eebe37e00ecb7fdce739c49f50a6dd49c45022b1`. The wrapper comes from the mechanism
pin recorded in `dev/carry-manifest.json`. No pin is written or built.

The kernel inside assay is kanon
`2c2e6e6831a0b2cf3107fa4aad392606109a2bcf`. Its term, shape, and count sources
have retained SHA-256 checksums under `dev/r0-diff/`. Their source is now
implemented in Bend; the original byte identities remain in the migration record.

`dev/carry-manifest.json` records every carried path, origin, original hash,
and exact adapted hash where applicable. `dev/carry-check.sh` verifies those
hashes, rejects unlisted files in the carried directories, and checks the
originals against pinned Git blobs when the local pins are available.
`ATTEST_ASSAY_PIN` and `ATTEST_MECHANISM_PIN` select other local pin checkouts.
An explicitly configured missing pin fails. Without local pins, the gate
reports manifest verification, so the source of its evidence stays visible.

The following table records the adaptations at the OCaml reference revision.
The Bend migration is recorded separately in `dev/bend-migration.json`, including
removed source dispositions, current Bend hashes and changed development gates.
See [the migration notes](dev/BEND-MIGRATION.md) for the current build and checks.

| path | adaptation |
| --- | --- |
| `dune` | Treat the existing design corpus as data and retain fatal warnings. |
| `lib/check.ml` | Allow erased Prop indices above the family universe and erased constructor fields directly determined by those indices. Retain Type bounds, quantity checks, positivity, and the recursive singleton restriction. |
| `test/dune` | Build the kernel and surface runners, include their fixtures in runtest, and omit EVM executable stanzas. |
| `dev/dunecho.sh` | Rename the optional switch selector to ATTEST_OPAM_SWITCH and explicitly select this tree as the build root, including nested scratch copies. |
| `dev/gates.sh` | Select the attest Stage A, initial erasure, and full LEAN-TWIN gates; keep full TRACE-ERASURE open on Acc. |
| `dev/carry-check.py` | Verify assay and mechanism origins, exact adaptation hashes, and the complete carried file set. |
| `dev/r0-count.sh` | Invoke the count checker that verifies the driver's exit status and the complete fenced block. |
| `dev/r0-audit.py` | Inspect every declared shape constructor and the attest backend directories. |
| `dev/trusted-lines.py` | Apply the four ratified OQ4 buckets and bounds. |
| `dev/house.sh` | Inspect attest backend directories and exclude the unchanged imported design corpus from the prose scan. |
| `dev/house-catchalls.py` | Select attest's CLI dispatch site and backend directories. |
| `dev/house-allow.txt` | Identify the exact argument-rejection arm in attest's string-list parser. |
| `dev/bench.sh` | Resolve Python through PATH instead of an absolute Homebrew path. |

The original OCaml libraries used the names `kanon_kernel` and `kanon_surface`.
The Bend modules now live in `lib/`, `surface/`, and `erase/`; the historical
source hashes remain available for provenance. The public executable is `attest`.
This is the naming adjustment to the illustrative layout in plan section 3.

EVM and Wasm fixture records remain as historical, verbatim test data.
Their backends and executables are not part of attest's Stage A build.
