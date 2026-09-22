# Carried source

Stage A carries all tracked files in `lib/`, `surface/`, and `test/`, the
licenses, root Dune configuration, and selected development gates from assay
`eebe37e00ecb7fdce739c49f50a6dd49c45022b1`. The wrapper comes from the mechanism
pin recorded in `dev/carry-manifest.json`. No pin is written or built.

The kernel inside assay is kanon
`2c2e6e6831a0b2cf3107fa4aad392606109a2bcf`. Its term, shape, and count sources
are separately retained under `dev/r0-diff/` with SHA-256 checksums.

`dev/carry-manifest.json` records every carried path, origin, original hash,
and exact adapted hash where applicable. `dev/carry-check.sh` verifies those
hashes, rejects unlisted files in the carried directories, and checks the
originals against pinned Git blobs when the local pins are available.
`ATTEST_ASSAY_PIN` and `ATTEST_MECHANISM_PIN` select other local pin checkouts.
An explicitly configured missing pin fails. Without local pins, the gate
reports manifest verification, so the source of its evidence stays visible.

Only the following carried files are adapted:

| path | adaptation |
| --- | --- |
| `dune` | Treat the existing design corpus as data and retain fatal warnings. |
| `test/dune` | Build the kernel and surface runners, include their fixtures in runtest, and omit EVM executable stanzas. |
| `dev/dunecho.sh` | Rename the optional switch selector to ATTEST_OPAM_SWITCH and explicitly select this tree as the build root, including nested scratch copies. |
| `dev/gates.sh` | Select the attest Stage A runner. |
| `dev/carry-check.py` | Verify assay and mechanism origins, exact adaptation hashes, and the complete carried file set. |
| `dev/r0-count.sh` | Invoke the count checker that verifies the driver's exit status and the complete fenced block. |
| `dev/r0-audit.py` | Inspect every declared shape constructor and the attest backend directories. |
| `dev/trusted-lines.py` | Apply the four ratified OQ4 buckets and bounds. |
| `dev/house.sh` | Inspect attest backend directories and exclude the unchanged imported design corpus from the prose scan. |
| `dev/house-catchalls.py` | Select attest's CLI dispatch site and backend directories. |
| `dev/house-allow.txt` | Identify the exact argument-rejection arm in attest's string-list parser. |
| `dev/bench.sh` | Resolve Python through PATH instead of an absolute Homebrew path. |

The internal libraries keep the upstream names `kanon_kernel` and
`kanon_surface`. This preserves every OCaml source in the carry byte for byte,
including module references. The package and public executable are `attest`.
This is the naming adjustment to the illustrative layout in plan section 3.

EVM and Wasm fixture records remain as historical, verbatim test data.
Their backends and executables are not part of attest's Stage A build.
