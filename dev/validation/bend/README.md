# Bend migration validation

The migration uses Bend 2.0.25 at commit
`ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b` and Bun 1.3.11. `index.json`
binds the final sources, JavaScript payload, build files, and retained evidence.

The evidence covers:

- All 20 JavaScript build targets in `build.log`.
- All 16 test programs in `tests.log`. Its original eight-group suite prefix
  matches `original-suite.log` byte for byte.
- The 941-case CLI comparison against `../ocaml-reference.json`, including
  stdout, stderr, and exit status. `differential-initial.json` records 936 exact
  matches and five 900-second timeouts. `differential-retry.json` records only
  those five retries, with a 3,600-second limit and pinned inputs. The initial
  failures remain in the record.
- All 13 Stage A mutations in `../stage-a.json`, all 32 erasure mutations in
  `../erasure-mutations.json`, and all five release checks in
  `../lean-twin-checks.json`.
- The accepted trusted-source ceiling: 5,874 physical lines out of 6,000.

The release runner's first 900-second attempt timed out during Stage A. Its
diagnostic is retained in `release-timeout.log`. The complete five-check run
was repeated with an explicit 3,600-second per-command limit and passed.
The existing trace-erasure frontier is checked by its expected exit status and
specific diagnostic.

`input-audit.json` verifies the mutation records against current inputs. The
Stage A record predates the release timeout option by one helper revision; the
exact historical helper is archived under `snapshots/`. All other Stage A
inputs and every erasure mutation input match the current sources. Captured
logs retain their original bytes, including trailing blank lines.

`closing-review.json` records independent review and isolated checks of the
retry, evidence, and application guards. The reviewed helper sources and guard
witness are retained under `snapshots/`.

To rerun the primary checks after setting up the pinned toolchain:

```sh
make build
make test
python3 -P dev/migration-differential.py compare \
  --root . --driver _build/default/bin/attest.exe \
  --manifest dev/validation/ocaml-reference.json \
  --report .gatework/differential.json --jobs 2 --timeout 3600
python3 -P dev/lean-twin-checks.py --record --timeout 3600
```

Full native compiler generation remains experimental. See
`../../BEND-MIGRATION.md` for the build policy and existing semantic limits.
