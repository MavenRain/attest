#!/bin/sh
set -eu
: "${ATTEST_BEND_ROOT:?set ATTEST_BEND_ROOT to the pinned Bend 2 source checkout}"
export BEND_NO_TELEMETRY=1
export BEND_LIB="${ATTEST_BEND_CACHE:-${TMPDIR:-/tmp}/attest-bend-cache}"
if test -x "$ATTEST_BEND_ROOT/bin/bend"; then
  exec "$ATTEST_BEND_ROOT/bin/bend" "$@"
fi
exec bun "$ATTEST_BEND_ROOT/bend2/main.ts" "$@"
