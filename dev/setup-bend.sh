#!/bin/sh
set -eu
attest_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
attest_bend_dir=${ATTEST_BEND_ROOT:-"$attest_root/_tools/bend"}
attest_bend_pin=$(python3 -P -c 'import json,sys; print(json.load(open(sys.argv[1]))["revision"])' "$attest_root/dev/bend-toolchain.json")
attest_bend_repo=$(python3 -P -c 'import json,sys; print(json.load(open(sys.argv[1]))["repository"])' "$attest_root/dev/bend-toolchain.json")
if test -e "$attest_bend_dir"; then
  test "$(git -C "$attest_bend_dir" rev-parse HEAD)" = "$attest_bend_pin"
else
  git clone "$attest_bend_repo" "$attest_bend_dir"
  git -C "$attest_bend_dir" checkout --detach "$attest_bend_pin"
fi
printf '%s\n' "Bend ready at $attest_bend_dir"
