#!/bin/zsh
# Without --record, every LEAN-TWIN record must name this repository as its
# root before the check runs (dev/lean-twin-checks.py --roots).
set -eu
dir=${0:A:h}
if (( ${argv[(Ie)--record]} == 0 )); then
  python3 -P "$dir/lean-twin-checks.py" --roots
fi
exec python3 -P "$dir/lean_twin.py" "$@"
