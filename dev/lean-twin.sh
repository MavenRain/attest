#!/bin/zsh
set -eu
exec python3 -P "${0:A:h}/lean_twin.py" "$@"
