#!/bin/zsh
set -eu
root=${1:-${0:A:h:h}}
exec python3 -P "$root/dev/house-bend.py" "$root"
