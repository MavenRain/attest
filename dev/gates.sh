#!/bin/zsh
set -eu
if (( $# != 0 )); then
  print -u2 -- 'usage: dev/gates.sh'
  exit 64
fi
exec python3 -P "${0:A:h}/stage-a-gates.py"
