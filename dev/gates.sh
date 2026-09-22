#!/bin/zsh
set -eu
if (( $# > 1 )); then
  print -u2 -- 'usage: dev/gates.sh [STAGE-A|ERASURE|TRACE-ERASURE]'
  exit 64
fi
case ${1:-all} in
  STAGE-A) exec python3 -P "${0:A:h}/stage-a-gates.py" ;;
  ERASURE) exec python3 -P "${0:A:h}/erasure-gates.py" ;;
  TRACE-ERASURE) exec python3 -P "${0:A:h}/erasure-gates.py" trace ;;
  all)
    python3 -P "${0:A:h}/stage-a-gates.py"
    exec python3 -P "${0:A:h}/erasure-gates.py"
    ;;
  *) print -u2 -- 'usage: dev/gates.sh [STAGE-A|ERASURE|TRACE-ERASURE]'; exit 64 ;;
esac
