#!/bin/zsh
set -eu
if (( $# > 1 )); then
  print -u2 -- 'usage: dev/gates.sh [STAGE-A|ERASURE|TRACE-ERASURE|LEAN-TWIN]'
  exit 64
fi
case ${1:-all} in
  STAGE-A) exec python3 -P "${0:A:h}/stage-a-gates.py" ;;
  ERASURE) exec python3 -P "${0:A:h}/erasure-gates.py" ;;
  TRACE-ERASURE) exec python3 -P "${0:A:h}/erasure-gates.py" trace ;;
  LEAN-TWIN) exec zsh -f "${0:A:h}/lean-twin.sh" ;;
  all)
    python3 -P "${0:A:h}/stage-a-gates.py"
    python3 -P "${0:A:h}/erasure-gates.py"
    exec zsh -f "${0:A:h}/lean-twin.sh"
    ;;
  *) print -u2 -- 'usage: dev/gates.sh [STAGE-A|ERASURE|TRACE-ERASURE|LEAN-TWIN]'; exit 64 ;;
esac
