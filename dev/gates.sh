#!/bin/zsh
set -eu
if (( $# > 1 )); then
  print -u2 -- 'usage: dev/gates.sh [STAGE-A|ERASURE|TRACE-ERASURE|LEAN-TWIN|ENC-XCHECK]'
  exit 64
fi
case ${1:-all} in
  STAGE-A) exec python3 -P "${0:A:h}/stage-a-gates.py" ;;
  ERASURE) exec python3 -P "${0:A:h}/erasure-gates.py" ;;
  TRACE-ERASURE) exec python3 -P "${0:A:h}/erasure-gates.py" trace ;;
  LEAN-TWIN) exec zsh -f "${0:A:h}/lean-twin.sh" ;;
  ENC-XCHECK)
    python3 -P "${0:A:h}/enc-xcheck-test.py"
    exec python3 -P "${0:A:h}/enc-xcheck.py"
    ;;
  all)
    python3 -P "${0:A:h}/stage-a-gates.py"
    python3 -P "${0:A:h}/erasure-gates.py"
    zsh -f "${0:A:h}/lean-twin.sh"
    python3 -P "${0:A:h}/enc-xcheck-test.py"
    exec python3 -P "${0:A:h}/enc-xcheck.py"
    ;;
  *) print -u2 -- 'usage: dev/gates.sh [STAGE-A|ERASURE|TRACE-ERASURE|LEAN-TWIN|ENC-XCHECK]'; exit 64 ;;
esac
