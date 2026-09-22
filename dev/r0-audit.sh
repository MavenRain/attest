#!/bin/zsh
set -eu
exec python3 -P ${0:A:h}/r0-audit.py "${1:-${0:A:h:h}}"
