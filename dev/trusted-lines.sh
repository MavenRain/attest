#!/bin/zsh
set -eu
exec python3 -P ${0:A:h}/trusted-lines.py "${1:-${0:A:h:h}}"
