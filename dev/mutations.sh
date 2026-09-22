#!/bin/zsh
set -eu
MUTATIONS_VIA_WRAPPER=1 exec python3 -P "${0:A:h}/mutations.py" "$@"
