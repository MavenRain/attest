#!/bin/zsh
set -eu
exec python3 -P "${0:A:h}/r0-count.py"
