#!/bin/zsh
# dev/house.sh:  the HOUSE gate (SD-G11) as an executable command.
#
# Usage:  zsh ROOT/dev/house.sh [ROOT]
#
# The gate has seven legs, one per house rule of the M0 plan section 11.
# Legs 1, 2, 4, 5, 6 and 7 must print nothing, leg 3 must print exactly
# one line.  The script prints one verdict line per leg, then HOUSE OK
# and exit 0, or HOUSE FAIL and exit 1.
#
# Review round 2026-09-10:  leg 6 (no loop keyword) and leg 7 (no bare
# division) were absent, so two of the five rules had no gate.  Leg 2
# now prints the roots it read, because its rule covers the kernel and
# the new backends only and the backends are empty before Stage B.
#
# SD-D21:  the em-dash leg of the brief is written with the exclusion
# globs '!vendor/**' and '!_build/**'.  ripgrep 15.1.0 on this machine
# does not honor that form:  it still reads vendor/tot, so the leg was
# reported clean while it had never excluded the vendor tree.  The
# forms '!vendor' and '!**/vendor/**' are honored, and this script uses
# both.  The pattern is written as a unicode escape, so that the file
# that checks for the character does not hold one.
set -u

root=${1:-${0:A:h:h}}
fail=0
backends=()
for folder in erase lower elf emu host; do
  if [[ -d $root/$folder ]]; then backends+=($root/$folder); fi
done

emdash=$'\u2014'
newline=$'\n'
pat_house='\braise\b|\bfailwith\b|\bassert\b|\binvalid_arg\b|\bexception\b|List\.nth|List\.hd|List\.tl|Option\.get|Result\.get_ok|\.\(|\.\['
pat_state='\bref\b|\bmutable\b|Array\.|Hashtbl|Buffer\.'
pat_bool='true ->|false ->'
pat_loop='\bfor\b.*\bdo\b|\bwhile\b.*\bdo\b'
pat_div=' / | mod '

# SL round 2026-09-07: dev/*.ml is policed too.  The dev tree also holds
# python and zsh files, so the second call is limited to OCaml sources
# and its output is joined to the first without a blank line.  Legs 1, 3
# and 4 use this helper.  Leg 2 names its own roots, because its rule
# covers the kernel and the encoder only.
# Review round 2026-09-22 (F4):  every leg prints paths relative to the
# tree, so the captured record does not name the checkout it came from
# and a capture from another checkout reproduces byte for byte.
relative () {
  print -r -- "${1//$root\//}"
}

scan () {
  local pattern=$1
  shift
  local main dev
  main=$(rg -n -- $pattern "$@")
  dev=$(rg -n --glob '*.ml' --glob '*.mli' -- $pattern $root/dev)
  relative "${main}${main:+${dev:+$newline}}${dev}"
}

report_empty () {
  local name=$1 out=$2
  if [[ -z $out ]]; then
    print -r -- "HOUSE $name OK"
  else
    print -r -- "HOUSE $name FAIL"
    print -r -- "$out"
    fail=1
  fi
}

# Leg 1: no exception, unapproved catch-all, List.nth or unsafe index.
# SL-D16: allow entries identify a function and exact arm, so line shifts
# cannot authorize another catch-all or invalidate the two ruled sites.
leg1=$(scan $pat_house $root/lib $root/surface $root/bin $root/test $backends)
named=$(python3 -P $root/dev/house-catchalls.py $root 2>&1)
named_code=$?
if [[ $named_code -ne 0 && -z $named ]]; then
  named="named catch-all scan failed with exit=$named_code"
fi
if [[ -n $named ]]; then
  leg1="${leg1}${leg1:+$newline}${named}"
fi
report_empty "no-exception" "$leg1"

# Leg 2: no mutable state in the kernel or new backends.  The roots are
# printed, so a reader sees which trees the rule covered.
leg2_names=(lib)
for folder in erase lower elf emu host; do
  if [[ -d $root/$folder ]]; then leg2_names+=($folder); fi
done
leg2=$(relative "$(rg -n -- $pat_state $root/lib $backends)")
report_empty "no-mutable-state" "$leg2"
print -r -- "HOUSE no-mutable-state roots=${leg2_names[*]}"

# Leg 3:  exactly one catch site in the repository (SD-D14).
leg3=$(scan '\btry\b' $root/lib $root/surface $root/bin $root/test $backends)
leg3_n=$(print -r -- "$leg3" | rg -c -- '.' || true)
if [[ $leg3_n == 1 ]]; then
  print -r -- "HOUSE one-catch-site OK"
  print -r -- "$leg3"
else
  print -r -- "HOUSE one-catch-site FAIL"
  print -r -- "$leg3"
  fail=1
fi

# Leg 4:  no bool match.
leg4=$(scan $pat_bool $root/lib $root/surface $backends $root/test $root/bin)
report_empty "no-bool-match" "$leg4"

# Leg 5: scan implementation and new prose; the imported design is historical.
leg5=$(relative "$(rg -n \
  --glob '!vendor' --glob '!**/vendor/**' \
  --glob '!_build' --glob '!**/_build/**' \
  --glob '!design' --glob '!**/design/**' \
  -e $emdash $root)")
report_empty "no-em-dash" "$leg5"

# Leg 6:  fold and map, never a loop keyword.
leg6=$(scan $pat_loop $root/lib $root/surface $root/bin $root/test $backends)
report_empty "no-loop-keyword" "$leg6"

# Leg 7:  total combinators only, so no bare division and no bare mod.
leg7=$(scan $pat_div $root/lib $root/surface $root/bin $root/test $backends)
report_empty "no-bare-division" "$leg7"

if [[ $fail == 0 ]]; then
  print -r -- "HOUSE OK"
  exit 0
fi
print -r -- "HOUSE FAIL"
exit 1
