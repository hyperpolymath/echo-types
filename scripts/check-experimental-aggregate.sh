#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Every direct echo-additive source must be imported by the CI entrypoint.
# This checks wiring only; it is not a substitute for Agda typechecking.
set -euo pipefail
root="${1:-proofs/agda/experimental/echo-additive}"
aggregate="$root/All.agda"
test -f "$aggregate" || { echo "Missing $aggregate" >&2; exit 1; }
imports="$(mktemp)"
trap 'rm -f "$imports"' EXIT

# Ignore line comments, nested Agda block comments, and string literals.
# A commented-out import must not certify that a module is typechecked.
# Keep whitespace where a comment occurred so adjacent tokens do not join.
awk '
  {
    for (i = 1; i <= length($0); ) {
      pair = substr($0, i, 2)
      char = substr($0, i, 1)
      if (depth > 0) {
        if (pair == "{-") { depth++; i += 2 }
        else if (pair == "-}") { depth--; i += 2 }
        else i++
      } else if (quoted) {
        if (char == "\\") i += 2
        else { if (char == "\"") quoted = 0; i++ }
      } else if (pair == "--") {
        break
      } else if (pair == "{-") {
        depth++; printf " "; i += 2
      } else if (char == "\"") {
        quoted = 1; printf " "; i++
      } else {
        printf "%s", char; i++
      }
    }
    printf "\n"
  }
  END {
    if (depth || quoted) {
      print "Unterminated block comment or string in aggregate" > "/dev/stderr"
      exit 1
    }
  }
' "$aggregate" > "$imports"

fail=0
while IFS= read -r -d '' file; do
  name="${file##*/}"
  name="${name%.agda}"
  [ "$name" = All ] && continue
  if ! grep -Eq "^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+experimental[.]echo-additive[.]${name}([[:space:];(]|$)" "$imports"; then
    echo "Missing aggregate import: $name" >&2
    fail=1
  fi
done < <(find "$root" -maxdepth 1 -type f -name '*.agda' -print0)
if [ "$fail" -ne 0 ]; then exit 1; fi
echo 'Experimental aggregate wiring: OK (not a typecheck)'
