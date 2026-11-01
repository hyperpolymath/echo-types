#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Every direct echo-additive source must be imported by the CI entrypoint.
# This checks wiring only; it is not a substitute for Agda typechecking.
set -euo pipefail
root="${1:-proofs/agda/experimental/echo-additive}"
aggregate="$root/All.agda"
test -f "$aggregate" || { echo "Missing $aggregate" >&2; exit 1; }
fail=0
while IFS= read -r -d '' file; do
  name="${file##*/}"
  name="${name%.agda}"
  [ "$name" = All ] && continue
  if ! grep -Eq "^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+experimental[.]echo-additive[.]${name}([[:space:];(]|$)" "$aggregate"; then
    echo "Missing aggregate import: $name" >&2
    fail=1
  fi
done < <(find "$root" -maxdepth 1 -type f -name '*.agda' -print0)
if [ "$fail" -ne 0 ]; then exit 1; fi
echo 'Experimental aggregate wiring: OK (not a typecheck)'
