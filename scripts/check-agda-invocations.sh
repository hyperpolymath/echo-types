#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Static lint for direct, single-line agda commands; not a shell parser/typecheck.
set -eu
if [ "$#" -eq 0 ]; then
  # verify.sh delegates to tools/check-audit.sh. That runner constructs argv
  # arrays and is verified by execution, not this direct-command-only lint.
  set -- .github/workflows/agda.yml scripts/check-grade3.sh Justfile
fi
for file do
  test -r "$file" || { printf '%s: unreadable input\n' "$file" >&2; exit 1; }
done
awk '
function finish() {
  if (FILENAME != "" && count == 0) {
    print FILENAME ": no direct Agda proof command found" > "/dev/stderr"
    failed = 1
  }
}
FNR == 1 {
  if (NR > 1 && count == 0) {
    print previous ": no direct Agda proof command found" > "/dev/stderr"
    failed = 1
  }
  count = 0; previous = FILENAME
}
{
  line = $0
  sub(/^[[:space:]]*(run:[[:space:]]*)?/, "", line)
  sub(/^@/, "", line)
  if (line !~ /^agda[[:space:]]+/) next
  sub(/^agda[[:space:]]+/, "", line)
  sub(/[[:space:]]*#.*/, "", line)
  sub(/[[:space:]]+$/, "", line)
  if (line == "--version") next
  count++
  for (key in arg) delete arg[key]
  n = split(line, fields, /[[:space:]]+/)
  for (i = 1; i <= n; i++) arg[fields[i]] = 1
  cubical = ("proofs/agda/EchoImageFactorizationPropCubical.agda" in arg)
  missing = !("--safe" in arg) || (cubical ? !("--cubical" in arg) : (!("--without-K" in arg) || !("--cubical-compatible" in arg)))
  forbidden = (!cubical && ("--cubical" in arg))
  split("--allow-unsolved-metas --with-K --no-without-K --type-in-type --no-termination-check --no-positivity-check", denied, " ")
  for (i in denied) if (denied[i] in arg) forbidden = 1
  if (missing || forbidden) {
    printf "%s:%d: invalid proof profile (missing=%d, forbidden=%d)\n", FILENAME, FNR, missing, forbidden > "/dev/stderr"
    failed = 1
  }
}
END { finish(); exit failed }
' "$@"
printf '%s\n' 'Agda invocation lint: OK (static only; no proof was checked)'
