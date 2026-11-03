#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Local, uncached Agda checks for the CI roots and the narrowing exhibit.
# Run from any directory after registering the standard-library and
# absolute-zero libraries. Save stdout AND stderr if a receipt is needed.
# Successful checks apply only to the source and dependencies actually used;
# this script does not assign repository-wide Mathesis grades.
set -euo pipefail
cd "$(dirname "$0")/.."

command -v agda >/dev/null || { echo 'ERROR: agda is not installed' >&2; exit 1; }
printf 'Source commit: '; git rev-parse HEAD
printf 'Working tree status (empty means clean):\n'; git status --short
printf 'Agda: '; agda --version
printf 'Library configuration (verify paths and revisions separately):\n'
for f in "${AGDA_DIR:-$HOME/.agda}/libraries" "${AGDA_DIR:-$HOME/.agda}/defaults"; do
  if [ -f "$f" ]; then printf '%s:\n' "$f"; cat "$f"; else printf '%s: absent\n' "$f"; fi
done

sh scripts/kernel-guard.sh
python3 scripts/check-agda-invocations.py
bash scripts/check-experimental-aggregate.sh
bash tools/check-guardrails.sh proofs/agda

# Typecheck the given Agda entrypoint without cached interfaces using the
# standard profile. A failed check stops the script.
check() {
  printf '\nChecking %s\n' "$1"
  agda --ignore-interfaces --safe --without-K --cubical-compatible -i proofs/agda "$1"
}
check proofs/agda/All.agda
check proofs/agda/Smoke.agda
check proofs/agda/characteristic/All.agda
check proofs/agda/examples/All.agda
check proofs/agda/experimental/echo-additive/All.agda
check proofs/agda/NarrowingSmoke.agda
# Cubical is a distinct --safe island: its source options govern its profile.
printf '\nChecking cubical island\n'
agda --ignore-interfaces --safe --cubical -i proofs/agda proofs/agda/EchoImageFactorizationPropCubical.agda
printf '\nAll requested checks exited successfully. Record dependency revisions and output before claiming a receipt.\n'
