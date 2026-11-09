#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Check the Rocq and Lean recheck legs and fail on any axiom.
# Usage: scripts/check-recheck.sh [rocq|lean|all]. Needs coqc on PATH and
# LEAN set to the lean binary (scripts/setup-recheck.sh provides both).
# Save stdout and stderr if a receipt is needed.
set -euo pipefail
cd "$(dirname "$0")/.."
want="${1:-all}"
printf 'Source commit: %s\n' "$(git rev-parse HEAD)"

if [ "$want" = all ] || [ "$want" = rocq ]; then
  coqc --version
  out="$(cd proofs/rocq && coqc -q EchoSearchExample.v 2>&1)"
  printf '%s\n' "$out"
  # Every Print Assumptions must close; any axiom fails the leg.
  n_closed="$(printf '%s\n' "$out" | grep -c '^Closed under the global context$' || true)"
  n_print="$(grep -c '^Print Assumptions' proofs/rocq/EchoSearchExample.v)"
  if [ "$n_closed" -ne "$n_print" ]; then
    printf 'Rocq leg: %s of %s Print Assumptions closed\n' "$n_closed" "$n_print" >&2
    exit 1
  fi
  rm -f proofs/rocq/*.vo proofs/rocq/*.vok proofs/rocq/*.vos proofs/rocq/*.glob proofs/rocq/.*.aux
  printf 'Rocq leg: OK (%s headlines, no axioms)\n' "$n_print"
fi

if [ "$want" = all ] || [ "$want" = lean ]; then
  lean="${LEAN:?set LEAN to the lean binary}"
  "$lean" --version
  out="$("$lean" proofs/lean4/EchoSearchExample.lean 2>&1)"
  printf '%s\n' "$out"
  if printf '%s\n' "$out" | grep -qE 'error|warning|sorry|depends on axioms'; then
    printf 'Lean leg: error, warning, sorry or axiom reported\n' >&2
    exit 1
  fi
  n_free="$(printf '%s\n' "$out" | grep -c 'does not depend on any axioms' || true)"
  n_print="$(grep -c '^#print axioms' proofs/lean4/EchoSearchExample.lean)"
  if [ "$n_free" -ne "$n_print" ]; then
    printf 'Lean leg: %s of %s #print axioms axiom-free\n' "$n_free" "$n_print" >&2
    exit 1
  fi
  printf 'Lean leg: OK (%s headlines, no axioms)\n' "$n_print"
fi
