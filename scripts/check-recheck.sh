#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Check the Rocq and Lean recheck legs and fail on any axiom.
# Usage: scripts/check-recheck.sh [rocq|lean|all]. Needs coqc on PATH and
# LEAN set to the lean binary (scripts/setup-recheck.sh provides both).
# Save stdout and stderr if a receipt is needed.
set -euo pipefail
cd "$(dirname "$0")/.."
want="${1:-all}"
case "$want" in
  all|rocq|lean) ;;
  *) printf 'usage: %s [rocq|lean|all]\n' "$0" >&2; exit 2 ;;
esac
printf 'Source commit: %s\n' "$(git rev-parse HEAD)"

# The five headlines of the PWG record (PROOF-STATUS.adoc). Each must have its
# own assumption check: a check on a supporting lemma never stands in for one.
rocq_headlines=(search_double_6_decided search_as_echo search_as_cost search_as_dec search_as_feasible)
lean_headlines=(searchDouble6Decided searchAsEcho searchAsCost searchAsDec searchAsFeasible)

if [ "$want" = all ] || [ "$want" = rocq ]; then
  v=proofs/rocq/EchoSearchExample.v
  coqc --version
  if ! out="$(cd proofs/rocq && coqc -q EchoSearchExample.v 2>&1)"; then
    printf '%s\n' "$out"
    printf 'Rocq leg: coqc failed\n' >&2
    exit 1
  fi
  printf '%s\n' "$out"
  for h in "${rocq_headlines[@]}"; do
    if ! grep -qx "Print Assumptions $h\." "$v"; then
      printf 'Rocq leg: no Print Assumptions for headline %s\n' "$h" >&2
      exit 1
    fi
  done
  # Every Print Assumptions must close; any axiom fails the leg.
  n_closed="$(printf '%s\n' "$out" | grep -c '^Closed under the global context$' || true)"
  n_print="$(grep -c '^Print Assumptions' "$v")"
  if [ "$n_closed" -ne "$n_print" ]; then
    printf 'Rocq leg: %s of %s Print Assumptions closed\n' "$n_closed" "$n_print" >&2
    exit 1
  fi
  rm -f proofs/rocq/*.vo proofs/rocq/*.vok proofs/rocq/*.vos proofs/rocq/*.glob proofs/rocq/.*.aux
  printf 'Rocq leg: OK (%s headlines and %s checks in all, no axioms)\n' \
    "${#rocq_headlines[@]}" "$n_print"
fi

if [ "$want" = all ] || [ "$want" = lean ]; then
  lean="${LEAN:?set LEAN to the lean binary}"
  "$lean" --version
  if ! out="$("$lean" proofs/lean4/EchoSearchExample.lean 2>&1)"; then
    printf '%s\n' "$out"
    printf 'Lean leg: lean failed\n' >&2
    exit 1
  fi
  printf '%s\n' "$out"
  if printf '%s\n' "$out" | grep -qE 'error|warning|sorry|depends on axioms'; then
    printf 'Lean leg: error, warning, sorry or axiom reported\n' >&2
    exit 1
  fi
  for h in "${lean_headlines[@]}"; do
    if ! printf '%s\n' "$out" | grep -qF "'EchoSearchExample.$h' does not depend on any axioms"; then
      printf 'Lean leg: headline %s has no axiom-free #print axioms result\n' "$h" >&2
      exit 1
    fi
  done
  n_free="$(printf '%s\n' "$out" | grep -c 'does not depend on any axioms' || true)"
  n_print="$(grep -c '^#print axioms' proofs/lean4/EchoSearchExample.lean)"
  if [ "$n_free" -ne "$n_print" ]; then
    printf 'Lean leg: %s of %s #print axioms axiom-free\n' "$n_free" "$n_print" >&2
    exit 1
  fi
  printf 'Lean leg: OK (%s headlines and %s checks in all, no axioms)\n' \
    "${#lean_headlines[@]}" "$n_print"
fi
