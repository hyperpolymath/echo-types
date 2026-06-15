#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Foundation guardrail (added 2026-05-18 — the long-documented
# "CI-grep-enforced" check that did not previously exist).
#
# Scans EVERY proofs/agda/**/*.agda — independent of any All.agda
# closure, so a module that no aggregator imports cannot hide a
# dropped flag or an escape pragma. Asserts, per file:
#
#   1. an `{-# OPTIONS ... #-}` line exists and contains BOTH
#      `--safe` and `--without-K`;
#   2. no axiom-K / soundness-relaxing OPTION flag is present;
#   3. no escape pragma (deny-list) anywhere;
#   4. no `postulate` in code (comments are stripped first, so
#      retraction/banner prose that *mentions* the word is fine).
#
# This is defence-in-depth. The primary soundness guarantee is still
# `--safe` enforced by the typecheck lanes; this catches the gap that
# `--safe` is per-file and only bites for files Agda actually loads.
#
# Comment stripping handles Agda `--` line comments and `{- … -}`
# block comments while preserving `{-# … #-}` pragmas. It does not
# model nested block comments (this codebase uses `--` banners, not
# nested `{- -}`); the typecheck lanes remain the backstop.
#
# Exit non-zero on the first failing file; prints every violation.

set -euo pipefail

ROOT="${1:-proofs/agda}"
fail=0

# Pragma names that must never appear in a {-# … #-} block.
DENY_PRAGMA='TERMINATING|NON_TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|POLARITY|INJECTIVE|IMPOSSIBLE|REWRITE|DISPLAY|ETA|NOT_PROJECTION_LIKE'
# OPTION flags that relax soundness / reintroduce K.
DENY_FLAG='--type-in-type|--cumulativity|--allow-unsolved-metas|--no-positivity-check|--no-termination-check|--injective-type-constructors|--rewriting|--with-K|--no-without-K|--guardedness=off'

# Exploratory modules exempt from guardrail checks (per
# docs/echo-types/echo-kernel-note.adoc, these are deliberately
# outside the kernel cone and use postulates by design).
EXPLORATORY_EXEMPT=(
  "EchoImageFactorizationPropPostulated"
  "EchoImageFactorizationPropCubical"
  "EchoDecorationBridge"
  "Fidelity"
)

strip_comments() {
  # Remove {- … -} blocks (but keep {-# … #-}), then -- line comments.
  awk '
    {
      line = $0
      out = ""
      i = 1
      n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        thr = substr(line, i, 3)
        if (incmt) {
          if (two == "-}") { incmt = 0; i += 2; continue }
          i += 1; continue
        }
        if (thr == "{-#") { out = out thr; i += 3; continue }   # keep pragma open
        if (two == "{-")  { incmt = 1; i += 2; continue }       # enter block comment
        if (two == "--")  { break }                              # line comment to EOL
        out = out substr(line, i, 1)
        i += 1
      }
      print out
    }
  ' "$1"
}

is_exploratory_exempt() {
  local filename="$1"
  local basename="${filename%.*}"
  basename="${basename##*/}"
  for exempt in "${EXPLORATORY_EXEMPT[@]}"; do
    if [ "$basename" = "$exempt" ]; then
      return 0
    fi
  done
  return 1
}

while IFS= read -r -d '' f; do
  rel="${f#./}"

  # Skip exploratory/exempt modules
  if is_exploratory_exempt "$f"; then
    continue
  fi

  # (1)+(2) OPTIONS line.
  opts_line="$(grep -m1 -E '\{-#[[:space:]]*OPTIONS' "$f" || true)"
  if [ -z "$opts_line" ]; then
    echo "VIOLATION [$rel]: no {-# OPTIONS #-} line"
    fail=1
  else
    case "$opts_line" in
      *--safe*) : ;;
      *) echo "VIOLATION [$rel]: OPTIONS missing --safe"; fail=1 ;;
    esac
    case "$opts_line" in
      *--without-K*) : ;;
      *) echo "VIOLATION [$rel]: OPTIONS missing --without-K"; fail=1 ;;
    esac
    if echo "$opts_line" | grep -qE -e "$DENY_FLAG"; then
      echo "VIOLATION [$rel]: OPTIONS has a soundness-relaxing flag: $opts_line"
      fail=1
    fi
  fi

  # (3) escape pragmas anywhere.
  if grep -nE "\{-#[^#]*(${DENY_PRAGMA})" "$f" >/dev/null 2>&1; then
    echo "VIOLATION [$rel]: forbidden pragma:"
    grep -nE "\{-#[^#]*(${DENY_PRAGMA})" "$f" | sed 's/^/    /'
    fail=1
  fi

  # (4) postulate / unsafe prims in code (comments stripped).
  stripped="$(strip_comments "$f")"
  if echo "$stripped" | grep -nE '(^|[^[:alnum:]_])postulate([^[:alnum:]_]|$)' >/dev/null 2>&1; then
    echo "VIOLATION [$rel]: 'postulate' in code (not a comment)"
    fail=1
  fi
  if echo "$stripped" | grep -nE 'primTrustMe|primEraseEquality|trustMe' >/dev/null 2>&1; then
    echo "VIOLATION [$rel]: unsafe primitive (primTrustMe/primEraseEquality/trustMe) in code"
    fail=1
  fi
done < <(find "$ROOT" -name '*.agda' -print0)

if [ "$fail" -ne 0 ]; then
  echo "guardrail: FAIL"
  exit 1
fi
echo "guardrail: OK — all $(find "$ROOT" -name '*.agda' | wc -l) modules declare --safe --without-K, no escape pragmas, no postulates (except exploratory: ${EXPLORATORY_EXEMPT[*]})"
