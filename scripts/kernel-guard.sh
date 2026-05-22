#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# (MPL-2.0 is automatic legal fallback until PMPL is formally recognised)
#
# kernel-guard.sh — enforce the EchoKernel funext-free certificate and
# keep docs/echo-types/echo-kernel-note.adoc honest.
#
# Two independent checks (both must pass; POSIX sh, coreutils only):
#
#   A. Funext-free certificate (kernel-cone integrity)
#      The in-repo kernel cone is exactly { Echo, EchoKernel }. Assert:
#        * both carry `--safe --without-K` and no safety-relaxing flag;
#        * neither contains a postulate / escape pragma (defence in
#          depth — `--safe` already blocks these, but we want a
#          legible failure, not an Agda backtrace);
#        * neither *imports* Axiom.Extensionality / a funext module
#          (comments mentioning "funext" are fine — only import lines
#          are scanned);
#        * Echo imports zero in-repo modules (stdlib-only root);
#        * EchoKernel's in-repo imports are a subset of { Echo }.
#      The certificate is then: kernel cone = these two files + stdlib,
#      none of which can reach funext.
#
#   B. Classification-drift lint (reverse dependency on the note)
#      Every proofs/agda/Echo*.agda module must be named in
#      echo-kernel-note.adoc. A new Echo* module that imports outside
#      the kernel (i.e. any derived module) therefore *cannot* land
#      without being classified there — the note stays the SoT.
#
# Usage: scripts/kernel-guard.sh   (run from repo root; exit 0 = pass)

set -eu

AGDA_DIR="proofs/agda"
NOTE="docs/echo-types/echo-kernel-note.adoc"
ECHO_SRC="$AGDA_DIR/Echo.agda"
KERNEL_SRC="$AGDA_DIR/EchoKernel.agda"

fail() { printf 'kernel-guard: FAIL: %s\n' "$1" >&2; exit 1; }
note()  { printf 'kernel-guard: %s\n' "$1"; }

for f in "$ECHO_SRC" "$KERNEL_SRC" "$NOTE"; do
  [ -f "$f" ] || fail "expected file missing: $f"
done

# --- Import extraction -------------------------------------------------
# Real import lines only (not comments): `open import M ...` / `import M`.
# Prints the dotted module token following the `import` keyword.
imports_of() {
  grep -E '^[[:space:]]*(open[[:space:]]+import|import)[[:space:]]' "$1" \
    | awk '{ for (i = 1; i <= NF; i++) if ($i == "import") { print $(i+1); break } }'
}

# Is dotted module name an in-repo module (a file under proofs/agda)?
is_in_repo() {
  _p=$(printf '%s' "$1" | tr '.' '/')
  [ -f "$AGDA_DIR/$_p.agda" ]
}

in_repo_imports_of() {
  imports_of "$1" | while IFS= read -r m; do
    [ -n "$m" ] || continue
    if is_in_repo "$m"; then printf '%s\n' "$m"; fi
  done
}

# ======================================================================
# Check A — funext-free certificate
# ======================================================================
note "A. funext-free certificate (kernel cone = Echo + EchoKernel)"

for src in "$ECHO_SRC" "$KERNEL_SRC"; do
  head -1 "$src" | grep -q -- '--safe' \
    || fail "$src: missing --safe in the OPTIONS pragma"
  head -1 "$src" | grep -q -- '--without-K' \
    || fail "$src: missing --without-K in the OPTIONS pragma"

  # No safety-relaxing flag, anywhere.
  if grep -nE -- '--(type-in-type|cubical|rewriting|sized-types|guardedness|injective-type-constructors|no-positivity-check|no-termination-check|allow-unsolved-metas)' "$src" >/dev/null; then
    fail "$src: a safety-relaxing OPTIONS flag is present"
  fi

  # No postulate / escape construct in *code* (skip --comment lines).
  if grep -vE '^[[:space:]]*--' "$src" \
       | grep -nE '(^|[^A-Za-z_])(postulate|believe_me|primTrustMe|primEraseEquality)([^A-Za-z_]|$)|\{-#[[:space:]]*(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_TERMINATION_CHECK|INJECTIVE)' >/dev/null; then
    fail "$src: postulate/escape construct present (breaks the certificate)"
  fi

  # No funext *import* (import lines only — prose is allowed).
  if imports_of "$src" | grep -qiE '(^|\.)Extensionality$|(^|\.)Funext$|Axiom\.Extensionality'; then
    fail "$src: imports a funext/Extensionality module — certificate void"
  fi
done

# Echo is the stdlib-only root: zero in-repo imports.
echo_repo_imports=$(in_repo_imports_of "$ECHO_SRC" | sort -u)
if [ -n "$echo_repo_imports" ]; then
  fail "Echo.agda must import zero in-repo modules; found: $(echo "$echo_repo_imports" | tr '\n' ' ')"
fi

# EchoKernel's in-repo imports ⊆ { Echo }.
bad_kernel_imports=$(in_repo_imports_of "$KERNEL_SRC" | sort -u | grep -vx 'Echo' || true)
if [ -n "$bad_kernel_imports" ]; then
  fail "EchoKernel.agda may only import Echo in-repo; offending: $(echo "$bad_kernel_imports" | tr '\n' ' ')"
fi
note "   ok: cone is { Echo, EchoKernel }, no funext / postulate / escape"

# ======================================================================
# Check B — classification-drift lint
# ======================================================================
note "B. classification-drift lint (every Echo*.agda named in the note)"

missing=""
for f in "$AGDA_DIR"/Echo*.agda; do
  [ -e "$f" ] || continue
  mod=$(basename "$f" .agda)
  # The note must name the module as a whole identifier (inside a
  # backticked token, a path, or prose — any explicit mention counts;
  # the word-boundary stops EchoGraded matching EchoGradedComonad).
  if ! grep -qE "(^|[^A-Za-z0-9_])$mod([^A-Za-z0-9_]|\$)" "$NOTE"; then
    missing="$missing $mod"
  fi
done
if [ -n "$missing" ]; then
  fail "unclassified Echo* module(s) — add to $NOTE (and MAP.adoc tag):$missing"
fi

# Soft: note names a module that no longer exists (stale entry → warn).
stale=""
for mod in $(grep -oE '\`Echo[A-Za-z0-9_]*\`' "$NOTE" | tr -d '\`' | sort -u); do
  [ -f "$AGDA_DIR/$mod.agda" ] || stale="$stale $mod"
done
[ -n "$stale" ] && note "   warning: note references absent module(s):$stale"
note "   ok: all Echo*.agda modules are classified in the note"

note "PASS — funext-free certificate enforced; classification in sync."
