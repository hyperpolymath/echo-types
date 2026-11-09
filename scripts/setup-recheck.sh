#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Linux x86-64 toolchain for the Rocq and Lean recheck legs
# (PROOF-POLICY section 2). Versions are asserted; a mismatch fails before
# any proof is checked.
#
# Deviation (PROOF-POLICY section 6): these provers are installed from the
# Ubuntu archive (Rocq/Coq) and from the upstream Lean release archive at a
# checked-in SHA-256, not from the repo's Guix manifest or container. The
# Agda lane makes the same choice in scripts/setup-agda.sh. The record is in
# proofs/RECHECK-EchoSearchExample.adoc, "Toolchain deviation". State: open.
set -euo pipefail

COQ_DEB_VERSION=8.18.0+dfsg-1build2
COQ_VERSION=8.18.0
LEAN_VERSION=4.30.0
LEAN_SHA256=4dad74141c2c119ca1aa626656be83b8e14238afba97271fd7bf1eb3f081b319

test "$(uname -s)-$(uname -m)" = Linux-x86_64
tool_dir="${RECHECK_TOOLS_DIR:-${RUNNER_TEMP:?RUNNER_TEMP or RECHECK_TOOLS_DIR is required}/echo-recheck}"
mkdir -p "$tool_dir"
tool_dir="$(cd "$tool_dir" && pwd)"

want="${1:-all}"
case "$want" in
  all|rocq|lean) ;;
  *) printf 'usage: %s [rocq|lean|all]\n' "$0" >&2; exit 2 ;;
esac

if [ "$want" = all ] || [ "$want" = rocq ]; then
  if ! dpkg-query -W -f='${Version}' coq 2>/dev/null | grep -qx "$COQ_DEB_VERSION"; then
    sudo_cmd=""
    [ "$(id -u)" -eq 0 ] || sudo_cmd=sudo
    $sudo_cmd apt-get update -qq
    $sudo_cmd env DEBIAN_FRONTEND=noninteractive apt-get install -y -qq "coq=$COQ_DEB_VERSION"
  fi
  actual="$(coqc --print-version | awk '{print $1}')"
  if [ "$actual" != "$COQ_VERSION" ]; then
    printf 'Rocq/Coq mismatch: expected %s, got %s\n' "$COQ_VERSION" "$actual" >&2
    exit 1
  fi
  printf 'coq=%s (deb %s)\n' "$actual" "$COQ_DEB_VERSION"
fi

if [ "$want" = all ] || [ "$want" = lean ]; then
  archive="$tool_dir/lean-$LEAN_VERSION-linux.tar.zst"
  if [ ! -f "$archive" ]; then
    curl --fail --location --retry 3 --proto '=https' --output "$archive" \
      "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.tar.zst"
  fi
  printf '%s  %s\n' "$LEAN_SHA256" "$archive" | sha256sum --check --strict -
  tar --zstd -xf "$archive" -C "$tool_dir"
  lean="$tool_dir/lean-$LEAN_VERSION-linux/bin/lean"
  actual="$("$lean" --version)"
  case "$actual" in
    "Lean (version $LEAN_VERSION,"*) ;;
    *) printf 'Lean mismatch: expected %s, got %s\n' "$LEAN_VERSION" "$actual" >&2; exit 1 ;;
  esac
  printf 'export LEAN=%q\n' "$lean" > "$tool_dir/env.sh"
  [ -z "${GITHUB_ENV:-}" ] || printf 'LEAN=%s\n' "$lean" >> "$GITHUB_ENV"
  printf '%s\nlean-archive-sha256=%s\n' "$actual" "$LEAN_SHA256"
fi
