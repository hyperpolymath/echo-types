#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Linux x86-64 CI toolchain. A release archive is accepted only at the
# checked-in checksum; version/dependency mismatches fail before typechecking.
set -euo pipefail

AGDA_VERSION=2.7.0.1
AGDA_SHA256=975b515a14877ab6bce5bfc641e16c4a3ee52ca5d7f846577dee80aa2145db8a
STDLIB_SHA=8326c7475af1fa456ca04a0203c168d5d7ff842b
ABSZ_SHA=f486c29903434589117fa0662c6f29b0f17d1d5f

test "$(uname -s)-$(uname -m)" = Linux-x86_64
tool_dir="${AGDA_TOOLS_DIR:-${RUNNER_TEMP:?RUNNER_TEMP or AGDA_TOOLS_DIR is required}/echo-agda}"
mkdir -p "$tool_dir"
tool_dir="$(cd "$tool_dir" && pwd)"
archive="${AGDA_ARCHIVE_PATH:-$tool_dir/Agda-v$AGDA_VERSION-linux.tar.xz}"
if [ ! -f "$archive" ]; then
  curl --fail --location --retry 3 --proto '=https' \
    --output "$archive" \
    "https://github.com/agda/agda/releases/download/v$AGDA_VERSION/Agda-v$AGDA_VERSION-linux.tar.xz"
fi
printf '%s  %s\n' "$AGDA_SHA256" "$archive" | sha256sum --check --strict -
tar -xf "$archive" -C "$tool_dir"
agda_root="$tool_dir/Agda-v$AGDA_VERSION"
export Agda_datadir="$agda_root/data"
actual_version="$("$agda_root/bin/agda" --version)"
if [ "$actual_version" != "Agda version $AGDA_VERSION" ]; then
  printf 'Compiler mismatch: expected Agda version %s, got %s\n' "$AGDA_VERSION" "$actual_version" >&2
  exit 1
fi

# Agda 2.7.0.1 can panic in Signature.hs when its first primitive-interface
# build is in full-Cubical mode. Bootstrap the compiler's own Primitive
# interface in the standard safe profile first. Only this generated cache
# file is discarded; the release sources and proof profiles are unchanged.
rm -f "$Agda_datadir/lib/prim/_build/$AGDA_VERSION/agda/Agda/Primitive.agdai"
cat > "$tool_dir/AgdaToolchainBootstrap.agda" <<'AGDA'
{-# OPTIONS --safe --without-K --cubical-compatible #-}
module AgdaToolchainBootstrap where
open import Agda.Primitive using (Level)
AGDA
"$agda_root/bin/agda" --no-libraries --safe --without-K --cubical-compatible \
  -i "$tool_dir" "$tool_dir/AgdaToolchainBootstrap.agda"

fetch_pinned() {
  local url="$2" revision="$3" destination="$tool_dir/$1" actual
  if [ ! -d "$destination/.git" ]; then
    git init --quiet "$destination"
    git -C "$destination" remote add origin "$url"
    git -C "$destination" fetch --quiet --depth=1 origin "$revision"
    git -C "$destination" checkout --quiet --detach FETCH_HEAD
  fi
  actual="$(git -C "$destination" rev-parse HEAD)"
  if [ "$actual" != "$revision" ]; then
    printf 'Dependency mismatch in %s: expected %s, got %s\n' "$destination" "$revision" "$actual" >&2
    exit 1
  fi
}
fetch_pinned agda-stdlib https://github.com/agda/agda-stdlib.git "$STDLIB_SHA"
fetch_pinned absolute-zero https://github.com/hyperpolymath/absolute-zero.git "$ABSZ_SHA"

mkdir -p "$tool_dir/libraries"
printf 'name: standard-library\ninclude: %s/agda-stdlib/src\n' "$tool_dir" > "$tool_dir/libraries/standard-library.agda-lib"
printf 'name: absolute-zero\ninclude: %s/absolute-zero/proofs/agda\n' "$tool_dir" > "$tool_dir/libraries/absolute-zero.agda-lib"
agda_config="${AGDA_CONFIG_DIR:-$tool_dir/agda-config}"
mkdir -p "$agda_config"
printf '%s\n%s\n' "$tool_dir/libraries/standard-library.agda-lib" "$tool_dir/libraries/absolute-zero.agda-lib" > "$agda_config/libraries"
printf 'standard-library\n' > "$agda_config/defaults"
export AGDA_DIR="$agda_config"
export AGDA="$agda_root/bin/agda"
export AGDA_STDLIB="$tool_dir/agda-stdlib/src"
export ABSOLUTE_ZERO_AGDA="$tool_dir/absolute-zero/proofs/agda"

# Local callers can source this file; CI receives the same values below.
{
  printf 'export AGDA=%q\n' "$AGDA"
  printf 'export Agda_datadir=%q\n' "$Agda_datadir"
  printf 'export AGDA_DIR=%q\n' "$AGDA_DIR"
  printf 'export AGDA_STDLIB=%q\n' "$AGDA_STDLIB"
  printf 'export ABSOLUTE_ZERO_AGDA=%q\n' "$ABSOLUTE_ZERO_AGDA"
  printf 'export PATH=%q:"$PATH"\n' "$agda_root/bin"
} > "$tool_dir/env.sh"

if [ -n "${GITHUB_PATH:-}" ]; then
  printf '%s\n' "$agda_root/bin" >> "$GITHUB_PATH"
fi
if [ -n "${GITHUB_ENV:-}" ]; then
  printf 'AGDA=%s\nAgda_datadir=%s\nAGDA_DIR=%s\nAGDA_STDLIB=%s\nABSOLUTE_ZERO_AGDA=%s\n' \
    "$AGDA" "$Agda_datadir" "$AGDA_DIR" "$AGDA_STDLIB" "$ABSOLUTE_ZERO_AGDA" >> "$GITHUB_ENV"
fi
printf '%s\ncompiler-sha256=%s\nstdlib=%s\nabsolute-zero=%s\n' \
  "$actual_version" "$AGDA_SHA256" "$STDLIB_SHA" "$ABSZ_SHA" | tee "$tool_dir/toolchain.txt"
