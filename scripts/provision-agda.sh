#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# On-demand provisioning of the Agda proof-checker toolchain for this repo.
#
# Automates the steps documented in the "# Build" section of CLAUDE.md so that
# `agda proofs/agda/All.agda` and `agda proofs/agda/Smoke.agda` typecheck.
# Idempotent: safe to re-run; skips anything already in place.
#
# Usage:  bash scripts/provision-agda.sh
set -euo pipefail

log() { echo "[provision-agda] $*"; }

STDLIB_DIR=/opt/agda-stdlib
STDLIB_BRANCH=v2.3
AGDA_HOME="${HOME}/.agda"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# 1. Agda compiler (Ubuntu universe ships 2.6.3; repo needs >= 2.6.3).
if command -v agda >/dev/null 2>&1; then
  log "Agda already present: $(agda --version)"
else
  log "installing Agda compiler (agda-bin)…"
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -qq || true   # tolerate unrelated third-party PPA failures
  apt-get install -y agda-bin >/dev/null
  log "Agda installed: $(agda --version)"
fi

# 2. agda-stdlib 2.3 from source (Ubuntu's agda-stdlib is 1.7.x — too old: it
#    lacks Data.Product.Base and other modules this repo imports).
if [ -f "${STDLIB_DIR}/standard-library.agda-lib" ]; then
  log "agda-stdlib already at ${STDLIB_DIR}"
else
  log "cloning agda-stdlib ${STDLIB_BRANCH}…"
  rm -rf "${STDLIB_DIR}"
  git clone --depth 1 --branch "${STDLIB_BRANCH}" \
    https://github.com/agda/agda-stdlib.git "${STDLIB_DIR}" >/dev/null 2>&1
  # ships as `name: standard-library-2.3`; echo-types depends on `standard-library`.
  sed -i 's/^name: standard-library-2.3$/name: standard-library/' \
    "${STDLIB_DIR}/standard-library.agda-lib"
  log "agda-stdlib ${STDLIB_BRANCH} ready"
fi

# 3. Locate absolute-zero (echo-types.agda-lib: `depend: standard-library absolute-zero`).
#    Expected as a sibling checkout in the multi-repo workspace.
AZ_LIB=""
for cand in \
  "${REPO_ROOT}/../absolute-zero/absolute-zero.agda-lib" \
  "/home/user/absolute-zero/absolute-zero.agda-lib" \
  "${HOME}/absolute-zero/absolute-zero.agda-lib"; do
  if [ -f "$cand" ]; then
    AZ_LIB="$(cd "$(dirname "$cand")" && pwd)/absolute-zero.agda-lib"
    break
  fi
done

# 4. Register libraries + default (idempotent rewrite).
mkdir -p "${AGDA_HOME}"
{
  echo "${STDLIB_DIR}/standard-library.agda-lib"
  if [ -n "${AZ_LIB}" ]; then echo "${AZ_LIB}"; fi
} > "${AGDA_HOME}/libraries"
echo "standard-library" > "${AGDA_HOME}/defaults"

if [ -n "${AZ_LIB}" ]; then
  log "registered libraries: standard-library + absolute-zero"
else
  log "WARNING: absolute-zero library not found — echo-types depends on it and"
  log "         will not typecheck. Check out the absolute-zero repo as a sibling"
  log "         of echo-types (or add it to this session's scope), then re-run."
fi

log "done. Verify with:  LC_ALL=C.UTF-8 agda proofs/agda/All.agda"
