#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SessionStart hook: provision the Agda proof-checker toolchain so Claude Code
# on the web can typecheck this repo (agda proofs/agda/All.agda, Smoke.agda).
#
# Thin wrapper around scripts/provision-agda.sh (idempotent). Web-only; local
# developers manage their own toolchain. Synchronous so the toolchain is ready
# before the agent loop starts.
set -euo pipefail

# Only provision in the remote (web) environment.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

exec bash "${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}/scripts/provision-agda.sh"
