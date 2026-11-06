#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
# Compatibility entrypoint. The canonical guard strips comments and enforces
# the existing, explicit quarantine/profile exemptions; do not duplicate it.
exec bash tools/check-guardrails.sh proofs/agda
