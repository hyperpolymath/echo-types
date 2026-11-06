#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

# Same guards and proof runner as `just verify`, without requiring just.
# Source the environment from scripts/setup-agda.sh before running this.
sh scripts/kernel-guard.sh
bash tools/check-guardrails.sh proofs/agda
bash scripts/check-experimental-aggregate.sh
sh scripts/check-agda-invocations.sh
exec bash tools/check-audit.sh
