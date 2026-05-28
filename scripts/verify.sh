#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
set -e

echo "Running verifications..."

echo "1. Checking no unsafe constructs..."
sh scripts/check-no-unsafe.sh

echo "2. Building All.agda..."
agda -i proofs/agda proofs/agda/All.agda

echo "3. Running just verify..."
just verify

echo "✅ All verifications passed."
