#!/bin/sh
set -e

echo "Running verifications..."

echo "1. Checking no unsafe constructs..."
sh scripts/check-no-unsafe.sh

echo "2. Building All.agda..."
agda -i proofs/agda proofs/agda/All.agda

echo "3. Running just verify..."
just verify

echo "✅ All verifications passed."
