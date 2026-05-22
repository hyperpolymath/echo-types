#!/bin/sh

echo "Checking for unsafe constructs in proofs/agda..."

# Search for postulate, TERMINATING, NON_TERMINATING, allow-unsolved-metas, ignoring lines containing -- that explain the lack of postulates.
UNSAFE=$(grep -rnE '^\s*postulate\b|{-# TERMINATING #-}|{-# NON_TERMINATING #-}|{-# OPTIONS.*--allow-unsolved-metas' proofs/agda)

if [ -n "$UNSAFE" ]; then
    echo "❌ Unsafe constructs found:"
    echo "$UNSAFE"
    exit 1
fi

echo "✅ No unsafe constructs found."
exit 0
