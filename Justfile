# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Agda 2.7.0.1. See scripts/setup-agda.sh and docs/build.adoc for pinned libraries.
set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

default:
    @just --list

# Ordinary profile; AGDA_STDLIB and ABSOLUTE_ZERO_AGDA are required paths.
build:
    agda --safe --without-K --cubical-compatible --no-libraries -i proofs/agda -i "$AGDA_STDLIB" -i "$ABSOLUTE_ZERO_AGDA" proofs/agda/All.agda

build-echo: build
build-all: build

# Changed proof modules and all seven aggregate roots; logs are receipts.
test:
    bash tools/check-audit.sh

test-all: test
verify: guard test

# Static checks are distinct from typechecking.
guard:
    sh scripts/kernel-guard.sh
    bash tools/check-guardrails.sh proofs/agda
    bash scripts/check-experimental-aggregate.sh
    sh scripts/check-agda-invocations.sh

kernel-guard:
    sh scripts/kernel-guard.sh

metadata:
    bash tools/check-metadata.sh

validate: guard metadata test

audit-inventory:
    bun tools/audit-inventory.mjs

# Actual tool coverage is recorded; neither scanner certifies Agda proofs.
panic:
    mkdir -p build/audit-2026-11-06
    panic-attack assail . --output build/audit-2026-11-06/panic.json

pons:
    mkdir -p build/audit-2026-11-06
    pons scan . --format json > build/audit-2026-11-06/pons.json

stability-report:
    @echo 'No numerical stability metric is defined. See PROOF-STATUS.adoc and docs/audit/ for scoped evidence.'

clean:
    find proofs/agda -type f -name '*.agdai' -delete
