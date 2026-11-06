#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Check the audit's changed proofs plus the existing seven CI entrypoints.
# Required: AGDA_STDLIB points at stdlib src, ABSOLUTE_ZERO_AGDA at proofs/agda.
# Optional: AGDA (executable), AUDIT_LOG_DIR, AUDIT_COLD=1 (ignore interfaces).
set -euo pipefail
cd "$(dirname "$0")/.."
: "${AGDA_STDLIB:?Set AGDA_STDLIB to the pinned standard-library src directory}"
: "${ABSOLUTE_ZERO_AGDA:?Set ABSOLUTE_ZERO_AGDA to the pinned CNO source directory}"
agda_bin="${AGDA:-agda}"
log_dir="${AUDIT_LOG_DIR:-build/audit-2026-11-06}"
mkdir -p "$log_dir"
args=(--no-libraries -i proofs/agda -i "$AGDA_STDLIB" -i "$ABSOLUTE_ZERO_AGDA")
if [[ "${AUDIT_COLD:-0}" == 1 ]]; then args+=(--ignore-interfaces); fi
"$agda_bin" --version > "$log_dir/compiler.txt"
git rev-parse HEAD > "$log_dir/base-commit.txt"
find proofs/agda -name '*.agda' -type f -print0 | sort -z | xargs -0 sha256sum > "$log_dir/proof-sources.sha256"
: > "$log_dir/results.tsv"
check() {
  local profile="$1" module="$2" key="${2//\//_}"
  local flags=(--safe --without-K --cubical-compatible)
  if [[ "$profile" == cubical ]]; then flags=(--safe --cubical); fi
  if "$agda_bin" "${args[@]}" "${flags[@]}" "proofs/agda/$module.agda" > "$log_dir/$key.log" 2>&1; then
    printf 'PASS\t%s\n' "$module" | tee -a "$log_dir/results.tsv"
  else
    local status=$?
    printf 'FAIL(%s)\t%s\n' "$status" "$module" | tee -a "$log_dir/results.tsv"
    tail -n 35 "$log_dir/$key.log"
    return "$status"
  fi
}
for module in EchoSourcePreserving EchoCNOSemantics EchoDependentPushforward \
              EchoSourcePreservingComparison EchoCNOPackaging EchoFiniteResidue \
              EchoResidueProtocol Echo/Measure/Composition \
              EchoErasingGradedComonad EchoNaturalityIndependence \
              EchoThinPreorderExample EchoGradedComonadNaturality \
              EchoGradedComonadF1 EchoGradedComonadInstance1 EchoGradedComonadInstance2 \
              EchoSeparating EchoCharacteristic EchoResidue EchoNoSectionGeneric AuditSmoke; do
  check ordinary "$module"
done
for module in All Smoke characteristic/All examples/All experimental/echo-additive/All NarrowingSmoke; do
  check ordinary "$module"
done
check cubical EchoImageFactorizationPropCubical
