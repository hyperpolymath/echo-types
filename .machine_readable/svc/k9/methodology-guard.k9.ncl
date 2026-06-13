# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <6759885+hyperpolymath@users.noreply.github.com>
#
# K9 Validator: Methodology Guard (echo-types)
# Checks that agent work respects the methodology constraints declared in
# agent_instructions/methodology.a2ml and the proof discipline in
# .machine_readable/6a2/META.a2ml § current-practices.
#
# Usage: k9 validate methodology-guard

let methodology_guard = {
  name = "methodology-guard",
  version = "1.0.0",
  description = "Validates that agent work respects echo-types' --safe --without-K zero-postulate proof discipline",

  checks = {
    safe_without_k_invariant = {
      description = "Every proofs/agda module must carry --safe and --without-K in its OPTIONS pragma",
      severity = "error",
      check_type = "options-pragma-guard",
      scope = "proofs/agda/",
      required_flags = ["--safe", "--without-K"],
    },

    postulate_ceiling = {
      description = "postulate count must not exceed the declared ceiling outside the Ordinal track",
      severity = "error",
      pattern = "^\\s*postulate",
      scope = "proofs/agda/ (excluding Ordinal/)",
      ceiling_key = "methodology.proof-invariants.postulate-ceiling",
      default_ceiling = 0,
    },

    believe_me_ceiling = {
      description = "believe_me / primTrustMe / primEraseEquality count must be zero",
      severity = "error",
      pattern = "believe_me|primTrustMe|primEraseEquality",
      scope = "proofs/agda/",
      ceiling_key = "methodology.proof-invariants.believe-me-ceiling",
      default_ceiling = 0,
    },

    escape_hatch_ceiling = {
      description = "sorry / Admitted / unsafeCoerce / Obj.magic count must be zero",
      severity = "error",
      pattern = "sorry|Admitted|unsafeCoerce|Obj\\.magic",
      scope = "proofs/agda/",
      default_ceiling = 0,
    },

    headline_pinned = {
      description = "Every headline theorem must be pinned in Smoke.agda via a `using` clause",
      severity = "warning",
      check_type = "smoke-pin-guard",
      file = "proofs/agda/Smoke.agda",
      rule = "New named theorems in All.agda's import set should appear in a Smoke.agda `using (...)` block.",
    },

    module_wired = {
      description = "Every new module must be wired into All.agda (orphan modules are dead code)",
      severity = "warning",
      check_type = "all-agda-coverage-guard",
      file = "proofs/agda/All.agda",
    },

    kernel_cone_intact = {
      description = "The funext-free kernel cone (Echo, EchoKernel) must pass scripts/kernel-guard.sh",
      severity = "error",
      check_type = "external-script",
      script = "scripts/kernel-guard.sh",
    },

    state_not_template = {
      description = "STATE.a2ml must not contain template placeholders",
      severity = "warning",
      file = ".machine_readable/6a2/STATE.a2ml",
      reject_patterns = ["{{PLACEHOLDER}}", "{{PROJECT}}", "rsr-template-repo"],
    },

    anchor_clade_not_fabricated = {
      description = "ANCHOR.a2ml clade/uuid must stay TODO until a gv-clade-index assignment exists",
      severity = "warning",
      file = ".machine_readable/anchors/ANCHOR.a2ml",
      require_pattern = "TODO: assign via gv-clade-index registry",
    },

    coverage_updated = {
      description = "coverage.a2ml should be updated within 30 days",
      severity = "info",
      file = ".machine_readable/agent_instructions/coverage.a2ml",
      staleness_days = 30,
    },
  },
}
in methodology_guard
