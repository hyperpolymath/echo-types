K9!
# SPDX-License-Identifier: MPL-2.0
# Yard-level K9 component: echo-types CI configuration with validation
# Security Level: Yard (Nickel evaluation, contract validation)
# Mirrors .github/workflows/agda.yml — Signature recommended

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "ci-configuration",
    security = {
      leash = 'Yard,
      trust_level = "validated-config",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
    },
    metadata = {
      name = "echo-types-ci-config",
      version = "1.0.0",
      description = "Agda proof-suite CI configuration with runtime validation",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  ci = {
    platform
      | [| 'GitHubActions, 'GitLabCI, 'Codeberg |]
      = 'GitHubActions,

    toolchain = {
      agda_version
        | String
        | std.string.NonEmpty
        = "2.6.3",
      stdlib_version
        | String
        | std.string.NonEmpty
        = "2.3",
      locale = "C.UTF-8",
    },

    # The proof gate — order matters: All before Smoke before kernel-guard.
    steps = [
      {
        name = "Checkout",
        action = "actions/checkout@v4",
        sha | String | std.string.NonEmpty = "b4ffde65f46336ab88eb53be808477a3936bae11",
      },
      {
        name = "Install agda-stdlib v2.3 from source",
        run = "git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git /opt/agda-stdlib",
      },
      {
        name = "Typecheck verified suite",
        run = "agda -i proofs/agda proofs/agda/All.agda",
      },
      {
        name = "Typecheck headline pins",
        run = "agda -i proofs/agda proofs/agda/Smoke.agda",
      },
      {
        name = "Kernel-cone certificate",
        run = "scripts/kernel-guard.sh",
      },
      {
        name = "No unsafe constructs",
        run = "scripts/check-no-unsafe.sh",
      },
    ],

    security = {
      enabled | Bool = true,
      scanners = [
        { name = "CodeQL" },
        { name = "OSSF Scorecard", enabled = true },
        { name = "Hypatia", scan_for = "neurosymbolic-findings" },
        { name = "secret-scanner", scan_for = "secrets" },
      ],
    },

    notifications = {
      on_success = "never",
      on_failure = "always",
      channels = ["email"],
    },
  },

  validation = {
    # The two typecheck steps + kernel-guard are mandatory.
    check_all_agda =
      std.array.any (fun s => std.record.has_field "run" s && s.run == "agda -i proofs/agda proofs/agda/All.agda") ci.steps,
    check_smoke =
      std.array.any (fun s => std.record.has_field "run" s && s.run == "agda -i proofs/agda proofs/agda/Smoke.agda") ci.steps,
    check_kernel_guard =
      std.array.any (fun s => std.record.has_field "run" s && s.run == "scripts/kernel-guard.sh") ci.steps,
    check_security = ci.security.enabled == true,
  },
}
