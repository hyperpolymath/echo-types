K9!
# SPDX-License-Identifier: MPL-2.0
# Example Yard-level K9 component: CI/CD configuration with validation
# Security Level: Yard (Nickel evaluation, contract validation)
# Signature recommended but not required

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
      name = "ci-config",
      version = "1.0.0",
      description = "CI/CD configuration with runtime validation",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # CI/CD configuration with Nickel contracts
  ci = {
    # Platform must be a known CI provider
    platform
      | [| 'GitHubActions, 'GitLabCI, 'CircleCI, 'TravisCI |]
      = 'GitHubActions,

    # Build matrix with validation
    matrix = {
      # Operating systems to test on
      os
        | Array String
        | std.array.NonEmpty
        = ["ubuntu-latest"],

      # Language versions to test
      versions
        | Array String
        | std.array.NonEmpty
        = ["agda-2.6.x + agda-stdlib-2.3"],   # per .github/workflows/agda.yml (CI installs stdlib v2.3)
    },

    # Workflow steps with validation
    steps = [
      {
        name = "Checkout",
        action = "actions/checkout@v4",
        # Version must be SHA-pinned for security
        sha | String | std.string.NonEmpty = "b4ffde65f46336ab88eb53be808477a3936bae11",
      },
      {
        name = "Build",
        run = "agda -i proofs/agda proofs/agda/All.agda",
      },
      {
        name = "Test",
        run = "agda -i proofs/agda proofs/agda/Smoke.agda",
      },
      {
        name = "Lint",
        run = "scripts/kernel-guard.sh && tools/check-guardrails.sh",
      },
    ],

    # Deployment configuration
    deploy = {
      enabled | Bool = false,

      # Only deploy from main branch
      branch
        | String
        | std.contract.from_predicate (fun b => b == "main" || b == "master")
        = "main",

      # Deployment requires manual approval
      requires_approval | Bool = true,
    },

    # Security scanning
    security = {
      enabled | Bool = true,

      scanners = [
        {
          name = "CodeQL",
          languages = ["javascript-typescript", "actions"],   # per .github/workflows/codeql.yml
        },
        {
          name = "OSSF Scorecard",
          enabled = true,
        },
        {
          name = "secret-scanner",   # .github/workflows/secret-scanner.yml
          scan_for = "secrets",
        },
      ],
    },

    # Notification settings
    notifications = {
      on_success = "never",
      on_failure = "always",
      channels = ["email"],
    },
  },

  # Validation rules (enforced by Nickel)
  validation = {
    # At least one OS must be specified
    check_os = std.array.length ci.matrix.os > 0,

    # At least one version must be tested
    check_versions = std.array.length ci.matrix.versions > 0,

    # Must have at least build and test steps
    check_steps = std.array.length ci.steps >= 2,

    # Security scanning must be enabled
    check_security = ci.security.enabled == true,
  },
}
