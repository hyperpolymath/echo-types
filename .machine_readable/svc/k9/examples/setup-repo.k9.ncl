K9!
# SPDX-License-Identifier: MPL-2.0
# Hunt-level K9 component: echo-types toolchain bootstrap
# Security Level: Hunt (full system access)
# SIGNATURE REQUIRED - Review carefully before use

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "setup-script",
    security = {
      leash = 'Hunt,
      trust_level = "full-system-access",
      allow_network = true,
      allow_filesystem_write = true,
      allow_subprocess = true,
      signature_required = true,
    },
    metadata = {
      name = "echo-types-setup-repo",
      version = "1.0.0",
      description = "Bootstraps the Agda toolchain (Agda >= 2.6.3 + agda-stdlib v2.3 from source) so the verified suite typechecks. Derived from CLAUDE.md § Build.",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
    warnings = [
      "This component clones an external repo and writes to /opt and ~/.agda",
      "Only run from a trusted source with a verified signature",
      "Review all Just recipes before execution",
      "Use dry-run mode first: ./must --dry-run run setup-repo.k9.ncl",
    ],
    side_effects = [
      "Clones agda-stdlib v2.3 into /opt/agda-stdlib",
      "Writes /opt/agda-stdlib/standard-library.agda-lib (name normalised)",
      "Writes ~/.agda/libraries",
      "Runs `agda` over proofs/agda/All.agda (no network, CPU-bound)",
    ],
  },

  config = {
    stdlib_dir
      | String
      | std.string.NonEmpty
      = "/opt/agda-stdlib",

    stdlib_branch
      | String
      | std.string.NonEmpty
      = "v2.3",

    dry_run | Bool = false,
  },

  recipes = {
    default = {
      recipe = "bootstrap",
      description = "Install stdlib v2.3, register it, and typecheck the suite",
    },

    "bootstrap" = {
      dependencies = ["check-prerequisites", "install-stdlib", "register-stdlib"],
      commands = [
        "agda -i proofs/agda proofs/agda/All.agda",
        "agda -i proofs/agda proofs/agda/Smoke.agda",
        "scripts/kernel-guard.sh",
      ],
    },

    "check-prerequisites" = {
      description = "Verify agda and git are present",
      commands = [
        "command -v agda || (echo 'ERROR: agda (>= 2.6.3) not found' && exit 1)",
        "command -v git  || (echo 'ERROR: git not found' && exit 1)",
      ],
    },

    "install-stdlib" = {
      description = "Clone agda-stdlib v2.3 from source",
      commands = [
        "test -d %{config.stdlib_dir} || git clone --depth 1 --branch %{config.stdlib_branch} https://github.com/agda/agda-stdlib.git %{config.stdlib_dir}",
        "sed -i 's/^name: standard-library-2.3$/name: standard-library/' %{config.stdlib_dir}/standard-library.agda-lib",
      ],
    },

    "register-stdlib" = {
      description = "Register the library with Agda",
      commands = [
        "mkdir -p ~/.agda",
        "echo %{config.stdlib_dir}/standard-library.agda-lib > ~/.agda/libraries",
      ],
    },
  },

  validation = {
    check_stdlib_dir = std.string.length config.stdlib_dir > 0,
    check_branch = std.string.length config.stdlib_branch > 0,
  },
}

# Usage:
# 1. Review side_effects and recipes
# 2. Dry-run: ./must --dry-run run setup-repo.k9.ncl
# 3. Sign:    ./must sign setup-repo.k9.ncl
# 4. Run:     ./must verify && ./must run setup-repo.k9.ncl
