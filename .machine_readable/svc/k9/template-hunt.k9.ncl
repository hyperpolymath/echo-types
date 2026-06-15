K9!
# SPDX-License-Identifier: MPL-2.0
# K9 Hunt-level template: Full execution with Just recipes
# Security Level: Hunt (full system access)
# SIGNATURE REQUIRED - Review carefully before use

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "TODO: describe component type (e.g., 'deployment', 'setup-script')",
    security = {
      leash = 'Hunt,
      trust_level = "full-system-access",
      allow_network = true,
      allow_filesystem_write = true,
      allow_subprocess = true,
      signature_required = true,
    },
    metadata = {
      name = "TODO: component-name",
      version = "1.0.0",
      description = "TODO: Detailed description of what this component does",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
    warnings = [
      "This component has full system access",
      "Only run from trusted sources with verified signatures",
      "Review all Just recipes before execution",
      "Use dry-run mode first: ./must --dry-run run your-file.k9.ncl",
    ],
    side_effects = [
      "TODO: List what files/directories this creates or modifies",
      "TODO: List what commands this executes",
      "TODO: List what network access this requires",
    ],
  },

  config = {
    target_dir
      | String
      | std.string.NonEmpty
      = "/tmp/k9-output",

    dry_run | Bool = false,
  },

  recipes = {
    default = {
      recipe = "TODO: main-task",
      description = "TODO: What the default recipe does",
    },

    "main-task" = {
      dependencies = ["check-prerequisites"],
      commands = [
        "echo 'TODO: Add your commands here'",
      ],
    },

    "check-prerequisites" = {
      description = "Verify required tools and permissions",
      commands = [
        "echo '✓ Prerequisites checked'",
      ],
    },
  },

  validation = {
    check_target_dir = std.string.length config.target_dir > 0,
  },
}

# Usage:
# 1. Fill in TODO items above
# 2. Define configuration with contracts
# 3. Implement Just recipes with your commands
# 4. Test with dry-run: ./must --dry-run run your-file.k9.ncl
# 5. Sign:    ./must sign your-file.k9.ncl
# 6. Users verify and run: ./must verify && ./must run your-file.k9.ncl
