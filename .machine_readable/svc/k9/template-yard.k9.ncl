K9!
# SPDX-License-Identifier: MPL-2.0
# K9 Yard-level template: Configuration with validation
# Security Level: Yard (Nickel evaluation with contracts)
# Signature recommended but not required

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "TODO: describe component type (e.g., 'validated-config', 'schema')",
    security = {
      leash = 'Yard,
      trust_level = "validated-config",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
    },
    metadata = {
      name = "TODO: component-name",
      version = "1.0.0",
      description = "TODO: Brief description with validation details",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # Configuration with Nickel contracts for validation
  config = {
    name
      | String
      | std.string.NonEmpty
      = "TODO: default value",

    port
      | Number
      | std.contract.from_predicate (fun p => p > 0 && p < 65536)
      = 8080,

    enabled | Bool = true,

    environment
      | [| 'Development, 'Staging, 'Production |]
      = 'Development,

    items
      | Array String
      | std.array.NonEmpty
      = ["item1", "item2"],
  },

  # Cross-field validation rules
  validation = {
    check_items = std.array.length config.items > 0,
    check_production =
      if config.environment == 'Production then
        config.enabled == true
      else
        true,
  },
}

# Usage:
# 1. Fill in TODO items above
# 2. Define your config with appropriate contracts
# 3. Add validation rules in validation = { ... }
# 4. Validate: nickel typecheck your-file.k9.ncl
# 5. Evaluate: nickel eval your-file.k9.ncl
