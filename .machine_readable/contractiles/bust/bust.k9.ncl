K9!
# SPDX-License-Identifier: MPL-2.0
# Pure declaration; no execution, side effects or signature claim.
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:bust",
    contractile_verb = "bust",
    side_effects = [
    ],
    metadata = {
      name = "echo-types-bust",
      version = "1.0.0",
      description = "Pure bust declaration for echo-types; explicit host actions discharge probes.",
      paired_xfile = "bust.k9.ncl#declaration",
      paired_runner = "bust.ncl"
    },
    security = {
      leash = 'Yard,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
      signature_required = false
    },
    capabilities = [
    ],
    trident = {
      cardinality = "one per repository",
      runner = "bust.ncl",
      declaration = "bust.k9.ncl#declaration",
      authority = "declaration; root recipes provide execution and receipts"
    }
  },
  declaration = {
    failure_modes = [
      {
        id = "missing-validator",
        description = "Missing standards or Nickel fails validation rather than becoming a pass.",
        class = 'panic,
        injection_probe = "ECHO_STANDARDS_DIR=/nonexistent bash tools/check-metadata.sh",
        recovery_probe = "bash tools/check-metadata.sh",
        status = 'declared,
        notes = "Declared negative control; no recovery duration is asserted."
      }
    ]
  }
}
