K9!
# SPDX-License-Identifier: MPL-2.0
# Pure declaration; no execution, side effects or signature claim.
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:trust",
    contractile_verb = "trust",
    side_effects = [
    ],
    metadata = {
      name = "echo-types-trust",
      version = "1.0.0",
      description = "Pure trust declaration for echo-types; explicit host actions discharge probes.",
      paired_xfile = "trust.k9.ncl#declaration",
      paired_runner = "trust.ncl"
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
      runner = "trust.ncl",
      declaration = "trust.k9.ncl#declaration",
      authority = "declaration; root recipes provide execution and receipts"
    }
  },
  declaration = {
    verifications = [
      {
        id = "ei-2-record-intact",
        description = "Preserve the EI-2 negative PATH-B record, its superseded readings, and the documented historical/audit qualifications.",
        probe = "bash tools/check-metadata.sh",
        status = 'declared,
        notes = "Migrates the repository-specific pre-estate Trustfile check without restoring A2ML or promoting its stronger historical claims into current proof results."
      },
      {
        id = "assumption-boundary",
        description = "Full-Cubical and postulated roots stay separate from the ordinary aggregate.",
        probe = "just guard",
        status = 'declared
      },
      {
        id = "registry-identity",
        description = "Use recorded fv identity without inventing identifiers or dates.",
        probe = "bash tools/check-metadata.sh",
        status = 'declared
      },
      {
        id = "no-execution-claim",
        description = "Metadata validation never executes embedded probe strings.",
        probe = "bash tools/check-metadata.sh",
        status = 'declared
      }
    ]
  }
}
