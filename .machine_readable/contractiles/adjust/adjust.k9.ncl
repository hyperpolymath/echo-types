K9!
# SPDX-License-Identifier: MPL-2.0
# Pure declaration; no execution, side effects or signature claim.
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:adjust",
    contractile_verb = "adjust",
    side_effects = [
    ],
    metadata = {
      name = "echo-types-adjust",
      version = "1.0.0",
      description = "Pure adjust declaration for echo-types; explicit host actions discharge probes.",
      paired_xfile = "adjust.k9.ncl#declaration",
      paired_runner = "adjust.ncl"
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
      runner = "adjust.ncl",
      declaration = "adjust.k9.ncl#declaration",
      authority = "declaration; root recipes provide execution and receipts"
    }
  },
  declaration = {
    requirements = [
      {
        id = "proof-drift",
        description = "Proof-root membership changes require inventory refresh and all root checks.",
        probe = "just audit-inventory && just test",
        status = 'declared,
        notes = "Zero tolerance for silently changing the ordinary theory profile."
      },
      {
        id = "metadata-drift",
        description = "A standards revision change requires review, pin update and semantic validation.",
        probe = "bash tools/check-metadata.sh",
        status = 'declared,
        notes = "Declare adoption only after the new gates actually run."
      }
    ]
  }
}
