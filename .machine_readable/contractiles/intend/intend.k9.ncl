K9!
# SPDX-License-Identifier: MPL-2.0
# Pure declaration; no execution, side effects or signature claim.
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:intend",
    contractile_verb = "intend",
    side_effects = [
    ],
    metadata = {
      name = "echo-types-intend",
      version = "1.0.0",
      description = "Pure intend declaration for echo-types; explicit host actions discharge probes.",
      paired_xfile = "intend.k9.ncl#declaration",
      paired_runner = "intend.ncl"
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
      runner = "intend.ncl",
      declaration = "intend.k9.ncl#declaration",
      authority = "declaration; root recipes provide execution and receipts"
    }
  },
  declaration = {
    intents = [
      {
        id = "metadata-reconciliation",
        description = "Collect canonical grammar and semantic validator receipts.",
        probe = "bash tools/check-metadata.sh",
        status = 'declared
      },
      {
        id = "proof-receipts",
        description = "Keep proof roots and assumption boundaries independently reviewable.",
        probe = "just test",
        status = 'declared
      }
    ],
    wishes = [
    ]
  }
}
