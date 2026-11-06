K9!
# SPDX-License-Identifier: MPL-2.0
# Pure declaration; no execution, side effects or signature claim.
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:dust",
    contractile_verb = "dust",
    side_effects = [
    ],
    metadata = {
      name = "echo-types-dust",
      version = "1.0.0",
      description = "Pure dust declaration for echo-types; explicit host actions discharge probes.",
      paired_xfile = "dust.k9.ncl#declaration",
      paired_runner = "dust.ncl"
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
      runner = "dust.ncl",
      declaration = "dust.k9.ncl#declaration",
      authority = "declaration; root recipes provide execution and receipts"
    }
  },
  declaration = {
    removal_candidates = [
      {
        id = "retired-a2ml",
        description = "Keep retired A2ML records absent.",
        target = ".machine_readable/6a2/*.a2ml",
        reason = "Owner retirement on 2026-09-30; successor descriptions live in the root chora.",
        probe = "bash tools/check-metadata.sh",
        status = 'removed,
        notes = "History remains at Git tree 39a7a99cbe19a918843e9624010510b5fc3b8366."
      },
      {
        id = "duplicate-k9-mirror",
        description = "Retire files from the duplicate svc/k9 mirror.",
        target = ".machine_readable/svc/k9/",
        reason = "One active self-validating tree prevents mirror drift.",
        probe = "bash tools/check-metadata.sh",
        status = 'removed,
        notes = "Empty untracked directories may remain on Windows; prior files remain in Git history."
      }
    ]
  }
}
