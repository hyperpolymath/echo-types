K9!
# SPDX-License-Identifier: MPL-2.0
# Pure declaration; no execution, side effects or signature claim.
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "contractile:must",
    contractile_verb = "must",
    side_effects = [
    ],
    metadata = {
      name = "echo-types-must",
      version = "1.0.0",
      description = "Pure must declaration for echo-types; explicit host actions discharge probes.",
      paired_xfile = "must.k9.ncl#declaration",
      paired_runner = "must.ncl"
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
      runner = "must.ncl",
      declaration = "must.k9.ncl#declaration",
      authority = "declaration; root recipes provide execution and receipts"
    }
  },
  declaration = {
    invariants = [
      {
        id = "ordinary-root",
        description = "Ordinary aggregate checks under its declared safe, without-K profile.",
        probe = "just build",
        status = 'declared,
        severity = 'critical
      },
      {
        id = "proof-roots",
        description = "Check declared proof roots separately with captured results.",
        probe = "just test",
        status = 'declared,
        severity = 'critical
      },
      {
        id = "guards",
        description = "Kernel, invocation and aggregate profile guards pass.",
        probe = "just guard",
        status = 'declared,
        severity = 'critical
      },
      {
        id = "metadata",
        description = "DEED grammar and K9 semantic validation pass against pinned standards.",
        probe = "bash tools/check-metadata.sh",
        status = 'declared,
        severity = 'high
      }
    ]
  }
}
