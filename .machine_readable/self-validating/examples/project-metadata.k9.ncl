K9!
# SPDX-License-Identifier: MPL-2.0
{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "project-metadata",
    metadata = {
      name = "echo-types-project-metadata",
      version = "1.0.0",
      description = "Source-true identity; project release version deliberately omitted."
    },
    security = {
      leash = 'Kennel,
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
      signature_required = false
    },
    capabilities = [
    ]
  },
  project = {
    name = "echo-types",
    repository = "https://github.com/hyperpolymath/echo-types",
    clade = "fv",
    prefixed_name = "fv-echo-types",
    uuid_v8 = "081ce0dd-51b8-80de-916a-f4593d7bbfbd",
    identity_source = "gv-clade-index@2cfabd15d6cb966ed369ee13aa7174b960f45abd:worker/data/repos.json",
    description = "Constructive Agda formalization of fiber-based structured loss.",
    code_license = "MPL-2.0",
    documentation_license = "Per-file notices; see docs/audit/2026-11-06-license-inventory.adoc"
  }
}
