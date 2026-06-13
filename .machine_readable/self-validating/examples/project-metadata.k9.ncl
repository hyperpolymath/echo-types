K9!
# SPDX-License-Identifier: MPL-2.0
# Example Kennel-level K9 component: Project metadata
# Security Level: Kennel (pure data, no execution)
# No signature required

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "project-metadata",
    security = {
      leash = 'Kennel,
      trust_level = "data-only",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
    },
    metadata = {
      name = "project-metadata",
      version = "1.0.0",
      description = "Pure data configuration for project metadata",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # Project configuration
  project = {
    name = "echo-types",
    version = "0.1.0",
    description = "Constructive Agda formalization of fiber-based structured loss (echo types)",

    repository = {
      url = "https://github.com/hyperpolymath/echo-types",
      type = "git",
    },

    author = {
      name = "Jonathan D.A. Jewell",
      email = "j.d.a.jewell@open.ac.uk",
      organization = "hyperpolymath",
    },

    license = "MPL-2.0",

    keywords = [
      "agda",
      "formal-verification",
      "echo-types",
      "rhodium-standard",
      "rsr",
      "hyperpolymath",
    ],
  },

  # Export as JSON for other tools
  export = {
    format = "json",
    destination = "project-metadata.json",
  },
}
