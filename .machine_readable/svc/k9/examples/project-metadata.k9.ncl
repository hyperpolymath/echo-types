K9!
# SPDX-License-Identifier: MPL-2.0
# Kennel-level K9 component: echo-types project metadata
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
      name = "echo-types-project-metadata",
      version = "1.0.0",
      description = "Pure data configuration for the echo-types proof library",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  project = {
    name = "echo-types",
    id = "org.hyperpolymath.echo-types",
    version_target = "0.1.1",
    description = "Constructive Agda formalisation of fiber-based structured loss (\"echo types\"): Echo f y := Σ (x : A) , (f x ≡ y).",

    repository = {
      url = "https://github.com/hyperpolymath/echo-types",
      type = "git",
      canonical_forge = "github",
      mirrors = ["gitlab", "codeberg"],
    },

    author = {
      name = "Jonathan D.A. Jewell",
      email = "j.d.a.jewell@open.ac.uk",
      organization = "hyperpolymath",
    },

    license = "MPL-2.0",

    proof_discipline = {
      checker = "agda",
      agda_min = "2.6.3",
      stdlib_min = "2.3",
      flags = ["--safe", "--without-K"],
      postulates_load_bearing = 0,
      verified_suite = "proofs/agda/All.agda",
      headline_pins = "proofs/agda/Smoke.agda",
      kernel_cone_guard = "scripts/kernel-guard.sh",
    },

    workstreams = [
      "composition-track (Echo-comp-iso, cancel-iso, pentagon) — landed",
      "ordinal-track (Buchholz, target Bachmann-Howard psi_0(Omega_omega)) — partial",
      "establishment-track (reindexing modality of structured loss, Pillars A-F) — Pillars A-D + F closed; Pillar E open",
    ],

    keywords = [
      "agda",
      "homotopy-type-theory",
      "fiber",
      "structured-loss",
      "graded-comonad",
      "ordinal-notation",
      "rhodium-standard",
      "hyperpolymath",
    ],

    # Registry-assigned; not yet known. Do not fabricate.
    clade = "TODO: assign via gv-clade-index registry",
  },

  export = {
    format = "json",
    destination = "project-metadata.json",
  },
}
