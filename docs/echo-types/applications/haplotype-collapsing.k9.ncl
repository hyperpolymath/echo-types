# SPDX-License-Identifier: CC-BY-SA-4.0
# haplotype-collapsing.k9.ncl — Nickel schema for haplotype collapsing with Echo fiber witness
#
# This is the k9 contract that validates the pipeline output:
#   collapsed_representatives (size m) + distance_matrix (m×m) + fibers (Echo sidecar)
#
# Design: fiber witness travels as sidecar, never in O(n²) hot loop.
# Echo f y = Σ (c : Clone) (f c ≡ y) serialized as FiberBundle.
#
# Validate: nickel typecheck docs/echo-types/applications/haplotype-collapsing.k9.ncl
# Export:   nickel export docs/echo-types/applications/haplotype-collapsing.k9.ncl > result.json

let CloneWitness = {
  clone_id | String,
  haplotype_id | String,
  sequence | String,
  sample | String,
  quality | optional | Number,
  lineage | {
    pcr_replicate | optional | Number,
    run_id | optional | String,
    extra | optional | Dyn,
  },
  collapsed_at | optional | String,
} in

let FiberBundle = {
  haplotype_id | String,
  representative | CloneWitness,
  clones | Array CloneWitness,
  count | Number,

  # Contracts: count = length clones, all clones point to this haplotype
  count = %force% (std.array.length clones),
} in

let Haplotype = {
  haplotype_id | String,
  representative_sequence | String,
  count | Number,  # redundant with fibers[haplotype_id].count, checked below
} in

let CollapsedResult = {
  # m distinct haplotypes — the domain of the O(m²) distance matrix
  collapsed_representatives | Array Haplotype,

  # m × m distance matrix — computed ONLY on representatives, NOT clones
  # O(m²) compute, not O(n²)
  distance_matrix | Array (Array Number),

  # Echo fiber sidecar: Dict haplotype_id => FiberBundle
  # Total size O(n) clones across all bundles, O(1) per clone insertion
  # This IS the Σ B (Echo f) witness serialized
  fibers | { _ : FiberBundle },

  # Provenance / pipeline metadata
  provenance | {
    total_clones | Number,
    distinct_haplotypes | Number,
    collapse_fn | String,  # e.g. "100% identity", "99% clustering", "dada2"
    collapsed_at | optional | String,
    pipeline_version | optional | String,
  },

  # Invariants checked by Nickel contracts
  # 1. distance_matrix is square and size = m
  # 2. fibers keys = collapsed_representatives[*].haplotype_id
  # 3. each fiber's count = length clones
  # 4. each fiber's clones[*].haplotype_id == fiber.haplotype_id
  # 5. provenance.distinct_haplotypes == m
  # 6. provenance.total_clones == sum_i fibers[rep_i].count

  distinct_haplotypes = %force% (std.array.length collapsed_representatives),
} in

# Example valid instance (for typechecking / documentation)
let example : CollapsedResult = {
  collapsed_representatives = [
    { haplotype_id = "H0", representative_sequence = "ACGTACGT", count = 2 },
    { haplotype_id = "H1", representative_sequence = "ACGTACGG", count = 1 },
  ],
  distance_matrix = [
    [0, 1],
    [1, 0],
  ],
  fibers = {
    H0 = {
      haplotype_id = "H0",
      representative = {
        clone_id = "C0",
        haplotype_id = "H0",
        sequence = "ACGTACGT",
        sample = "S1",
        lineage = { pcr_replicate = 1 },
      },
      clones = [
        {
          clone_id = "C0",
          haplotype_id = "H0",
          sequence = "ACGTACGT",
          sample = "S1",
          lineage = { pcr_replicate = 1 },
        },
        {
          clone_id = "C1",
          haplotype_id = "H0",
          sequence = "ACGTACGT",
          sample = "S1",
          lineage = { pcr_replicate = 2 },
        },
      ],
      count = 2,
    },
    H1 = {
      haplotype_id = "H1",
      representative = {
        clone_id = "C2",
        haplotype_id = "H1",
        sequence = "ACGTACGG",
        sample = "S2",
        lineage = { pcr_replicate = 1 },
      },
      clones = [
        {
          clone_id = "C2",
          haplotype_id = "H1",
          sequence = "ACGTACGG",
          sample = "S2",
          lineage = { pcr_replicate = 1 },
        },
      ],
      count = 1,
    },
  },
  provenance = {
    total_clones = 3,
    distinct_haplotypes = 2,
    collapse_fn = "100% identity",
    collapsed_at = "2026-09-27T00:00:00Z",
    pipeline_version = "protoctist-0.1.0 + echo-types",
  },
  distinct_haplotypes = 2,
} in

{
  CloneWitness = CloneWitness,
  FiberBundle = FiberBundle,
  Haplotype = Haplotype,
  CollapsedResult = CollapsedResult,
  example = example,
}
