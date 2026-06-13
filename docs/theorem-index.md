<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Theorem Index

This document maps foundational theorems and characteristic results
to their exact locations in the `proofs/agda/` tree.

**Authoritative sources.** `proofs/agda/Smoke.agda` is the
machine-checked headline manifest (every name below is pinned there
under a `using` block); `docs/echo-types/MAP.adoc` is the
content/architecture map. This file is the human-readable index;
when in doubt, prefer Smoke.agda + MAP.adoc.

## Foundational Core

| Theorem | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `echo-intro` | PROVED | `proofs/agda/Echo.agda` | Introduction of an echo from the base point. |
| `map-over` | PROVED | `proofs/agda/Echo.agda` | Action on fibers for morphisms over a fixed base. |
| `map-over-comp` | PROVED | `proofs/agda/Echo.agda` | Composition law for fiber morphisms. |
| `map-over-id` | PROVED | `proofs/agda/Echo.agda` | Identity law for fiber morphisms. |
| `map-square` | PROVED | `proofs/agda/Echo.agda` | Action along a commuting square. |
| `Echo-comp-iso` | PROVED | `proofs/agda/Echo.agda` | Composition-accumulation iso (packaged `↔`). |
| `cancel-iso` | PROVED | `proofs/agda/Echo.agda` | Cancellation iso through a section (with explicit triangle identities). |

## Characteristic Results

| Theorem | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `collapse-non-injective` | PROVED | `proofs/agda/EchoCharacteristic.agda` | Explicit witness of irreversible collapse. |
| `no-section-collapse` | PROVED | `proofs/agda/EchoCharacteristic.agda` | Impossibility of inverting the collapse map. |
| `no-section-visible` | PROVED | `proofs/agda/EchoCharacteristic.agda` | Impossibility of full reconstruction from visible output alone. |
| `echo-true≢echo-false` | PROVED | `proofs/agda/EchoCharacteristic.agda` | Distinct echoes exist over the same visible output. |
| `visible-constraint` | PROVED | `proofs/agda/EchoCharacteristic.agda` | Projection-style loss retains a provable constraint on the source. |
| `no-section-collapse-to-residue` | PROVED | `proofs/agda/EchoResidue.agda` | Weakening an echo to a residue discards irrecoverable information. |

## Canonical identity layer (2026-05-27)

Tier 1 — the canonical-identity-layer named theorems:

| Theorem | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `A↔ΣEcho` | PROVED | `proofs/agda/EchoTotalCompletion.agda` | The slogan-unlock: `A ≃ Σ B (Echo f)`. |
| `ofs-witness` | PROVED | `proofs/agda/EchoOrthogonalFactorizationSystem.agda` | The (equivalence, projection) OFS witness at the K-free level. |
| `Image` / `image-factor-{left,right,commutes}` | PROVED | `proofs/agda/EchoImageFactorization.agda` | Image factorisation in Echo language. |
| `no-section-of-collapsing-map` | PROVED | `proofs/agda/EchoNoSectionGeneric.agda` | Structural lift: any collapsing map with distinguishable collapsing pair admits no section. |

Tier 2 — the classification grid (kinds-of-loss × shapes-of-residue):

| Theorem / Record | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `HasInverse` + EQUIV/INJ/SURJ/CONST theorems | PROVED | `proofs/agda/EchoLossTaxonomy.agda` | Function-side four-axis classification. |
| `ResidueForm` + four instances | PROVED | `proofs/agda/EchoResidueTaxonomy.agda` | Per-output residue carrier + lowering shape. |
| `DecorationStructure` + four instances + `DegradeAbstract` | PROVED | `proofs/agda/EchoDecorationStructure.agda` | Seven-field decoration recipe + abstract degrade-compose. |
| `_≡m_` + `mode-equality-strictly-finer-at-linear` | PROVED | `proofs/agda/EchoObservationalEquivalence.agda` | Mode-indexed observational equality on `LEcho`. |

Tier 3 / Pillar F Gate F5 FULL PASS (qualified OFS earn-back, funext-qualified, never postulated):

| Theorem | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `echo-factorisation-strict` | PROVED (funext) | `proofs/agda/EchoOFSUnivF5.agda` | F5-1: function-level factorisation triangle. |
| Diagonal lifting (`module Pointwise` + `module Strict`) | PROVED | `proofs/agda/EchoOFSUnivF5Diag.agda` | F5-2: diagonal lifting property. |
| Factorisation uniqueness up to iso (`module Pointwise` + `module Strict`) | PROVED | `proofs/agda/EchoOFSUnivF5Iso.agda` | F5-3: factorisation uniqueness via composition design. |

Audience-facing modules (Tier 3 audience moves; each ships record + parametric headline theorems + worked instance + honest-bound matched-negatives):

| Module | Audience | Worked Instance |
|--------|----------|-----------------|
| `EchoProvenance.agda` | Database / lineage / K-provenance | `bool-over-nat-provenance` |
| `EchoSecurity.agda` | Region-exit / capability-flow (generalises `tutorial/region_exit_audit/`) | `region-exit-audit-instance` |
| `EchoProbabilisticSupport.agda` | Sampling / draw-id (NOT measure-theoretic probability) | `bool-indexed-nat-sampling` |
| `EchoDifferential.agda` | Sensitivity / perturbation tracking (NOT ε-DP) | `bool-perturbed-nat-sensitivity` |

Cementing matched-negatives:

| Theorem | Module Path | Meaning |
|---------|-------------|---------|
| `entropy-shadow-blind` + `witness-distinguishes-where-entropy-cannot` | `proofs/agda/EchoEntropy.agda` | Shannon-entropy shadow is blind where Echo distinguishes. |
| `gap-paired` (`ll-encoding-gap` + `source-no-section`) | `proofs/agda/EchoLLEncoding.agda` | LL `!A := 1` shadow has a section that Echo provably lacks. |

Curated single-file entry point: `proofs/agda/EchoCanonicalIdentitySuite.agda` re-exports every load-bearing headline above under the suite-side index.

## Degrade-law family (aggregate)

The "degrade" results are the per-decoration composition + join laws
demonstrating that loss has *direction* (down-step admissible, up-step
not — the no-section family below is the matching diagonal). All sites
PROVED and pinned in `proofs/agda/Smoke.agda`.

| Site | Module Path |
|------|-------------|
| `degrade-comp`, `degrade-compose`, `degrade-via-join` | `proofs/agda/EchoGraded.agda` |
| `degradeMode-comp`, `degradeMode-compose`, `degradeMode-via-join` | `proofs/agda/EchoLinear.agda` |
| `applyChoreo-compose` | `proofs/agda/EchoChoreo.agda` |
| `degrade-access-comp`, `degrade-access-compose`, `degrade-access-via-join` | `proofs/agda/EchoAccess.agda` |
| `degrade-cost-compose` (and family) | `proofs/agda/EchoCost.agda` |
| `degrade-search-compose` (and family) | `proofs/agda/EchoSearch.agda` |
| **`DegradeAbstract.degrade-compose-abstract`** (carrier-side abstract; closes the per-module recipes once over the `DecorationStructure` record) | `proofs/agda/EchoDecorationStructure.agda` |

Separating model (locates the reduction): `EchoSeparating.sep-degrade-compose-fails`
exhibits a checked `true ≢ false` failure when the single load-bearing
hypothesis `≤g-prop` is removed.

See `core/skepticisms/is-this-just-sigma-types.md` §2 and
`docs/echo-types/sigma-distinctness-map.adoc` §"Demand 2" for the
sceptic-facing framing. Honest framing per
`docs/retractions.adoc` R-2026-05-18: this is a *thin-poset reindexing
modality*, not a graded comonad.

## No-section family (aggregate)

The "no-section" results land at multiple sites across the decoration
layers and are collectively the answer to "raw `Σ` would give `proj₁`
for free". All are pinned in `proofs/agda/Smoke.agda`.

| Site | Module Path |
|------|-------------|
| `no-section-collapse` | `proofs/agda/EchoCharacteristic.agda` |
| `no-section-visible` | `proofs/agda/EchoCharacteristic.agda` |
| `no-section-collapse-to-residue` | `proofs/agda/EchoResidue.agda` |
| `no-section-weaken` | `proofs/agda/EchoLinear.agda` |
| `no-section-ordinal-collapse` | `proofs/agda/EchoOrdinal.agda` |
| `no-section-to-epistemic` | `proofs/agda/EchoEpistemicResidue.agda` |
| **`no-section-of-collapsing-map`** (structural lift covering all of the above) | `proofs/agda/EchoNoSectionGeneric.agda` |
| **`no-section-when-non-injective-at-y`** (Echo-specific corollary) | `proofs/agda/EchoNoSectionGeneric.agda` |
| **`audit-no-recovery-at`** (per-region instance, factored through `no-section-of-collapsing-map`) | `proofs/agda/EchoSecurity.agda` |

See `core/skepticisms/is-this-just-sigma-types.md` §1 and
`docs/echo-types/sigma-distinctness-map.adoc` §"Demand 1" for the
sceptic-facing framing.

## Pillar F gate ledger

| Gate | Status | Module Path | Date |
|------|--------|-------------|------|
| F1 — Graded-comonad witness (make-or-break) | PASSED | `proofs/agda/EchoGradedComonadF1.agda` | 2026-05-20 |
| F2 — Echo functor second model | PASSED | `proofs/agda/EchoStepNDModelF2.agda` | 2026-05-18 |
| F3 — Independent second graded-comonad model | PASSED | `proofs/agda/EchoGradedComonadInstance{1,2}.agda` | 2026-05-20 |
| F4 — Funext-qualified pullback universal property | PASSED | `proofs/agda/EchoPullbackUnivF4.agda` | 2026-05-18 |
| F5 — Funext-qualified full OFS (three slices) | PASSED | `proofs/agda/EchoOFSUnivF5{,Diag,Iso}.agda` | 2026-05-27 |

Gate ledger: `docs/echo-types/earn-back-plan.adoc`.
Retraction follow-ups: `docs/retractions.adoc` (R-2026-05-18 + F-2026-05-18a + F-2026-05-20a/b + F-2026-05-27a).

*Note: For experimental bridges or retracted claims, refer to the [Proof Obligation Ledger](proof-obligations.md) and [Bridge Status](bridge-status.md).*
