# Theorem Index

This document maps foundational theorems and characteristic results to their exact locations in the `proofs/agda/` tree.

## Foundational Core

| Theorem | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `echo-intro` | PROVED | `Echo/Core.agda` | Introduction of an echo from the base point. |
| `map-over` | PROVED | `Echo/Core.agda` | Action on fibers for morphisms over a fixed base. |
| `map-over-comp` | PROVED | `Echo/Core.agda` | Composition law for fiber morphisms. |
| `map-over-id` | PROVED | `Echo/Core.agda` | Identity law for fiber morphisms. |

## Characteristic Results

| Theorem | Status | Module Path | Meaning |
|---------|--------|-------------|---------|
| `collapse-non-injective` | PROVED | `Echo/Characteristic.agda` | Explicit witness of irreversible collapse. |
| `no-section-collapse` | PROVED | `Echo/Characteristic.agda` | Impossibility of inverting the collapse map. |
| `no-section-visible` | PROVED | `Echo/Characteristic.agda` | Impossibility of full reconstruction from visible output alone. |
| `echo-true≢echo-false` | PROVED | `Echo/Characteristic.agda` | Distinct echoes exist over the same visible output. |
| `visible-constraint` | PROVED | `Echo/Characteristic.agda` | Projection-style loss retains a provable constraint on the source. |
| `no-section-collapse-to-residue` | PROVED | `Echo/Residue.agda` | Weakening an echo to a residue discards irrecoverable information. |

## Degrade-law family (aggregate)

The "degrade" results are the per-decoration composition + join laws
demonstrating that loss has *direction* (down-step admissible, up-step
not — the no-section family below is the matching diagonal). All sites
PROVED and pinned in `proofs/agda/Smoke.agda`.

| Site | Module Path |
|------|-------------|
| `degrade-comp`, `degrade-compose`, `degrade-via-join` | `EchoGraded.agda` |
| `degradeMode-comp`, `degradeMode-compose`, `degradeMode-via-join` | `EchoLinear.agda` |
| `applyChoreo-compose` | `EchoChoreo.agda` |
| `degrade-access-comp`, `degrade-access-compose`, `degrade-access-via-join` | `EchoAccess.agda` |
| `degrade-cost-compose` (and family) | `EchoCost.agda` |
| `degrade-search-compose` (and family) | `EchoSearch.agda` |

Separating model (locates the reduction): `EchoSeparating.sep-degrade-compose-fails`
exhibits a checked `true ≢ false` failure when the single load-bearing
hypothesis `≤g-prop` is removed.

See `core/skepticisms/is-this-just-sigma-types.md` §2 and
`docs/echo-types/sigma-distinctness-map.adoc` §"Demand 2" for the
sceptic-facing framing. Honest framing per
`docs/retractions.adoc` R-2026-05-18: this is a *thin-poset reindexing
modality*, not a graded comonad.

## No-section family (aggregate)

The "no-section" results land at six sites across the decoration layers
and are collectively the answer to "raw `Σ` would give `proj₁` for
free". All are pinned in `proofs/agda/Smoke.agda`.

| Site | Module Path |
|------|-------------|
| `no-section-collapse` | `EchoCharacteristic.agda` |
| `no-section-visible` | `EchoCharacteristic.agda` |
| `no-section-collapse-to-residue` | `EchoResidue.agda` |
| `no-section-weaken` | `EchoLinear.agda` |
| `no-section-ordinal-collapse` | `EchoOrdinal.agda` |
| `no-section-to-epistemic` | `EchoEpistemicResidue.agda` |

See `core/skepticisms/is-this-just-sigma-types.md` §1 and
`docs/echo-types/sigma-distinctness-map.adoc` §"Demand 1" for the
sceptic-facing framing.

*Note: For experimental bridges or retracted claims, refer to the [Proof Obligation Ledger](proof-obligations.md) and [Bridge Status](bridge-status.md).*
