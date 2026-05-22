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

*Note: For experimental bridges or retracted claims, refer to the [Proof Obligation Ledger](proof-obligations.md) and [Bridge Status](bridge-status.md).*
