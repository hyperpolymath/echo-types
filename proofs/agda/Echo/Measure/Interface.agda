{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo.Measure.Interface — the residue-measure SEAM.
--
-- This module defines how an external resource algebra may *measure*
-- Echo residues WITHOUT becoming part of Echo core. It is the
-- decorating/observation boundary named in `FOUNDATION_CONTRACT.md`:
--
--   * `Echo.Measure.*` MAY depend on order / resource interfaces.
--   * `Echo.Modality.Core` / `Echo.Modality.Interface` MUST NOT.
--
-- A `ResidueMeasure` consumes an `EchoModality` (the proof-relevant
-- Echo structure) plus an `OrderedCarrier` (a minimal ordered target,
-- the place a resource-algebra value lives) and packages a `measure`
-- map together with a `monotone` law. It OBSERVES the modality; it
-- never defines it. Per the boundary invariant, equal residue measure
-- does not imply equal Echo (see
-- `Echo.Separation.NotResourceInstance`).
--
-- Local ordered carrier, by design. Rather than importing a concrete
-- semiring / resource-algebra interface (which would pull a heavier
-- dependency into the measure layer), the target is the MINIMAL local
-- `OrderedCarrier` interface: a carrier with a reflexive-transitive
-- order. Semiring-valued measures (cost monoids, tropical min-plus,
-- probability) are downstream REFINEMENTS that supply an
-- `OrderedCarrier` view of their carrier — see `Echo.Measure.Examples`.

module Echo.Measure.Interface where

open import Level using (Level; suc; _⊔_)

open import Echo.Modality.Interface using (ThinPoset; EchoModality)

----------------------------------------------------------------------
-- The minimal ordered-carrier target.
--
-- Just enough structure to state a monotone measure: a carrier and a
-- reflexive, transitive order. A resource algebra (ordered
-- commutative monoid, tropical semiring, probability/confidence
-- lattice, …) yields one of these by forgetting down to its order;
-- the extra algebraic structure is not needed to state the seam.
----------------------------------------------------------------------

record OrderedCarrier (ℓc ℓr : Level) : Set (suc (ℓc ⊔ ℓr)) where
  field
    Carrier  : Set ℓc
    _≤_      : Carrier → Carrier → Set ℓr
    ≤-refl   : ∀ {x}     → x ≤ x
    ≤-trans  : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

----------------------------------------------------------------------
-- The residue-measure seam.
--
-- Given an `EchoModality E` over a thin echo index `P`, and an
-- ordered carrier `R`, a `ResidueMeasure E R` is:
--
--   * `measure`  : observe the residue at any index as a value in `R`;
--   * `monotone` : degrading along the index order does not decrease
--                  the measured residue. (Variance choice, made
--                  explicit: `measure x ≤R measure (degrade p x)` — a
--                  *loss/cost* reading, where degradation accumulates
--                  measured residue. A *confidence* reading uses the
--                  opposite order on `R`; both are expressible by
--                  choosing the `OrderedCarrier` order — see Examples.)
--
-- `measure` and `monotone` are the WHOLE seam. There is deliberately
-- no field forcing `measure` to be injective or to reconstruct the
-- residue: a measure is a lossy observation, never a definition of
-- Echo.
----------------------------------------------------------------------

record ResidueMeasure
  {ℓi ℓr ℓc : Level} {P : ThinPoset ℓi ℓr} (E : EchoModality P ℓc)
  {ℓm ℓo : Level} (R : OrderedCarrier ℓm ℓo)
  : Set (ℓi ⊔ ℓr ⊔ ℓc ⊔ ℓm ⊔ ℓo) where
  open ThinPoset P
  open EchoModality E
  open OrderedCarrier R renaming (Carrier to RC; _≤_ to _≤R_)
  field
    measure  : ∀ {i} → ⟦ i ⟧ → RC
    monotone : ∀ {i j} (p : i ≤ j) (x : ⟦ i ⟧) →
               measure x ≤R measure (degrade p x)
