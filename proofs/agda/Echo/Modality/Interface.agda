{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo.Modality.Interface — the ABSTRACT Echo-modality contract,
-- parameterised over an arbitrary echo index (`ThinPoset`).
--
-- This is the object a downstream language (e.g. my-lang) instantiates
-- to obtain "an Echo modality of its own". It is split out from
-- `Echo.Modality.Core` so that the record's field projections
-- (`degrade`, `degrade-id`, `degrade-compose`) live in their own
-- namespace and do not collide with the concrete same-named operations
-- that `Echo.Modality.Core` re-exports from `EchoGraded`.
--
-- MEASURE-INDEPENDENCE INVARIANT. No semiring / resource-algebra
-- import. The modality is specified purely in terms of the thin echo
-- index and propositional equality. A residue *measure* is a SEPARATE
-- record (`Echo.Measure.Interface`) that observes an inhabitant of
-- this one; it is never a field here.
--
--   Echo IS-NOT a resource instance.

module Echo.Modality.Interface where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Echo.Index.ThinPoset public

----------------------------------------------------------------------
-- The abstract Echo-modality interface, over an arbitrary echo index.
--
-- Supply a `ThinPoset` index `P` and an `EchoModality P ℓc`: an
-- index-graded carrier `⟦_⟧` with a `degrade` reindexing action
-- satisfying the unit and path-independence laws. This is the
-- proof-relevant residual modality, parameterised so it can be
-- instantiated at the consumer's own fibration — WITHOUT committing
-- to any measure.
--
-- The fields ARE what the foundation contract means by "Echo core":
-- a residue *measure* observes a value of this record; it is never
-- one of these fields.
----------------------------------------------------------------------

record EchoModality
  {ℓi ℓr : Level} (P : ThinPoset ℓi ℓr) (ℓc : Level)
  : Set (suc (ℓi ⊔ ℓr ⊔ ℓc)) where
  open ThinPoset P
  field
    -- The index-graded residual carrier: `⟦ i ⟧` is the Echo residue
    -- retained at echo index `i`.
    ⟦_⟧ : Ix → Set ℓc
    -- Reindexing along the index order: degrade a residue from a
    -- more-retained index to a less-retained one.
    degrade : ∀ {i j} → i ≤ j → ⟦ i ⟧ → ⟦ j ⟧
    -- Unit law: degrading along a reflexive arrow is the identity.
    degrade-id :
      ∀ {i} (p : i ≤ i) (x : ⟦ i ⟧) → degrade p x ≡ x
    -- Path-independence (the characteristic law): every factoring of
    -- an index transition gives the same degraded residue. Carried by
    -- thinness of the index — see Echo.Separation.NotResourceInstance.
    --
    -- This single law subsumes the concrete `EchoGraded.degrade-comp`
    -- (associativity along ONE chosen factoring): under a thin index,
    -- `r` is forced equal to `≤-trans p q`, so path-independence and
    -- associativity coincide. We keep only `degrade-compose` as a
    -- field; a downstream instance whose index is genuinely thin gets
    -- associativity for free, and one whose index is NOT thin should
    -- not be an `EchoModality` at all (see the separating model).
    degrade-compose :
      ∀ {i j k} (p : i ≤ j) (q : j ≤ k) (r : i ≤ k) (x : ⟦ i ⟧) →
      degrade q (degrade p x) ≡ degrade r x
