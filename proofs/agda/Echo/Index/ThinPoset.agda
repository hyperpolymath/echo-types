{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Public echo-index interface. The legacy name ThinPoset is retained for
-- compatibility; its fields express a thin preorder, without antisymmetry.
-- EchoThinPreorderExample exhibits distinct mutually reachable indices.
-- Thinness proves independence from the choice of arrows. Ordinary action
-- composition only requires chosen composition and its functor law.
-- Echo indices describe retention/degradation, independently of resource
-- measures and semiring grades. The concrete grade-thinPoset is exported
-- below; Echo.Modality.Core supplies the modality action.

module Echo.Index.ThinPoset where

open import Level using (Level; suc; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

----------------------------------------------------------------------
-- Legacy interface for a thin preorder: reflexive, transitive, and with
-- proposition-valued homs. No antisymmetry or object equality is asserted.
----------------------------------------------------------------------

record ThinPoset (ℓi ℓr : Level) : Set (suc (ℓi ⊔ ℓr)) where
  field
    Ix      : Set ℓi
    _≤_     : Ix → Ix → Set ℓr
    ≤-refl  : ∀ {i}     → i ≤ i
    ≤-trans : ∀ {i j k} → i ≤ j → j ≤ k → i ≤ k
    -- Thinness / propositionality of the order. This IS the property
    -- that makes the index "thin": each hom `i ≤ j` is a singleton.
    ≤-thin  : ∀ {i j} (p q : i ≤ j) → p ≡ q

----------------------------------------------------------------------
-- The canonical concrete echo index: the three-point loss order.
--
-- Re-exported verbatim from `EchoGraded`. `keep ≤ residue ≤ forget`
-- is the retention axis: `keep` retains the full proof-relevant
-- witness, `residue` keeps a certified residue, `forget` discards it.
-- We re-export ONLY the order pieces — NOT `GEcho` / `degrade`, which
-- belong to the modality layer (`Echo.Modality.Core`).
----------------------------------------------------------------------

open import EchoGraded public
  using ( Grade ; keep ; residue ; forget
        ; _≤g_
        ; keep≤keep ; keep≤residue ; keep≤forget
        ; residue≤residue ; residue≤forget ; forget≤forget
        ; ≤g-trans
        ; ≤g-prop
        ; _⊔g_ ; ⊔g-assoc
        ; ≤g-⊔g-left ; ≤g-⊔g-right ; ≤g-⊔g-univ
        )

-- Reflexivity of the concrete loss order. `EchoGraded` derives
-- transitivity and thinness but leaves reflexivity implicit in the
-- constructors; the stable interface needs it as a named arrow, so
-- we expose it here (one line per grade).
≤g-refl : ∀ {g : Grade} → g ≤g g
≤g-refl {keep}    = keep≤keep
≤g-refl {residue} = residue≤residue
≤g-refl {forget}  = forget≤forget

----------------------------------------------------------------------
-- The canonical instance, packaged as a `ThinPoset`.
--
-- This witnesses that the abstract interface is inhabitable and pins
-- the concrete loss order as the reference echo index. Downstream
-- code that wants "the echo index echo-types ships" uses this; code
-- that wants "an echo index of my own" instantiates `ThinPoset`.
----------------------------------------------------------------------

grade-thinPoset : ThinPoset 0ℓ 0ℓ
grade-thinPoset = record
  { Ix      = Grade
  ; _≤_     = _≤g_
  ; ≤-refl  = ≤g-refl
  ; ≤-trans = ≤g-trans
  ; ≤-thin  = ≤g-prop
  }
