{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo.Index.ThinPoset — the stable exported interface for the *echo
-- index*: the thin poset/order of retention-vs-degradation that the
-- Echo modality is indexed by.
--
-- This is one of the four curated public-surface modules of the Echo
-- foundation (see `FOUNDATION_CONTRACT.md`). It names, under a stable
-- API, the *index axis* of the residual modality — and ONLY the index
-- axis. It carries:
--
--   * the abstract `ThinPoset` record (carrier `Ix`, order `_≤_`,
--     reflexivity, transitivity, and *thinness* — propositionality of
--     order proofs) that downstream languages (e.g. my-lang)
--     instantiate;
--
--   * the canonical concrete instance `grade-thinPoset` over the
--     three-point loss order `keep ≤ residue ≤ forget`, re-exported
--     verbatim from the proven `EchoGraded` module so there is a
--     SINGLE source of truth for the order — the same order that
--     `Echo.Modality.Core.degrade` acts over.
--
-- VOCABULARY (see `FOUNDATION_CONTRACT.md`). The inhabitants of `Ix`
-- are *echo indices*, NOT *resource grades*. An echo index lives on
-- the thin-poset retention axis of the Echo modality; a resource
-- grade lives on the semiring/resource-algebra axis. They are
-- orthogonal. This module touches only the echo-index axis.
--
-- MEASURE-INDEPENDENCE INVARIANT. This module imports NO semiring /
-- resource-algebra machinery (it imports `EchoGraded`, whose own cone
-- is stdlib-only). The echo index is defined without reference to any
-- residue *measure*; measures are a downstream observation seam
-- (`Echo.Measure.Interface`), never part of the index.

module Echo.Index.ThinPoset where

open import Level using (Level; suc; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

----------------------------------------------------------------------
-- The abstract echo-index interface.
--
-- A `ThinPoset` is a poset whose order is *thin* (a.k.a.
-- propositional / a preorder that is moreover a poset-of-truth-
-- values on each hom): any two proofs of `i ≤ j` are equal. Thinness
-- is the load-bearing hypothesis behind `degrade-compose`
-- (path-independence of degradation); the separating model in
-- `Echo.Separation.NotResourceInstance` shows that dropping thinness
-- breaks composition, so the field is not cosmetic.
--
-- Downstream consumers instantiate this record at their own index
-- type. The canonical inhabitant `grade-thinPoset` is provided below.
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
