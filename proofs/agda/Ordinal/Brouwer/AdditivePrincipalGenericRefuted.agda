{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Checked refutation of "additive-principal closure on generic sums".
--
-- The Phase13/RankLexSlice3 design notes flag this as one of two
-- potential unblock routes for the bplus-chain-level extension of
-- the joint-bplus rank-mono primitive — but mark it as "not
-- available", citing that `rank-adm y₁ = ω-rank-pow ν ⊕ rank-pow β`
-- is a generic sum and the existing `additive-principal-ω-rank-pow`
-- only applies to pure ω-powers (single-marker form).  This module
-- promotes that prose claim into a CHECKED REFUTATION: the
-- generic-sum form fails outright at the obvious counterexample
-- (X = Y = ω; α = β = ω).
--
-- Concretely, the hypothesised property
--
--   AdditivePrincipalGenericSum :=
--     ∀ {X Y α β} → α <′ X ⊕ Y → β <′ X ⊕ Y → α ⊕ β <′ X ⊕ Y
--
-- would imply `ω ⊕ ω <′ ω ⊕ ω` (irreflexive ⇒ ⊥) at
-- `X = Y = α = β = olim nat-to-ord (= ω)`.  Both premises
-- `ω <′ ω ⊕ ω` hold (branch 1 of the limit suffices via
-- `osuc (olim f) ≤′ osuc (olim f ⊕ oz) = osuc (olim f)`); the
-- conclusion contradicts `<′-irrefl`.
--
-- Cited by `Ordinal.Buchholz.RankLexSlice3` as the structural
-- blocker for route (a) of its design-note's open follow-on plan.
-- Promoting prose to a named theorem makes the closure-decision
-- auditable.
--
-- ## What lands
--
--   * `AdditivePrincipalGenericSum` — the hypothesised property.
--   * `ω<′ω⊕ω` — `olim nat-to-ord <′ olim nat-to-ord ⊕ olim nat-to-ord`,
--     concretely via branch index 1 in the outer olim.
--   * `additive-principal-generic-sum-refuted` — the headline
--     `¬ AdditivePrincipalGenericSum`.
--
-- ## Headlines (pin in `Smoke.agda`)
--
--   * `AdditivePrincipalGenericSum`
--   * `additive-principal-generic-sum-refuted`

module Ordinal.Brouwer.AdditivePrincipalGenericRefuted where

open import Data.Nat.Base                        using (ℕ; zero; suc)
open import Data.Empty                           using (⊥)
open import Data.Product.Base                    using (_,_)
open import Relation.Nullary                     using (¬_)

open import Ordinal.Brouwer                      using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Arithmetic           using (_⊕_; nat-to-ord)
open import Ordinal.Brouwer.Phase13              using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  )
open import Ordinal.Brouwer.StrictLeftMonoRefuted using (<′-irrefl)

----------------------------------------------------------------------
-- The hypothesised property
----------------------------------------------------------------------

-- "Additive-principal closure on generic sums": if both summands
-- of `α ⊕ β` are strictly below `X ⊕ Y`, then so is the sum.
-- This generalises `additive-principal-ω-rank-pow` (which holds
-- only when the target is a pure ω-power `ω-rank-pow μ`).  REFUTED
-- below.

AdditivePrincipalGenericSum : Set
AdditivePrincipalGenericSum =
  ∀ {X Y α β} → α <′ X ⊕ Y → β <′ X ⊕ Y → α ⊕ β <′ X ⊕ Y

----------------------------------------------------------------------
-- The counterexample witness: ω <′ ω ⊕ ω
----------------------------------------------------------------------

-- The premise `ω <′ ω ⊕ ω` we need to feed to the refutation chain.
-- Concretely: `osuc (olim nat-to-ord) ≤′ olim nat-to-ord ⊕ olim
-- nat-to-ord = olim (λ n → olim nat-to-ord ⊕ nat-to-ord n)`.
-- The `osuc (olim f) ≤′ olim g` clause of `_≤′_` reduces to
-- `Σ ℕ (λ n → osuc (olim f) ≤′ g n)`; we pick branch n = 1.
--
-- At n = 1: `g 1 = olim nat-to-ord ⊕ nat-to-ord 1
--                = olim nat-to-ord ⊕ osuc oz
--                = osuc (olim nat-to-ord ⊕ oz)
--                = osuc (olim nat-to-ord)` (all definitional).
-- So we need `osuc (olim nat-to-ord) ≤′ osuc (olim nat-to-ord)`,
-- which is `≤′-refl`.

ω<′ω⊕ω : olim nat-to-ord <′ olim nat-to-ord ⊕ olim nat-to-ord
ω<′ω⊕ω = suc zero , ≤′-refl {olim nat-to-ord}

----------------------------------------------------------------------
-- The headline refutation
----------------------------------------------------------------------

-- Instantiating the hypothesised property at X = Y = α = β = ω
-- yields `ω ⊕ ω <′ ω ⊕ ω`; `<′-irrefl` (from the (b) refutation
-- module) refutes it.  Both premises are `ω<′ω⊕ω`.

additive-principal-generic-sum-refuted : ¬ AdditivePrincipalGenericSum
additive-principal-generic-sum-refuted apgs =
  <′-irrefl {olim nat-to-ord ⊕ olim nat-to-ord}
    (apgs {olim nat-to-ord} {olim nat-to-ord}
          {olim nat-to-ord} {olim nat-to-ord}
          ω<′ω⊕ω ω<′ω⊕ω)
