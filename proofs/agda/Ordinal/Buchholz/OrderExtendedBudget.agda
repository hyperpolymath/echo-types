{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Budgeted shared-binder closure on the K-restricted extended order.
--
-- Mirrors `Ordinal.Buchholz.RecursiveSurfaceBudget`'s strategy but
-- for the depth-1 `_<ᵇ⁺_` relation defined in
-- `Ordinal.Buchholz.OrderExtended`. Because every `<ᵇ⁺` derivation
-- has a single (immediate) inner step (either `<ᵇ` via `<ᵇ⁺-base`
-- or `<ᵇ` carried by the two shared-binder lex constructors
-- `<ᵇ⁺-ψα` / `<ᵇ⁺-+2`), the budget consumption collapses to
-- "every `<ᵇ⁺` step costs `suc`" — no derivation-depth extraction
-- needed (cf. `<ᵇʳᶠ-depth` in `RecursiveSurfaceBudget`, which
-- threads the recursive same-binder depth).
--
-- This is the budgeted analogue of `wf-<ᵇ⁺_`, which is OPEN per
-- `docs/echo-types/buchholz-extended-wf.md`. Carrying the budget
-- alongside `BT` exposes a well-founded carrier for the shared-
-- binder shapes (`<ᵇ⁺-ψα`, `<ᵇ⁺-+2`) even before the unbudgeted
-- theorem lands. Downstream consumers that need only the depth-
-- stratified order (e.g. `IteratedExtendedOrder` step-induction)
-- can switch from `_<ᵇ⁺_` to `_<ᵇ⁺ᵇ_` without losing well-
-- foundedness.

module Ordinal.Buchholz.OrderExtendedBudget where

open import Data.Nat.Base using (ℕ; suc; _<_)
open import Data.Nat.Induction as NatInd using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded; wf⇒asym; module Subrelation)
open import Relation.Binary.Construct.On as On using (wellFounded)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Nullary using (¬_)

open import Ordinal.Buchholz.Syntax using (BT)
open import Ordinal.Buchholz.OrderExtended using (_<ᵇ⁺_)

BudgetedBT⁺ : Set
BudgetedBT⁺ = ℕ × BT

infix 4 _<ᵇ⁺ᵇ_

data _<ᵇ⁺ᵇ_ : BudgetedBT⁺ → BudgetedBT⁺ → Set where
  spend : ∀ {n x y} (p : x <ᵇ⁺ y) → (n , x) <ᵇ⁺ᵇ (suc n , y)

BudgetOrder⁺ : Rel BudgetedBT⁺ _
BudgetOrder⁺ = _<_ on proj₁

<ᵇ⁺ᵇ⇒budget : _<ᵇ⁺ᵇ_ ⇒ BudgetOrder⁺
<ᵇ⁺ᵇ⇒budget (spend _) = ≤-refl

wf-<ᵇ⁺ᵇ : WellFounded _<ᵇ⁺ᵇ_
wf-<ᵇ⁺ᵇ =
  let module SR = Subrelation <ᵇ⁺ᵇ⇒budget
  in SR.wellFounded (On.wellFounded proj₁ NatInd.<-wellFounded)

<ᵇ⁺ᵇ-irreflexive : ∀ {s} → ¬ (s <ᵇ⁺ᵇ s)
<ᵇ⁺ᵇ-irreflexive {s} p = wf⇒asym wf-<ᵇ⁺ᵇ p p
