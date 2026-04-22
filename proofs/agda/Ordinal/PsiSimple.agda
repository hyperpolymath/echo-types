{-# OPTIONS --safe --without-K #-}

-- Stage S0 / Milestone E4 of docs/buchholz-plan.adoc.
--
-- Pedagogical least-gap shape for the toy ψ constructor over the
-- ℕ-staged closure family `C` from Ordinal.Closure.
--
-- `psi-notin-C` captures the exclusion side at stage 0:
-- no ψ-term is generable at stage 0 because `c-psi` requires an
-- earlier stage `k < m`.
--
-- `psi-least` captures the minimal-stage side:
-- whenever `psi β` is generable at stage `m`, we must have `1 ≤ m`.
-- Together with `psi-at-1` (from a stage-0 witness for β), this gives
-- the expected "first appears at stage 1" pattern.

module Ordinal.PsiSimple where

open import Data.Nat.Base using (ℕ; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Nullary using (¬_)

open import Ordinal.Base using (OT; psi)
open import Ordinal.Closure using (C; c-psi)

-- Exclusion side: no ψ-term can be in stage 0.

psi-notin-C : ∀ {β} → ¬ C 0 (psi β)
psi-notin-C (c-psi () _)

-- Construction side at the first non-zero stage, assuming β is already
-- in stage 0.

psi-at-1 : ∀ {β} → C 0 β → C 1 (psi β)
psi-at-1 cβ = c-psi (s≤s z≤n) cβ

-- Minimality side: any stage that contains `psi β` is at least 1.

psi-least : ∀ {β m} → C 0 β → C m (psi β) → 1 ≤ m
psi-least _ (c-psi k<m _) = ≤-trans (s≤s z≤n) k<m
