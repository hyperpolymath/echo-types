{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- First ψ_ν-side exclusion statement over the ν-indexed closure:
-- no ψ-term can be generated at stage 0 because `cν-psi` requires
-- a strictly earlier stage witness.

module Ordinal.Buchholz.Psi where

open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Nullary using (¬_)

open import Ordinal.OmegaMarkers using (OmegaIndex)
open import Ordinal.Buchholz.Syntax using (BT; bpsi)
open import Ordinal.Buchholz.Closure using (Cν; cν-psi)

psiν-notin-Cν : ∀ {ν μ β} → ¬ Cν ν 0 (bpsi μ β)
psiν-notin-Cν (cν-psi _ () _)

-- Useful companion: any derivation of `ψ_μ β` lives at stage at least 1.

psiν-stage-lb : ∀ {ν μ β m} → Cν ν m (bpsi μ β) → 1 ≤ m
psiν-stage-lb (cν-psi _ k<m _) = ≤-trans (s≤s z≤n) k<m
