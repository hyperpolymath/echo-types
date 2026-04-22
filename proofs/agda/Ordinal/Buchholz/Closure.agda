{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- `Cν ν m t` is the ν-indexed closure family at stage `m` for term
-- `t`. This is the Buchholz-shaped generalisation of Ordinal.Closure:
-- closure is still staged by ℕ while carrying an explicit Ω-index
-- parameter `ν` for future side conditions.

module Ordinal.Buchholz.Closure where

open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans)

open import Ordinal.OmegaMarkers using (OmegaIndex; _≤Ω_)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)

data Cν (ν : OmegaIndex) : ℕ → BT → Set where
  cν-zero  : ∀ {m} → Cν ν m bzero
  cν-omega : ∀ {m μ} → μ ≤Ω ν → Cν ν m (bOmega μ)
  cν-plus  : ∀ {m x y} → Cν ν m x → Cν ν m y → Cν ν m (bplus x y)
  cν-psi   : ∀ {m k μ β} → μ ≤Ω ν → k < m → Cν ν k β → Cν ν m (bpsi μ β)

-- Headline E5 structural lemma: raising the stage keeps derivability.

Cν-monotone : ∀ {ν m n t} → m ≤ n → Cν ν m t → Cν ν n t
Cν-monotone _   cν-zero          = cν-zero
Cν-monotone _   (cν-omega μ≤ν)   = cν-omega μ≤ν
Cν-monotone m≤n (cν-plus cx cy)  = cν-plus (Cν-monotone m≤n cx) (Cν-monotone m≤n cy)
Cν-monotone m≤n (cν-psi μ≤ν k<m ck) = cν-psi μ≤ν (≤-trans k<m m≤n) ck
