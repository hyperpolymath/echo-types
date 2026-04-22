{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Formal Ω-index markers only; no ordinal semantics is claimed here.
-- Finite markers are represented by `fin n`, and `ω` is the first
-- limit marker used later by Buchholz syntax.

module Ordinal.OmegaMarkers where

open import Data.Nat.Base using (ℕ; _≤_; zero; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

data OmegaIndex : Set where
  fin : ℕ → OmegaIndex
  ω   : OmegaIndex

-- Structural preorder on Ω-markers used as side conditions in Buchholz
-- closure rules: finite indices compare by `ℕ` order, every finite
-- index is below `ω`, and `ω` is only below itself.

data _≤Ω_ : OmegaIndex → OmegaIndex → Set where
  fin≤fin : ∀ {m n} → m ≤ n → fin m ≤Ω fin n
  fin≤ω   : ∀ {m}   → fin m ≤Ω ω
  ω≤ω     : ω ≤Ω ω

infix 4 _≤Ω_

≤Ω-refl : ∀ {ν} → ν ≤Ω ν
≤Ω-refl {fin n} = fin≤fin ≤-refl
≤Ω-refl {ω}     = ω≤ω

≤Ω-trans : ∀ {α β γ} → α ≤Ω β → β ≤Ω γ → α ≤Ω γ
≤Ω-trans (fin≤fin m≤n) (fin≤fin n≤k) = fin≤fin (≤-trans m≤n n≤k)
≤Ω-trans (fin≤fin _)   fin≤ω         = fin≤ω
≤Ω-trans fin≤ω         ω≤ω           = fin≤ω
≤Ω-trans ω≤ω           ω≤ω           = ω≤ω

Omega0 : OmegaIndex
Omega0 = fin zero

Omega1 : OmegaIndex
Omega1 = fin (suc zero)

Omegaω : OmegaIndex
Omegaω = ω
