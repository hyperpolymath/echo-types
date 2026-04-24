{-# OPTIONS --safe --without-K #-}

-- Phase 1.2 of the Option B programme (see `docs/buchholz-plan.adoc`).
--
-- Ordinal arithmetic on Brouwer notations: *definitions* only.
-- All non-trivial monotonicity proofs are scheduled for Phase 1.3,
-- where they may drive a small redesign of `_≤_` in the base
-- `Ordinal.Brouwer` module (the current data-type axiomatisation
-- proves key lemmas like `osuc-mono-≤` only with some care, and
-- the Phase 1.3 work will decide whether to add constructors or
-- switch to a recursive `_≤_`).
--
-- Contents:
--
-- * `_⊕_` — left-recursive naive ordinal sum. Not Hessenberg; the
--   full natural-sum definition (commutative + bi-monotonic) needs
--   more machinery than pays off for the rank we actually need.
--   This is the cheapest sum that still lets `psi-rank` propagate
--   ordinal-argument descent via right-monotonicity, which is the
--   only direction we need for Phase 2.2.
-- * `nat-to-ord` — the standard successor-stack encoding of ℕ.
-- * `ω-rank : OmegaIndex → Ord` — rank for Ω-markers. `fin n` maps
--   to `osuc^(n+1) oz`, `ω` maps to the canonical Brouwer ω.
-- * `psi-rank : OmegaIndex → Ord → Ord` — rank for ψ-terms, shape
--   `osuc (ω-rank ν ⊕ α)`. The outer successor guarantees
--   `ω-rank ν < psi-rank ν α` regardless of α; the `⊕ α` tail
--   carries the ψ-argument's rank so that `<ᵇ-ψα α<β` descends
--   via right-monotonicity of `⊕`.

module Ordinal.Brouwer.Arithmetic where

open import Data.Nat.Base using (ℕ; zero; suc)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin; ω)
open import Ordinal.Brouwer using (Ord; oz; osuc; olim)

----------------------------------------------------------------------------
-- Naive ordinal sum
----------------------------------------------------------------------------

-- Left-recursive: zero on the left is the unit definitionally,
-- successor on the left lifts the successor past the sum, limit on
-- the left distributes under the sum.

infixl 6 _⊕_

_⊕_ : Ord → Ord → Ord
oz      ⊕ β = β
osuc α  ⊕ β = osuc (α ⊕ β)
olim f  ⊕ β = olim (λ n → f n ⊕ β)

----------------------------------------------------------------------------
-- Rank target for Ω-indices
----------------------------------------------------------------------------

-- Standard encoding of ℕ into Ord as a successor stack.

nat-to-ord : ℕ → Ord
nat-to-ord zero    = oz
nat-to-ord (suc n) = osuc (nat-to-ord n)

-- Rank of an Ω-marker. `fin n` goes to a successor stack of length
-- `n + 1`; `ω` goes to the canonical Brouwer ω. The `+ 1` offset
-- keeps `ω-rank (fin 0)` strictly above `oz = rank bzero` so the
-- `<ᵇ-0-Ω` constructor descends into `<Ord` in Phase 2.2.

ω-rank : OmegaIndex → Ord
ω-rank (fin n) = nat-to-ord (suc n)
ω-rank ω       = olim nat-to-ord

----------------------------------------------------------------------------
-- Rank target for ψ-terms
----------------------------------------------------------------------------

-- `psi-rank ν α = osuc (ω-rank ν ⊕ α)`. The outer `osuc` is what
-- `<ᵇ-0-ψ` / `<ᵇ-ψΩ≤` need (strict domination of bzero / Ω-rank);
-- the `⊕ α` tail is what `<ᵇ-ψα` needs (right-monotonic descent on
-- the ψ-argument).

psi-rank : OmegaIndex → Ord → Ord
psi-rank ν α = osuc (ω-rank ν ⊕ α)

----------------------------------------------------------------------------
-- Definitional sanity checks (no proofs, just unit tests via ≡)
----------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ordinal.Brouwer using (one; two)

-- The smallest Ω-rank is strictly above zero.

ω-rank-fin0 : ω-rank (fin 0) ≡ one
ω-rank-fin0 = refl

ω-rank-fin1 : ω-rank (fin 1) ≡ two
ω-rank-fin1 = refl

-- `psi-rank ν oz = osuc (ω-rank ν ⊕ oz)`. Since `⊕`'s right-identity
-- is only up to `≤` (proved in Phase 1.3), we don't state `≡` here.

-- Left-unit of `⊕` is definitional.

⊕-oz-left : ∀ β → oz ⊕ β ≡ β
⊕-oz-left _ = refl
