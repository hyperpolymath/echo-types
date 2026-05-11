{-# OPTIONS --safe --without-K #-}

-- Phase 1.2 of the Option B programme (see `docs/buchholz-plan.adoc`).
--
-- Ordinal arithmetic on Brouwer notations: *definitions* only.
-- All non-trivial monotonicity proofs are in Phase 1.3 (Phase13.agda).
--
-- Contents:
--
-- * `_⊕_` — right-recursive ordinal sum. Recursion is on the right
--   argument, mirroring `_≤′_`'s second-argument structure, so that
--   `⊕-mono-<-right` and `⊕-mono-≤-right` are provable by structural
--   induction on `γ` (see issue #34 for the counterexample that ruled
--   out the original left-recursive form). Right-unit `α ⊕ oz = α` is
--   definitional; left-unit `oz ⊕ β = β` is propositional (Phase 1.3).
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
-- Ordinal sum (right-recursive)
----------------------------------------------------------------------------

-- Right-recursive: right-unit `α ⊕ oz = α` is definitional; successor
-- on the right lifts past the sum; limit on the right distributes.
-- This direction aligns with `_≤′_`'s second-argument recursion and
-- makes `⊕-mono-<-right` provable by induction on γ (Phase 1.3).

infixl 6 _⊕_

_⊕_ : Ord → Ord → Ord
α ⊕ oz      = α
α ⊕ osuc β  = osuc (α ⊕ β)
α ⊕ olim f  = olim (λ n → α ⊕ f n)

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

-- Right-unit of `⊕` is definitional.

⊕-oz-right : ∀ α → α ⊕ oz ≡ α
⊕-oz-right _ = refl
