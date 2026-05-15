{-# OPTIONS --safe --without-K #-}

-- Phase 1.1 of the WF-track "Option B" programme in
-- `docs/buchholz-plan.adoc`. Establishes a constructive
-- Brouwer-style ordinal notation with a direct well-foundedness
-- proof. This file does NOT depend on `Ordinal.Buchholz.Order`
-- or any `<ᵇ` infrastructure — that independence is the whole
-- point. Later phases (2+) will embed the Buchholz order into
-- this rank target and derive `wf-<ᵇ` for the enlarged order via
-- `Subrelation.wellFounded`.
--
-- Representation: zero, successor, ℕ-indexed supremum. This already
-- exhausts countable ordinals below ω₁; for Buchholz rank up to
-- ψ(Ω_ω) it is far more than we need.
--
-- The strict order `_<_` is defined as `osuc α ≤ β`. WF is proved by
-- structural induction on `Ord` directly; the higher-order `olim`
-- branch is accepted by Agda's structural recursion on subterms of
-- the function-indexed inductive.

module Ordinal.Brouwer where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Induction.WellFounded using (Acc; acc; WellFounded; wf⇒asym)
open import Relation.Nullary using (¬_)

----------------------------------------------------------------------------
-- Ordinal notations
----------------------------------------------------------------------------

data Ord : Set where
  oz   : Ord
  osuc : Ord → Ord
  olim : (ℕ → Ord) → Ord

----------------------------------------------------------------------------
-- Strict and non-strict orders
----------------------------------------------------------------------------

infix 4 _≤_ _<_

-- Reflexive closure. Three generators:
--   * identity,
--   * one-step successor on the right-hand side,
--   * selecting a specific branch inside a limit on the right.

data _≤_ : Ord → Ord → Set where
  ≤-refl : ∀ {α}     → α ≤ α
  ≤-suc  : ∀ {α β}   → α ≤ β → α ≤ osuc β
  ≤-lim  : ∀ {α f} n → α ≤ f n → α ≤ olim f

-- Strict order: successor of α still fits at-or-below β.

_<_ : Ord → Ord → Set
α < β = osuc α ≤ β

----------------------------------------------------------------------------
-- Basic structural properties
----------------------------------------------------------------------------

-- Zero is minimum. Structural on the right-hand side.

≤-zero : ∀ {α} → oz ≤ α
≤-zero {oz}     = ≤-refl
≤-zero {osuc α} = ≤-suc ≤-zero
≤-zero {olim f} = ≤-lim 0 ≤-zero

-- Weakening into successor.

≤-step : ∀ {α β} → α ≤ β → α ≤ osuc β
≤-step = ≤-suc

-- Each branch of a limit sits at-or-below it. Strict-below is not
-- available in general — a constant sequence has `f n ≡ olim f` —
-- but the ≤ witness is enough for rank bookkeeping.

f-in-lim : ∀ f n → f n ≤ olim f
f-in-lim f n = ≤-lim n ≤-refl

-- Successor strictly above its predecessor.

<-suc-self : ∀ {α} → α < osuc α
<-suc-self = ≤-refl

----------------------------------------------------------------------------
-- Transitivity
----------------------------------------------------------------------------

-- Transitivity of ≤ by induction on the right leg. `≤-refl` case
-- returns the left leg unchanged; `≤-suc` / `≤-lim` cases propagate.

≤-trans : ∀ {α β γ} → α ≤ β → β ≤ γ → α ≤ γ
≤-trans p ≤-refl       = p
≤-trans p (≤-suc q)    = ≤-suc (≤-trans p q)
≤-trans p (≤-lim n q)  = ≤-lim n (≤-trans p q)

-- β ≤ osuc β, the canonical one-step witness.

≤-osuc : ∀ {β} → β ≤ osuc β
≤-osuc = ≤-suc ≤-refl

-- Transitivity of <: osuc α ≤ β ≤ osuc β ≤ osuc β... ≤ γ.

<-trans : ∀ {α β γ} → α < β → β < γ → α < γ
<-trans {α} {β} p q = ≤-trans (≤-trans p ≤-osuc) q

----------------------------------------------------------------------------
-- Well-foundedness
----------------------------------------------------------------------------

-- Predecessor of osuc α is either α itself (≤-refl case) or a
-- strictly smaller β with β < α (≤-suc case). Both yield Acc.

pred-of-osuc : ∀ {α} → Acc _<_ α → ∀ {β} → β < osuc α → Acc _<_ β
pred-of-osuc (acc rsα) ≤-refl    = acc rsα
pred-of-osuc (acc rsα) (≤-suc q) = rsα q

-- Predecessor of olim f: must come via ≤-lim with a branch index `n`,
-- giving β < f n. Inductive accessibility of f n gives Acc β.

pred-of-olim :
  ∀ {f} → (∀ n → Acc _<_ (f n)) →
  ∀ {β} → β < olim f → Acc _<_ β
pred-of-olim wfs (≤-lim n q) with wfs n
... | acc rs = rs q

-- Top-level WF: structural induction on Ord.

wf-< : WellFounded _<_
wf-< oz       = acc λ ()
wf-< (osuc α) = acc (pred-of-osuc (wf-< α))
wf-< (olim f) = acc (pred-of-olim (λ n → wf-< (f n)))

----------------------------------------------------------------------------
-- Derived corollaries
----------------------------------------------------------------------------

-- Irreflexivity via wf⇒asym; no direct pattern match is needed.

<-irrefl : ∀ {α} → ¬ (α < α)
<-irrefl {α} p = wf⇒asym wf-< p p

-- Worked small witnesses.

one : Ord
one = osuc oz

two : Ord
two = osuc one

ω : Ord
ω = olim nat-to-ord
  where
  nat-to-ord : ℕ → Ord
  nat-to-ord zero    = oz
  nat-to-ord (suc n) = osuc (nat-to-ord n)

oz<one : oz < one
oz<one = <-suc-self

one<two : one < two
one<two = <-suc-self

oz<two : oz < two
oz<two = <-trans oz<one one<two

one<ω : one < ω
one<ω = ≤-lim 2 ≤-refl
