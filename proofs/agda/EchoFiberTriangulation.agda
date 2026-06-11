{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- External-fibre triangulation (foundation P1; docs/foundation.adoc
-- §"Known limitations", item 2; answers docs/retractions.adoc
-- R-2026-05-18 finding 5 "echo↔fib is a same-module triviality").
--
-- The retraction correctly flagged that `EchoFiberBridge.fiber` is a
-- *same-module restatement* of the Σ, so `echo↔fib` is the identity
-- on a type — a triviality, not corroboration. This module removes
-- that self-reference by triangulating `Echo` against the standard
-- library's OWN, independently-authored notions in
-- `Function.Definitions` / `Function.Bundles` — code written by other
-- people, for surjections, with no knowledge of echo-types.
--
-- Three results, each stated at its TRUE strength (no overclaim):
--
--   T1  CALIBRATION COINCIDENCE (not a deep theorem): the per-point
--       witness of stdlib's `StrictlySurjective _≡_ f` is *exactly*
--       `Echo f y`. Mostly definitional; its value is that the other
--       definition is the community's, not ours.
--   T2  GENUINE CONTENT: `Echo f y` ↔ the opposite-orientation fibre
--       `∃ x. y ≡ f x`, via stdlib's independent `_↔_` bundle. The
--       round-trips are NOT `refl` — they carry `sym`/`sym-sym`
--       transport content. This is the substantive coherence.
--   T3  SURJECTION TIE: all echo-fibres inhabited gives a bona fide
--       stdlib surjection `A ↠ B` (`mk↠ₛ`). Connects `Echo` to the
--       community surjectivity notion.
--
-- --safe --without-K, ZERO postulates. The only non-structural lemma
-- is `sym-sym` (involutivity of `sym`), proved here by pattern match
-- (K-free: matching `refl`, not UIP).

module EchoFiberTriangulation where

open import Level using (Level)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; ∃; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

-- INDEPENDENT anchors — authored in the standard library, not here:
open import Function.Definitions using (StrictlySurjective)
open import Function.Bundles using (_↔_; mk↔ₛ′; _↠_; mk↠ₛ)

open import Echo using (Echo)

private
  variable
    a b : Level
    A : Set a
    B : Set b

----------------------------------------------------------------------
-- T1 — Calibration coincidence with the stdlib surjectivity witness.
--
-- `StrictlySurjective _≡_ f` is, by stdlib's definition,
-- `∀ y → ∃ λ x → f x ≡ y`.  Its per-point witness is `∃ λ x → f x ≡ y`,
-- which is *definitionally* `Echo f y`.  Honest framing: this is a
-- sanity/coincidence anchor — `Echo` is the community's fibre, not a
-- bespoke construction — NOT a grounding metatheorem.

echo-is-stdlib-witness :
  (f : A → B) (y : B) → Echo f y ≡ (∃ λ x → f x ≡ y)
echo-is-stdlib-witness f y = refl

all-echo→stdlib-strictly-surjective :
  {f : A → B} → (∀ y → Echo f y) → StrictlySurjective _≡_ f
all-echo→stdlib-strictly-surjective h y = h y

stdlib-strictly-surjective→all-echo :
  {f : A → B} → StrictlySurjective _≡_ f → (∀ y → Echo f y)
stdlib-strictly-surjective→all-echo s y = s y

----------------------------------------------------------------------
-- T2 — Genuine content: Echo agrees with the opposite-orientation
-- fibre up to the standard symmetry, mechanised against stdlib's
-- independent `_↔_` bundle.  Round-trips are NOT refl.

-- Involutivity of `sym` (K-free: pattern-match on refl, no UIP).
sym-sym : {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
sym-sym refl = refl

-- The opposite-orientation fibre (the other common convention).
CoEcho : (A → B) → B → Set _
CoEcho {A = A} f y = ∃ λ x → y ≡ f x

-- `mk↔ₛ′ to from invˡ invʳ` wants the STRICT pointwise inverse laws
-- `invˡ : ∀ yc → to (from yc) ≡ yc` and `invʳ : ∀ xe → from (to xe) ≡ xe`
-- (stdlib `StrictlyInverseˡ/ʳ`). Both round-trips reduce a doubled
-- `sym`; neither is `refl` — this is the genuine transport content.
echo↔coecho : {f : A → B} {y : B} → Echo f y ↔ CoEcho f y
echo↔coecho {f = f} {y = y} =
  mk↔ₛ′
    (λ (x , p) → x , sym p)                       -- to   : Echo  → CoEcho
    (λ (x , q) → x , sym q)                       -- from : CoEcho → Echo
    (λ (x , q) → cong (x ,_) (sym-sym q))         -- to ∘ from ≡ id (NOT refl)
    (λ (x , p) → cong (x ,_) (sym-sym p))         -- from ∘ to ≡ id (NOT refl)

----------------------------------------------------------------------
-- T3 — Surjection tie: all echo-fibres inhabited ⇒ a stdlib `A ↠ B`.

all-echo→stdlib-surjection :
  {f : A → B} → (∀ y → Echo f y) → A ↠ B
all-echo→stdlib-surjection {f = f} h =
  mk↠ₛ {to = f} (all-echo→stdlib-strictly-surjective h)
