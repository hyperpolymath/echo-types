{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoSearch — Axis 8 witness-search abstract machine (thin slice).
--
-- Axis 8 of `docs/echo-types/taxonomy.md` distinguishes
-- information-theoretic inhabitation of `Echo f y` from a
-- *computational* witness extracted by an algorithm. Refinement (4)
-- in that section names the heaviest reading:
--
--     "Witness-search abstract machine. Model the extractor as a
--      term in a bounded-step abstract machine and pair it with
--      the echo."
--
-- A faithful "abstract machine" with steps, configurations, and a
-- semantics would be a sizeable separate development; the *honest*
-- thin slice of that idea is the enumerator-bounded witness:
--
--     a search strategy = an enumerator `enum : ℕ → A`
--     a bound-`n` echo  = a witness `enum k ≡ x` with `k < n`
--                         together with the usual `f x ≡ y`
--
-- The `ℕ`-bound is the "step budget" of the would-be machine. Every
-- machine of the heavier refinement (e.g. a Turing-bounded extractor,
-- a polynomial-time enumeration) projects onto this thin slice by
-- forgetting everything except the index it queried and the bound it
-- queried under. So this module sits at the *bottom* of the
-- axis-8(4) lattice in the same sense that `EchoDecidable` sits at
-- the bottom of the axis-8(3) lattice (`docs/echo-types/taxonomy.md`
-- §"Open question / lattice"), and a heavier machine model lands on
-- top later without renaming or invalidating these lemmas.
--
-- Design choices, in line with `EchoApprox` / `EchoFiberCount`:
--
--   * `SearchStrategy A := ℕ → A`. A total function. Partiality is
--     not modelled here — that is a separate refinement (axis 8(2)).
--     A total enumerator is exactly the right shape for a
--     bound-respecting machine: at step `k` it produces the element
--     `enum k`; nothing else.
--
--   * `EchoS enum f y n := Σ ℕ λ k → (k < n) × (f (enum k) ≡ y)`.
--     Crucially `_<_` is stdlib's `Data.Nat.Base._<_`, i.e.
--     `suc m ≤ n` — the strict form. This is the form `≤-<-trans` /
--     `<-≤-trans` from `Data.Nat.Properties` operate on without any
--     conversion glue.
--
--   * Composition: we ship `echo-search-postcompose`, the
--     "post-compose with `g`" rule. This is the search analogue of
--     "f x ≡ y ⇒ (g ∘ f) x ≡ g y" — it preserves the bound exactly
--     (the same k, the same enumerator step, the same `< n` proof).
--     This is the genuinely-honest compositional content available
--     without further machinery; a product/sequential composition
--     under two strategies needs more (a `ℕ × ℕ` index, a paired
--     bound, and a choice of pairing function on the index set),
--     which is a separate slice. See "where next" below.
--
-- Where next:
--
--   * Sequential composition `EchoS enum f b n₁ → EchoS enum' g y n₂
--     → EchoS (paired-enum) (g ∘ f) y (n₁ * n₂)` under a pairing
--     enumerator on `ℕ × ℕ`. Honest but needs a bijection
--     `ℕ × ℕ ↔ ℕ`; defer to the slice that wants it.
--
--   * A real abstract-machine refinement: configurations + a step
--     relation, with `EchoS` recovered as `∃ trace . trace.length < n
--     ∧ trace.last ≡ x ∧ f x ≡ y`. The current `EchoS` projects from
--     that by collapsing the trace to its terminal index.
--
--   * A *bounded-search-is-decidable* lemma in the presence of
--     decidable equality on `B`: search up to `n` either yields an
--     `EchoS enum f y n` or proves `¬ EchoS enum f y n`. This is the
--     concrete bridge to `EchoDecidable`, kept as a separate slice
--     because it needs a `_≟_` on `B` and a finite-walk recursion.

module EchoSearch where

open import Function.Base                         using (_∘_; id)
open import Data.Nat.Base                         using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties                   using (≤-<-trans; <-≤-trans)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Echo                                  using (Echo)

----------------------------------------------------------------------
-- Search strategies and bound-indexed echoes
----------------------------------------------------------------------

-- A search strategy on `A` is a total enumeration of its elements
-- indexed by ℕ. Total, by design — partiality is a separate axis 8(2)
-- refinement and would obscure the bound semantics here.
SearchStrategy : ∀ {a} → Set a → Set a
SearchStrategy A = ℕ → A

-- The witness-search echo at bound `n`: a step index `k < n` at
-- which the enumerator produced a preimage of `y` under `f`.
EchoS :
  ∀ {a b} {A : Set a} {B : Set b}
  (enum : SearchStrategy A) (f : A → B) (y : B) (n : ℕ) → Set b
EchoS enum f y n = Σ ℕ (λ k → (k < n) × (f (enum k) ≡ y))

----------------------------------------------------------------------
-- Headlines
----------------------------------------------------------------------

-- Introduction. If at step `k < n` the enumerator returns an element
-- whose image is `y`, we have a bound-`n` search echo.
echo-search-intro :
  ∀ {a b} {A : Set a} {B : Set b}
  (enum : SearchStrategy A) (f : A → B) {y : B}
  (k : ℕ) (n : ℕ) (k<n : k < n) →
  f (enum k) ≡ y →
  EchoS enum f y n
echo-search-intro enum f k n k<n eq = k , k<n , eq

-- Bound monotonicity. A larger budget admits every shorter-budget
-- search; the same step index, lifted along `<-≤-trans`.
echo-search-relax :
  ∀ {a b} {A : Set a} {B : Set b}
  (enum : SearchStrategy A) (f : A → B) {y : B} {n m : ℕ}
  (n≤m : n ≤ m) →
  EchoS enum f y n → EchoS enum f y m
echo-search-relax enum f n≤m (k , k<n , eq) =
  k , <-≤-trans k<n n≤m , eq

-- Forgetful projection. Throw away the step budget and the index
-- bound and keep only the underlying intensional `Echo`. This is the
-- canonical "search refines inhabitation" arrow.
echo-search-forget :
  ∀ {a b} {A : Set a} {B : Set b}
  {enum : SearchStrategy A} {f : A → B} {y : B} {n : ℕ} →
  EchoS enum f y n → Echo f y
echo-search-forget (k , _ , eq) = _ , eq

-- Empty-budget vacuity. No witness can live at bound 0, because
-- `k < 0` is uninhabited in stdlib's `Data.Nat._<_`.
echo-search-bound-zero :
  ∀ {a b} {A : Set a} {B : Set b}
  (enum : SearchStrategy A) (f : A → B) (y : B) →
  ¬ EchoS enum f y 0
echo-search-bound-zero enum f y (k , () , eq)

-- Post-composition. The honest compositional rule available without
-- a product-strategy / pairing-bijection on the index set: a
-- bound-`n` search witnessing `f` at `y` also witnesses `g ∘ f` at
-- `g y`, at the *same* step index and the *same* bound. The bound
-- is preserved exactly because the enumerator and the queried step
-- have not changed — only what we report as the "answer" has.
echo-search-postcompose :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (enum : SearchStrategy A) (f : A → B) (g : B → C) {y : B} {n : ℕ} →
  EchoS enum f y n → EchoS enum (g ∘ f) (g y) n
echo-search-postcompose enum f g (k , k<n , eq) =
  k , k<n , cong g eq
