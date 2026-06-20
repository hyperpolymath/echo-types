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
--   * (LANDED) Product / sequential composition. The original sketch
--     `EchoS enum f b n₁ → EchoS enum' g y n₂ → EchoS … (g ∘ f) y (n₁ * n₂)`
--     is ill-typed (the second search's witness is not tied to the first's
--     output `b`); the well-typed form is the PRODUCT of two independent
--     searches, `echo-search-product` below, over `A₁ × A₂` with budget
--     `n₁ * n₂`. The `n₁ * n₂` budget provably needs a budget-dependent
--     row-major pairing (a global `ℕ × ℕ ↔ ℕ` cannot keep
--     `pair (n₁-1) (n₂-1) < n₁ * n₂`), so it divides by `n₂` and requires
--     `NonZero n₂`. See `productEnum` / `echo-search-product` at the bottom.
--
--   * A real abstract-machine refinement: configurations + a step
--     relation, with `EchoS` recovered as `∃ trace . trace.length < n
--     ∧ trace.last ≡ x ∧ f x ≡ y`. The current `EchoS` projects from
--     that by collapsing the trace to its terminal index.
--
--   * (LANDED) A *bounded-search-is-decidable* lemma in the presence
--     of decidable equality on `B`: search up to `n` either yields an
--     `EchoS enum f y n` or proves `¬ EchoS enum f y n`. This is the
--     concrete bridge to `EchoDecidable`; it needs a `_≟_` on `B` and a
--     finite-walk recursion on the budget. See `bounded-search-is-decidable`
--     at the bottom of this module.

module EchoSearch where

open import Function.Base                         using (_∘_; id)
open import Data.Nat.Base                         using (ℕ; zero; suc; _≤_; _<_; _+_; _*_; z≤n; s≤s; NonZero)
open import Data.Nat.Properties
  using (≤-<-trans; <-≤-trans; <-cmp; <-trans; ≤-trans; ≤-refl; <-irrefl; +-monoˡ-<; *-monoˡ-≤)
open import Data.Nat.DivMod
  using (_/_; _%_; [m+kn]%n≡m%n; m<n⇒m%n≡m; m<n⇒m/n≡0; m*n/n≡m; +-distrib-/-∣ʳ)
open import Data.Nat.Divisibility                 using (divides-refl)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary                      using (¬_; Dec; yes; no)
open import Relation.Binary.Definitions           using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

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

----------------------------------------------------------------------
-- Decidability bridge
----------------------------------------------------------------------

-- Bounded search is decidable under decidable equality on the codomain.
-- Because `EchoS enum f y n` is exactly the bounded existential
-- `Σ k. (k < n) × (f (enum k) ≡ y)`, searching up to the budget `n`
-- either produces a bound-`n` search echo or refutes one. This is the
-- concrete bridge from EchoSearch to `EchoDecidable` (axis 8(3)): no
-- machine model is required, only the step budget and a `_≟_` on `B`.
-- Structural recursion on `n`; the `suc` step tests the new index `n`
-- and otherwise recurses, using trichotomy to refute every index below
-- `suc n` in the negative case.
bounded-search-is-decidable :
  ∀ {a b} {A : Set a} {B : Set b}
  (_≟_ : (x y : B) → Dec (x ≡ y))
  (enum : SearchStrategy A) (f : A → B) (y : B) (n : ℕ) →
  Dec (EchoS enum f y n)
bounded-search-is-decidable _≟_ enum f y zero =
  no (echo-search-bound-zero enum f y)
bounded-search-is-decidable _≟_ enum f y (suc n) with f (enum n) ≟ y
... | yes eq = yes (n , ≤-refl , eq)
... | no ¬eq with bounded-search-is-decidable _≟_ enum f y n
...   | yes (k , k<n , eqk) = yes (k , <-trans k<n ≤-refl , eqk)
...   | no ¬below          = no λ { (k , k<1+n , eqk) → contra k k<1+n eqk }
  where
    -- No index below `suc n` can witness `y`: indices below `n` are
    -- refuted by `¬below`, the index `n` itself by `¬eq`, and there is
    -- no index strictly between `n` and `suc n`.
    contra : ∀ k → k < suc n → f (enum k) ≡ y → ⊥
    contra k (s≤s k≤n) eqk with <-cmp k n
    ... | tri< k<n _ _ = ¬below (k , k<n , eqk)
    ... | tri≈ _ k≡n _ = ¬eq (trans (sym (cong (λ j → f (enum j)) k≡n)) eqk)
    ... | tri> _ _ n<k = <-irrefl refl (≤-trans n<k k≤n)

----------------------------------------------------------------------
-- Product (sequential) composition
----------------------------------------------------------------------

-- The product of two searches. `productMap` runs `f₁` and `f₂` on the two
-- components; `productEnum n₂` is the row-major product strategy on
-- `A₁ × A₂`: at index `k` it queries `enum₁ (k / n₂)` and `enum₂ (k % n₂)`,
-- where `n₂` is the second budget.
productMap :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
  (A₁ → B₁) → (A₂ → B₂) → (A₁ × A₂ → B₁ × B₂)
productMap f₁ f₂ (a₁ , a₂) = f₁ a₁ , f₂ a₂

productEnum :
  ∀ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
  (n₂ : ℕ) .{{_ : NonZero n₂}} →
  SearchStrategy A₁ → SearchStrategy A₂ → SearchStrategy (A₁ × A₂)
productEnum n₂ enum₁ enum₂ k = enum₁ (k / n₂) , enum₂ (k % n₂)

-- Two bounded searches compose into a single bounded search over the
-- product, with the *product* budget `n₁ * n₂`. The witness pairs the two
-- step indices row-major as `k₂ + k₁ * n₂`; this stays `< n₁ * n₂` exactly
-- when `k₁ < n₁` and `k₂ < n₂`, and `/ n₂` / `% n₂` recover `k₁` / `k₂`.
--
-- The `n₁ * n₂` budget provably needs this budget-dependent pairing — a
-- global `ℕ × ℕ ↔ ℕ` cannot keep `pair (n₁-1) (n₂-1) < n₁ * n₂` — which is
-- why the scheme divides by `n₂` and requires `NonZero n₂` (a zero-width
-- second dimension admits no witness anyway).
echo-search-product :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂}
  {enum₁ : SearchStrategy A₁} {enum₂ : SearchStrategy A₂}
  {f₁ : A₁ → B₁} {f₂ : A₂ → B₂} {y₁ : B₁} {y₂ : B₂}
  {n₁ n₂ : ℕ} .{{_ : NonZero n₂}} →
  EchoS enum₁ f₁ y₁ n₁ →
  EchoS enum₂ f₂ y₂ n₂ →
  EchoS (productEnum n₂ enum₁ enum₂) (productMap f₁ f₂) (y₁ , y₂) (n₁ * n₂)
echo-search-product {enum₁ = enum₁} {enum₂} {f₁} {f₂} {y₁} {y₂} {n₁} {n₂}
  (k₁ , k₁<n₁ , eq₁) (k₂ , k₂<n₂ , eq₂) =
    idx , idx<n₁n₂ , prodEq
  where
    idx : ℕ
    idx = k₂ + k₁ * n₂
    -- k₂ + k₁*n₂ < n₂ + k₁*n₂ = suc k₁ * n₂ ≤ n₁ * n₂
    idx<n₁n₂ : idx < n₁ * n₂
    idx<n₁n₂ = <-≤-trans (+-monoˡ-< (k₁ * n₂) k₂<n₂) (*-monoˡ-≤ n₂ k₁<n₁)
    idx/n₂≡k₁ : idx / n₂ ≡ k₁
    idx/n₂≡k₁ = trans (+-distrib-/-∣ʳ k₂ (divides-refl k₁))
                      (cong₂ _+_ (m<n⇒m/n≡0 k₂<n₂) (m*n/n≡m k₁ n₂))
    idx%n₂≡k₂ : idx % n₂ ≡ k₂
    idx%n₂≡k₂ = trans ([m+kn]%n≡m%n k₂ k₁ n₂) (m<n⇒m%n≡m k₂<n₂)
    prodEq :
      productMap f₁ f₂ (productEnum n₂ enum₁ enum₂ idx) ≡ (y₁ , y₂)
    prodEq = cong₂ _,_
               (trans (cong (f₁ ∘ enum₁) idx/n₂≡k₁) eq₁)
               (trans (cong (f₂ ∘ enum₂) idx%n₂≡k₂) eq₂)
