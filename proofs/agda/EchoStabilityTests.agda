{-# OPTIONS --safe --without-K #-}

-- Stability tests: a lightweight harness of propositional-equality
-- lemmas that wedge the shape of core Echo/Thermodynamics theorems
-- against unintended rewrites. Each "test" here is a theorem whose
-- body is `refl`, so it breaks immediately under a silent rename,
-- signature change, or constructor reshuffle in the upstream module.
--
-- Scope note: the earlier version of this file tested against
-- EchoCategory, EchoCNO, and several theorems that were never proved.
-- Those modules were deleted (duplicates of EchoCategorical /
-- EchoCNOBridge), so the corresponding sections were removed rather
-- than rewritten against a different API. Reintroduce on a per-
-- section basis as new content lands.

module EchoStabilityTests where

open import Data.Nat.Base using (ℕ; zero; suc; _*_)
open import Data.Nat.Logarithm using (⌊log₂_⌋)
open import Data.Fin.Base using (Fin) renaming (zero to fzero)
open import Data.Fin.Properties using (_≟_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo using (Echo; echo-intro; MapOver; map-over; map-over-id; map-over-comp)
open import EchoFiberCount using
  ( FiberSize-fin
  ; FiberSize-fin-id-zero
  ; FiberSize-fin-const
  )
open import EchoThermodynamics using
  ( Temperature
  ; k
  ; landauer-bound
  ; fiber-erasure-bound
  ; bennett-reversible
  ; bennett-reversible-id-zero
  ; landauer-collapse
  )

----------------------------------------------------------------------------
-- Section 1: Core Echo type stability
----------------------------------------------------------------------------

-- Test 1. Echo introduction places the provided x as the first
-- component of the sigma. Breaks under a silent reshape of Echo.
echo-intro-fst : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) →
                 proj₁ (echo-intro f x) ≡ x
echo-intro-fst f x = refl

-- Test 2. map-over advances the first component by the underlying
-- map u. Breaks if map-over's tuple shape changes. Uses fully
-- explicit f and f' so Agda can pin the MapOver implicit args.
map-over-fst : ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
               (f : A → B) (f' : A' → B) {y : B}
               (u : A → A') (c : ∀ x → f' (u x) ≡ f x)
               (x : A) (p : f x ≡ y) →
               proj₁ (map-over {f = f} {f' = f'} (u , c) (x , p)) ≡ u x
map-over-fst f f' u c x p = refl

-- Test 3. Identity law for map-over (restates the pinned lemma so
-- both the name and the shape are locked in by this module).
map-over-id-check : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
                    (e : Echo f y) →
                    map-over (id , (λ _ → refl)) e ≡ e
map-over-id-check e = map-over-id e

----------------------------------------------------------------------------
-- Section 2: Thermodynamic stability
--
-- This section was rewritten when EchoThermodynamics was redeemed
-- against the honest finite-domain Landauer/Bennett bounds. The
-- earlier `cno-fiber-size`, `fiber-energy`, and `cno-zero-energy-*`
-- API tested vacuous theorems built on top of `FiberSize = 1` —
-- those names are gone, and these tests now pin the new shape:
-- `fiber-erasure-bound`, `bennett-reversible`, `landauer-collapse`.
----------------------------------------------------------------------------

private
  -- Pin Fin 1 / Fin 3 decision procedures so Agda can resolve the
  -- implicit `n` argument of `Data.Fin.Properties._≟_` in the
  -- thermodynamic tests below.
  _≟₁_ : (a b : Fin 1) → _
  a ≟₁ b = a ≟ b

  _≟₃_ : (a b : Fin 3) → _
  a ≟₃ b = a ≟ b

-- Test 4. id : Fin 1 → Fin 1 at index zero is the canonical
-- Bennett-reversible single-step computation: erasure bound 0.
bennett-id-zero-check : ∀ (T : Temperature) →
                       fiber-erasure-bound {n = suc zero} (λ x → x) fzero _≟₁_ T ≡ 0
bennett-id-zero-check T = bennett-reversible-id-zero _≟₁_ T

-- Test 5. The constant map (λ _ → fzero) on Fin 3 collapses every
-- domain index onto fzero, so its erasure bound is the full
-- Landauer cost k * T * ⌊log₂ 3⌋.
landauer-const3-check :
  ∀ (T : Temperature) →
  fiber-erasure-bound {n = 3} (λ _ → fzero {2}) (fzero {2}) _≟₃_ T
  ≡ k * T * ⌊log₂ 3 ⌋
landauer-const3-check T =
  landauer-collapse {n = 3} (λ _ → fzero {2}) (fzero {2}) _≟₃_ T (λ _ → refl)

-- Test 6. The bennett corollary itself: any function whose fiber
-- size at y is 1 dissipates zero on the bound. Pinned at the
-- id-zero instance so the test is closed.
bennett-corollary-check : ∀ (T : Temperature) →
                          fiber-erasure-bound {n = suc zero} (λ x → x) fzero _≟₁_ T ≡ 0
bennett-corollary-check T =
  bennett-reversible (λ x → x) fzero _≟₁_ T (FiberSize-fin-id-zero _≟₁_)

----------------------------------------------------------------------------
-- What is deliberately not tested here
----------------------------------------------------------------------------

-- * Universal CNO / categorical equivalence: the EchoCategory module
--   was a duplicate of EchoCategorical and has been deleted. Port
--   these tests to EchoCategorical when it grows a matching API.
-- * CNO singleton equivalence under identity: the EchoCNO module
--   was a duplicate of EchoCNOBridge and has been deleted. Add
--   stability tests against EchoCNOBridge's CNOEcho / nullop-echo
--   lemmas in a follow-up pass.
-- * Infinite-domain (`ProgramState = ℕ → ℕ`) erasure bounds:
--   `FiberSize-fin` is finite-domain only; the infinite case
--   needs measure-theoretic or capacity arguments and is open.
-- * Shannon-entropy / mutual-information formalisations: not yet
--   present in the repo. See `docs/echo-types/roadmap.md`.
