{-# OPTIONS --safe --without-K #-}

-- EchoThermoCollapseImpossible: O-THERMO-∞ confirmed negative.
--
-- O-THERMO-∞ (docs/ECHO-CNO-BRIDGE.adoc §"Thermodynamic Bridge") is
-- the falsifiable obligation: there is no `--safe --without-K` total
-- `cost` on an infinite carrier that agrees with `fiber-erasure-bound`
-- on every finite restriction. Its kill condition has two horns —
-- exhibit such a `cost` (impossibility *refuted*), or mechanise a
-- proof that clauses (i)∧(ii) ⊢ ⊥ (impossibility *confirmed*).
--
-- This module discharges the obligation via the second horn:
-- impossibility CONFIRMED, for the doc's own named witness.
--
-- The argument is exactly the doc's "Witness that it bites". Take the
-- constant map `c : ℕ → B`, `c _ = y₀` (the canonical Landauer-collapse
-- input). Its restriction along any inclusion `Fin n ↪ ℕ` is the
-- constant map `Fin n → B`, whose `fiber-erasure-bound` over `y₀` is
-- `landauer-bound T n` (PR #58's honest count: `FiberSize-fin-const`).
-- Clause (ii) instantiated at this witness forces, for *every* `n`,
--
--     cost c y₀ _≟_ T  ≡  landauer-bound T n
--
-- But `cost c y₀ _≟_ T` is a *single* natural number (the `cost` is
-- total — clause (i)); the right-hand side is unbounded in `n` (at
-- `T = 1`, `landauer-bound 1 n = ⌊log₂ n⌋`, with `⌊log₂ 1⌋ = 0` and
-- `⌊log₂ 2⌋ = 1`). One number cannot equal both `0` and `1`. ⊥.
--
-- So O-THERMO-∞ is `[CLOSED-NEG]`: the quantitative-collapse
-- functional provably does NOT extend to an infinite carrier as a
-- total `--safe` function. This is a settled *negative* result — a
-- genuine boundary of the theory, not an open gap. It does not touch
-- the Bennett *zero* direction, which is closed for all carriers
-- (`EchoThermodynamicsArbitrary`).
--
-- Honesty. The structural reason is also recorded positively:
-- `ℕ ↪ Echo (const y₀) y₀` exhibits the collapse fiber as infinite,
-- which is *why* no finite count exists. The impossibility theorem is
-- the sharp form that matches the obligation's wording verbatim.
--
-- Headlines (pinned in Smoke.agda):
--
--   * nat-into-collapse-fiber          -- the collapse fiber is infinite
--   * nat-into-collapse-fiber-injective
--   * collapse-cost-impossible         -- O-THERMO-∞: (i)∧(ii) ⊢ ⊥

module EchoThermoCollapseImpossible where

open import Data.Empty                            using (⊥)
import      Data.Nat.Base                         as ℕ
open        ℕ                                     using (ℕ)
open import Data.Nat.Properties                   using (*-identityˡ)
open import Data.Nat.Logarithm                    using (⌊log₂_⌋; ⌊log₂[2^n]⌋≡n)
open import Data.Fin.Base                         using (Fin)
open import Data.Product.Base                     using (Σ; _,_; proj₁)
open import Relation.Nullary.Decidable.Core       using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Echo                                  using (Echo)
open import EchoFiberCount                        using (FiberSize-fin-const)
open import EchoThermodynamics using
  ( Temperature ; Energy
  ; landauer-bound ; fiber-erasure-bound ; ⌊log₂1⌋≡0 )

----------------------------------------------------------------------
-- The structural reason: the collapse fiber is infinite.
--
-- For the constant map `c : ℕ → B`, every `n : ℕ` is a preimage of
-- `y₀`, so `ℕ` injects into `Echo c y₀`. A type into which `ℕ`
-- injects has no `Fin n` cardinality — this is *why* the
-- enumeration-count `fiber-erasure-bound` cannot exist for the
-- infinite carrier. (Recorded positively; the sharp impossibility
-- matching O-THERMO-∞'s wording is `collapse-cost-impossible` below.)
----------------------------------------------------------------------

nat-into-collapse-fiber :
  ∀ {b} {B : Set b} (y₀ : B) → ℕ → Echo {A = ℕ} (λ _ → y₀) y₀
nat-into-collapse-fiber y₀ n = n , refl

nat-into-collapse-fiber-injective :
  ∀ {b} {B : Set b} (y₀ : B) {m n : ℕ} →
  nat-into-collapse-fiber y₀ m ≡ nat-into-collapse-fiber y₀ n → m ≡ n
nat-into-collapse-fiber-injective y₀ = cong proj₁

----------------------------------------------------------------------
-- fiber-erasure-bound of the finite restriction is `landauer-bound T n`.
--
-- The restriction of the constant `ℕ → B` along any `Fin n ↪ ℕ` is
-- the constant `Fin n → B`. Its honest count is `n`
-- (`FiberSize-fin-const`, PR #58), so its erasure bound is exactly
-- `landauer-bound T n`. Specialised at `T = 1` where
-- `landauer-bound 1 n = ⌊log₂ n⌋`.
----------------------------------------------------------------------

private
  -- 0 ≡ 1 in ℕ is absurd.
  0≢1 : 0 ≡ 1 → ⊥
  0≢1 ()

  -- ⌊log₂ 2 ⌋ ≡ 1 (std-lib: `2 ^ 1` reduces to `2`).
  ⌊log₂2⌋≡1 : ⌊log₂ 2 ⌋ ≡ 1
  ⌊log₂2⌋≡1 = ⌊log₂[2^n]⌋≡n 1

  -- landauer-bound 1 n ≡ ⌊log₂ n⌋  (k = 1, `1 * 1` reduces; `1 * x`
  -- collapsed by *-identityˡ).
  lb1 : ∀ n → landauer-bound 1 n ≡ ⌊log₂ n ⌋
  lb1 n = *-identityˡ ⌊log₂ n ⌋

  feb-const :
    ∀ {b} {B : Set b} (y₀ : B)
    (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) (n : ℕ) →
    fiber-erasure-bound {n = n} (λ _ → y₀) y₀ _≟_ 1 ≡ ⌊log₂ n ⌋
  feb-const y₀ _≟_ n =
    trans (cong (landauer-bound 1) (FiberSize-fin-const {n = n} y₀ _≟_))
          (lb1 n)

  feb-const-1 :
    ∀ {b} {B : Set b} (y₀ : B)
    (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
    fiber-erasure-bound {n = 1} (λ _ → y₀) y₀ _≟_ 1 ≡ 0
  feb-const-1 y₀ _≟_ = trans (feb-const y₀ _≟_ 1) ⌊log₂1⌋≡0

  feb-const-2 :
    ∀ {b} {B : Set b} (y₀ : B)
    (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
    fiber-erasure-bound {n = 2} (λ _ → y₀) y₀ _≟_ 1 ≡ 1
  feb-const-2 y₀ _≟_ = trans (feb-const y₀ _≟_ 2) ⌊log₂2⌋≡1

----------------------------------------------------------------------
-- O-THERMO-∞ — impossibility CONFIRMED.
--
-- Any total `cost : (ℕ → B) → (y : B) → DecEq B → Temperature →
-- Energy` (clause (i): it is a function — total, no postulate, no
-- escape pragma, that is what `--safe` totality *is*) that agrees
-- with `fiber-erasure-bound` on the finite restrictions of the
-- constant map (clause (ii)) is impossible: clause (ii) at `n = 1`
-- and `n = 2` (with `T = 1`) forces its single value to be both `0`
-- and `1`. This is the doc's kill condition, second horn.
----------------------------------------------------------------------

collapse-cost-impossible :
  ∀ {b} {B : Set b}
  (y₀ : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂))
  (cost : (ℕ → B) → (y : B) →
          ((y₁ y₂ : B) → Dec (y₁ ≡ y₂)) → Temperature → Energy)
  (agree : ∀ (n : ℕ) (T : Temperature) →
             cost (λ _ → y₀) y₀ _≟_ T
               ≡ fiber-erasure-bound {n = n} (λ _ → y₀) y₀ _≟_ T) →
  ⊥
collapse-cost-impossible y₀ _≟_ cost agree =
  0≢1 (trans (sym (trans (agree 1 1) (feb-const-1 y₀ _≟_)))
             (trans (agree 2 1) (feb-const-2 y₀ _≟_)))
