{-# OPTIONS --safe --without-K #-}

-- EchoThermodynamics: honest finite-domain Landauer / Bennett bounds.
--
-- This module replaces an earlier draft in which `FiberSize` was
-- hardcoded to 1, which collapsed the Landauer factor `⌊log₂ N⌋`
-- to zero everywhere and rendered the headline claims vacuous.
-- The current module imports the actual fiber count
-- `FiberSize-fin` from `EchoFiberCount` and states the two
-- extremal bounds — the Bennett (reversible) zero-cost case at
-- `FiberSize = 1`, and the Landauer (full collapse) worst case
-- at `FiberSize = n`.
--
-- Scope and honesty.
--
-- * Domain is `Fin n` only. The earlier `ProgramState = ℕ → ℕ`
--   carrier is gone: counting fibers of a function on an
--   infinite type is not constructively meaningful here, and
--   pretending otherwise was the original sin of the deleted
--   `ECHO-CNO-BRIDGE-SUMMARY.md`.
--
-- * The Boltzmann constant `k` and temperature `T` live in
--   arbitrary natural-number units. Quantitative physics is not
--   the goal — the goal is an honest *shape* for the bound:
--   linear in `k`, linear in `T`, logarithmic in the fiber
--   count.
--
-- * `bennett-reversible` is stated as a corollary of
--   `FiberSize-fin ≡ 1` (the `EchoFiberCount.FiberSize-fin-id-zero`
--   instance discharges this for `id : Fin (suc m) → Fin (suc m)`
--   at index zero) and `⌊log₂ 1 ⌋ ≡ 0`. The Bennett intuition —
--   reversible computations preserve all information, hence
--   erasure cost is zero — is captured exactly at the points
--   where the count is one.
--
-- * `landauer-collapse` is the worst-case shape:
--   `(∀ x → f x ≡ y) → bound ≡ k · T · ⌊log₂ n⌋`. Constant maps
--   are the canonical instance.
--
-- Headlines (pinned in Smoke.agda):
--
--   * landauer-bound                  -- the bound shape itself
--   * fiber-erasure-bound             -- bound applied at a fiber
--   * bennett-reversible              -- FiberSize ≡ 1 ⇒ bound ≡ 0
--   * bennett-reversible-id-zero      -- id at zero: bound ≡ 0
--   * landauer-collapse               -- constant map: bound = k·T·⌊log₂ n⌋

module EchoThermodynamics where

open import Function.Base                         using (_∘_)
import      Data.Nat.Base                         as ℕ
open        ℕ                                     using (ℕ; _*_)
open import Data.Nat.Properties                   using (*-zeroʳ)
open import Data.Nat.Logarithm                    using (⌊log₂_⌋; ⌊log₂[2^n]⌋≡n)
open import Data.Fin.Base                         using (Fin; zero)
open import Relation.Nullary.Decidable.Core       using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import EchoFiberCount                        using
  ( FiberSize-fin
  ; FiberSize-fin-id-zero
  ; FiberSize-fin-const
  ; FiberSize-fin-all-hit
  )

----------------------------------------------------------------------
-- Thermodynamic types (simplified units)
----------------------------------------------------------------------

Temperature : Set
Temperature = ℕ

Energy : Set
Energy = ℕ

-- Boltzmann constant in arbitrary units.
k : ℕ
k = 1

----------------------------------------------------------------------
-- The bound
----------------------------------------------------------------------

-- Landauer's bound for erasing log₂ n bits at temperature T.
-- Linear in T, logarithmic (floor) in n. The `⌊log₂ 0 ⌋ = 0`
-- and `⌊log₂ 1 ⌋ = 0` corner cases naturally give zero — there
-- is nothing to erase when the alternatives count is below 2.

landauer-bound : Temperature → ℕ → Energy
landauer-bound T n = k * T * ⌊log₂ n ⌋

-- Erasure bound for the fiber of `f : Fin n → B` over `y`.
-- The erasure cost is set by how many domain points are
-- collapsed onto `y` — exactly the fiber count.

fiber-erasure-bound :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) →
  ((y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  Temperature → Energy
fiber-erasure-bound f y _≟_ T = landauer-bound T (FiberSize-fin f y _≟_)

----------------------------------------------------------------------
-- Auxiliary: ⌊log₂ 1⌋ ≡ 0.
--
-- Specialisation of `⌊log₂[2^n]⌋≡n` at `n = 0`, exploiting that
-- `2 ^ 0 = 1` definitionally. Bennett's reversible-computation
-- bound runs on this lemma plus `*-zeroʳ`.
----------------------------------------------------------------------

⌊log₂1⌋≡0 : ⌊log₂ 1 ⌋ ≡ 0
⌊log₂1⌋≡0 = ⌊log₂[2^n]⌋≡n 0

----------------------------------------------------------------------
-- bennett-reversible
--
-- If the fiber over `y` has size 1 — exactly one preimage —
-- then the erasure bound is zero at every temperature. This is
-- the constructive content of the Bennett picture: a reversible
-- computation has no fan-in, hence no thermodynamically
-- mandatory dissipation under Landauer. Stated as a clean
-- corollary of `FiberSize-fin ≡ 1` and `⌊log₂ 1⌋ ≡ 0`.
----------------------------------------------------------------------

bennett-reversible :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂))
  (T : Temperature) →
  FiberSize-fin f y _≟_ ≡ 1 →
  fiber-erasure-bound f y _≟_ T ≡ 0
bennett-reversible f y _≟_ T fs1
  rewrite fs1 | ⌊log₂1⌋≡0 = *-zeroʳ (k * T)

----------------------------------------------------------------------
-- bennett-reversible-id-zero
--
-- Concrete instance of `bennett-reversible` for the identity map
-- on `Fin (suc m)` at index `zero`. The fiber size is 1 by
-- `FiberSize-fin-id-zero`, hence the erasure bound is 0.
----------------------------------------------------------------------

bennett-reversible-id-zero :
  ∀ {m : ℕ} (_≟_ : (a b : Fin (ℕ.suc m)) → Dec (a ≡ b))
  (T : Temperature) →
  fiber-erasure-bound {n = ℕ.suc m} (λ x → x) zero _≟_ T ≡ 0
bennett-reversible-id-zero {m} _≟_ T =
  bennett-reversible (λ x → x) zero _≟_ T (FiberSize-fin-id-zero _≟_)

----------------------------------------------------------------------
-- landauer-collapse
--
-- The worst-case shape: if every input maps to the same `y`,
-- the fiber size is exactly `n`, and the erasure bound is the
-- full Landauer cost `k · T · ⌊log₂ n⌋`. The constant function
-- `(λ _ → y₀)` is the canonical instance — every Fin-index is
-- collapsed onto a single output.
----------------------------------------------------------------------

landauer-collapse :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂))
  (T : Temperature) →
  (∀ x → f x ≡ y) →
  fiber-erasure-bound f y _≟_ T ≡ k * T * ⌊log₂ n ⌋
landauer-collapse f y _≟_ T h =
  cong (λ z → k * T * ⌊log₂ z ⌋) (FiberSize-fin-all-hit f y _≟_ h)

----------------------------------------------------------------------
-- Companion remark on what is NOT claimed.
--
-- This module proves *bound-shape* lemmas at the finite-domain
-- `Fin n` level. It does NOT claim:
--
--   * that any specific physical computation realises the bound
--     (the bound is a lower bound; physical reality may dissipate
--     more);
--   * that arbitrary "CNO" programs (state-preserving programs
--     over `ProgramState = ℕ → ℕ`) have zero erasure cost — that
--     would require either a finite-state restriction or an
--     extension of `FiberSize-fin` to a measure-theoretic count
--     on infinite types, neither of which is available here;
--   * that Shannon-entropy / informational arguments are
--     formalised — they are not. See `docs/echo-types/roadmap.md`
--     for the open thermodynamic items.
----------------------------------------------------------------------
