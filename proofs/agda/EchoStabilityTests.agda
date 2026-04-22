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

open import Data.Nat.Base using (ℕ; zero)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo using (Echo; echo-intro; MapOver; map-over; map-over-id; map-over-comp)
open import EchoThermodynamics using
  ( Temperature
  ; fiber-energy
  ; echo-energy-cost
  ; cno-identity
  ; cno-fiber-size
  ; cno-zero-energy-at-zero
  ; echo-cost-at-zero
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
----------------------------------------------------------------------------

-- Test 4. The CNO fiber has size one.
cno-fiber-is-one : ∀ (s : ℕ → ℕ) → cno-fiber-size s ≡ refl
cno-fiber-is-one s = refl

-- Test 5. At temperature zero, a CNO dissipates zero energy.
cno-zero-T-check : ∀ (s : ℕ → ℕ) →
                   fiber-energy cno-identity s 0 ≡ 0
cno-zero-T-check s = cno-zero-energy-at-zero s

-- Test 6. At temperature zero, *any* echo-energy-cost is zero. Locks
-- the shape of the cost function against changes to FiberSize.
echo-cost-zero-T-check : ∀ {a b} {A : Set a} {B : Set b}
                        (f : A → B) (x : A) →
                        echo-energy-cost f x 0 ≡ 0
echo-cost-zero-T-check f x = echo-cost-at-zero f x

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
-- * Thermodynamic optimality / energy hierarchy: needs a real fiber
--   count and a `≤` relation on energies, neither of which the
--   simplified EchoThermodynamics yet provides.
