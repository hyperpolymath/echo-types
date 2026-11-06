{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module Echo.Measure.Composition where

open import Level using (Level; _⊔_)
open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Properties using (++-monoid; length-isMonoidHomomorphism)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (+-0-monoid; ≤-refl)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import EchoFiniteResidue using (ExactRecovery; recovery-forbids-residue-collision)
open import Echo.Modality.Core using (grade-echoModality)
open import Echo.Measure.Interface using (ResidueMeasure)
open import Echo.Measure.Examples using (ℕ-≤)

-- Composition is ADDITIONAL to the existing ordered-measure seam. Both
-- source and target are supplied LAWFUL monoids (including associativity
-- and units); their equivalence relations need not be propositional equality.
-- This is the standard monoid-homomorphism contract. It does not endow Echo
-- with a resource algebra, grading, naturality, a semiring, or an order.
record CompositionalMeasure {e e≈ r r≈ : Level}
  (Evidence : Monoid e e≈) (Resource : Monoid r r≈)
  : Set (e ⊔ e≈ ⊔ r ⊔ r≈) where
  field
    measure : Monoid.Carrier Evidence → Monoid.Carrier Resource
    preserves : IsMonoidHomomorphism
      (Monoid.rawMonoid Evidence) (Monoid.rawMonoid Resource) measure

  open IsMonoidHomomorphism preserves public
    renaming (ε-homo to measure-unit; homo to measure-combine)

-- The exact same length/append pattern is independently present in the
-- Lean tropical-types bridge. This Agda proof reuses the standard library;
-- it is not a checked Lean-to-Agda translation or a novelty claim.
list-length-measure : (A : Set) →
  CompositionalMeasure (++-monoid A) +-0-monoid
list-length-measure A = record
  { measure = length
  ; preserves = length-isMonoidHomomorphism A
  }

equal-cost : length (true ∷ []) ≡ length (false ∷ [])
equal-cost = refl

distinct-evidence : (true ∷ []) ≢ (false ∷ [])
distinct-evidence ()

-- Even a lawful compositional cost can erase evidence. Exact recovery from
-- a constant public observation and this cost is impossible.
length-cost-cannot-recover :
  ExactRecovery {A = List Bool} (λ _ → tt) length → ⊥
length-cost-cannot-recover recovery =
  recovery-forbids-residue-collision recovery distinct-evidence refl equal-cost

-- Conversely, monotonicity alone does not supply unit preservation.
-- The constant-one measure satisfies the existing ordered seam, but cannot
-- be an additive cost homomorphism whose target unit is zero.
constant-one-monotone : ResidueMeasure grade-echoModality ℕ-≤
constant-one-monotone = record
  { measure = λ _ → 1
  ; monotone = λ _ _ → ≤-refl
  }

constant-one-not-additive-unit : _≡_ {A = ℕ} 1 0 → ⊥
constant-one-not-additive-unit ()

constant-one-not-homomorphism : (A : Set) →
  IsMonoidHomomorphism (Monoid.rawMonoid (++-monoid A))
    (Monoid.rawMonoid +-0-monoid) (λ _ → 1) → ⊥
constant-one-not-homomorphism A h =
  constant-one-not-additive-unit (IsMonoidHomomorphism.ε-homo h)
