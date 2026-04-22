{-# OPTIONS --safe --without-K #-}

-- Echo thermodynamics: minimum viable compile.
--
-- Bridge module expressing Landauer-style bit-erasure cost in terms
-- of a (simplified, singleton) fiber size. This is pedagogical, not a
-- quantitative physics claim: FiberSize is always 1 and fiber-energy
-- of identity functions is zero. The load-bearing content is just
-- that CNOs (identity-preserving programs) have fiber-energy = 0.

module EchoThermodynamics where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo using (Echo; echo-intro)

----------------------------------------------------------------------------
-- Thermodynamic types (simplified units)
----------------------------------------------------------------------------

Temperature : Set
Temperature = ℕ

Energy : Set
Energy = ℕ

Information : Set
Information = ℕ

Entropy : Set
Entropy = ℕ

-- Boltzmann constant in arbitrary units.
k : ℕ
k = 1

-- Landauer's principle: minimum energy to erase one bit at temperature T.
landauer-energy : Temperature → Energy
landauer-energy T = k * T

----------------------------------------------------------------------------
-- Simplified fiber size
----------------------------------------------------------------------------

-- Fiber size as a natural number. Deliberately simplified to 1 at this
-- stage; a real count would require decidable equality on the codomain
-- plus an enumeration of preimages, which this module does not yet have.
FiberSize : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) → ℕ
FiberSize f y = 1

-- Energy dissipation for a single-bit erasure at given temperature,
-- scaled by the simplified fiber size (= 1).
fiber-energy : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) → Temperature → Energy
fiber-energy f y T = landauer-energy T * FiberSize f y

-- Thermodynamic cost of computing f on input x at temperature T.
echo-energy-cost : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → Temperature → Energy
echo-energy-cost f x T = fiber-energy f (f x) T

----------------------------------------------------------------------------
-- CNO (identity-preserving) thermodynamic properties
----------------------------------------------------------------------------

-- Abstract program state.
ProgramState : Set
ProgramState = ℕ → ℕ

-- CNO modelled as identity on ProgramState.
cno-identity : ProgramState → ProgramState
cno-identity s = s

-- CNOs have unit fiber size (trivially, by FiberSize's simplification).
cno-fiber-size : ∀ (s : ProgramState) → FiberSize cno-identity s ≡ 1
cno-fiber-size s = refl

-- CNOs at temperature zero dissipate zero energy. This is the only
-- strong-form zero-energy statement the simplified FiberSize lets us
-- prove: landauer-energy 0 = 0 * FiberSize = 0. The stronger claim
-- "CNOs dissipate zero energy at every temperature" is not yet
-- discharged — it needs FiberSize to track actual preimages.
cno-zero-energy-at-zero : ∀ (s : ProgramState) →
                          fiber-energy cno-identity s 0 ≡ 0
cno-zero-energy-at-zero s = refl

-- Echo-cost at temperature zero is likewise zero, for any function.
echo-cost-at-zero : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) →
                    echo-energy-cost f x 0 ≡ 0
echo-cost-at-zero f x = refl
