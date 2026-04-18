{-# OPTIONS --safe --without-K #-}

module EchoExamples where

open import Echo
open import EchoCharacteristic using (collapse; echo-true; echo-false)
open import EchoResidue using (collapse-to-residue; collapse-residue-same)

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

true≢false : true ≢ false
true≢false ()

-- Example 1: x ↦ x², visible value 9 with hidden sign provenance.
data SignedNine : Set where
  plus3 : SignedNine
  minus3 : SignedNine

plus3≢minus3 : plus3 ≢ minus3
plus3≢minus3 ()

square9 : SignedNine → ℕ
square9 plus3 = 9
square9 minus3 = 9

square9-non-injective :
  Σ SignedNine
    (λ x1 → Σ SignedNine (λ x2 → x1 ≢ x2 × square9 x1 ≡ square9 x2))
square9-non-injective = plus3 , minus3 , plus3≢minus3 , refl

echo-plus3 : Echo square9 9
echo-plus3 = echo-intro square9 plus3

echo-minus3 : Echo square9 9
echo-minus3 = echo-intro square9 minus3

echo-plus3≢echo-minus3 : echo-plus3 ≢ echo-minus3
echo-plus3≢echo-minus3 p = plus3≢minus3 (cong proj₁ p)

square9-classification : ∀ (e : Echo square9 9) → proj₁ e ≡ plus3 ⊎ proj₁ e ≡ minus3
square9-classification (plus3 , _) = inj₁ refl
square9-classification (minus3 , _) = inj₂ refl

-- Example 2: structured projection that forgets detail but keeps constraints.
State : Set
State = Bool × Bool

visible : State → Bool
visible = proj₁

visible-constraint : ∀ {y : Bool} (e : Echo visible y) → proj₁ (proj₁ e) ≡ y
visible-constraint (_ , p) = p

stateA : Echo visible true
stateA = (true , true) , refl

stateB : Echo visible true
stateB = (true , false) , refl

stateA≢stateB : stateA ≢ stateB
stateA≢stateB p = true≢false (cong (λ e → proj₂ (proj₁ e)) p)

-- Example 3: quotient-like collapse with remembered representative class.
quot : Bool → ⊤
quot _ = tt

quot-non-injective :
  Σ Bool (λ b1 → Σ Bool (λ b2 → b1 ≢ b2 × quot b1 ≡ quot b2))
quot-non-injective = true , false , true≢false , refl

quot-echo-true : Echo quot tt
quot-echo-true = echo-intro quot true

quot-echo-false : Echo quot tt
quot-echo-false = echo-intro quot false

quot-echo-classification :
  ∀ (e : Echo quot tt) → proj₁ e ≡ true ⊎ proj₁ e ≡ false
quot-echo-classification (true , _) = inj₁ refl
quot-echo-classification (false , _) = inj₂ refl

-- Example 4: same collapse residue from distinct full echoes.
collapse-residue-identifies :
  collapse-to-residue echo-true ≡ collapse-to-residue echo-false
collapse-residue-identifies = collapse-residue-same
