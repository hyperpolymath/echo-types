{-# OPTIONS --safe --without-K #-}

module EchoCharacteristic where

open import Echo

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

true≢false : true ≢ false
true≢false ()

-- A maximally collapsing non-injective computation.
collapse : Bool → ⊤
collapse _ = tt

-- Non-injectivity is explicit: distinct sources can share the same visible output.
collapse-non-injective :
  Σ Bool (λ x1 → Σ Bool (λ x2 → x1 ≢ x2 × collapse x1 ≡ collapse x2))
collapse-non-injective = true , false , true≢false , refl

-- Irreversible at the plain-output level: no section can reconstruct every source.
no-section-collapse :
  ¬ (Σ (⊤ → Bool) (λ g → ∀ b → g (collapse b) ≡ b))
no-section-collapse (g , sec) = true≢false (trans (sym (sec true)) (sec false))

-- Yet echoes retain proof-relevant distinctions for the same visible output.
echo-true : Echo collapse tt
echo-true = echo-intro collapse true

echo-false : Echo collapse tt
echo-false = echo-intro collapse false

echo-true≢echo-false : echo-true ≢ echo-false
echo-true≢echo-false p = true≢false (cong proj₁ p)

-- A structured-loss example: projection forgets the second component only.
State : Set
State = Bool × Bool

visible : State → Bool
visible = proj₁

-- Echo witness enforces the retained constraint on visible state.
visible-constraint : ∀ {y : Bool} (e : Echo visible y) → proj₁ (proj₁ e) ≡ y
visible-constraint (_ , p) = p

state₁ : Echo visible true
state₁ = (true , true) , refl

state₂ : Echo visible true
state₂ = (true , false) , refl

-- Same visible value, different retained witnesses.
state₁≢state₂ : state₁ ≢ state₂
state₁≢state₂ p = true≢false (cong (λ e → proj₂ (proj₁ e)) p)

-- Plain visible output still cannot reconstruct full source state.
no-section-visible :
  ¬ (Σ (Bool → State) (λ g → ∀ s → g (visible s) ≡ s))
no-section-visible (g , sec) =
  true≢false
    (trans
      (sym (cong proj₂ (sec (true , true))))
      (cong proj₂ (sec (true , false))))

-- Characteristic preimage class: every echo over collapse tt constrains source to Bool cases.
collapse-classification :
  ∀ (e : Echo collapse tt) → proj₁ e ≡ true ⊎ proj₁ e ≡ false
collapse-classification (true , _) = inj₁ refl
collapse-classification (false , _) = inj₂ refl

-- Echo transport along a commuting square in this concrete setting.
flip₁ : State → State
flip₁ (b , c) = not b , c

flip-square : ∀ s → visible (flip₁ s) ≡ not (visible s)
flip-square (true , _) = refl
flip-square (false , _) = refl

transport-visible-not :
  ∀ {y : Bool} → Echo visible y → Echo visible (not y)
transport-visible-not = map-square visible visible flip₁ not flip-square
