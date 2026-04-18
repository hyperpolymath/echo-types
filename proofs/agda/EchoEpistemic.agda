{-# OPTIONS --safe --without-K #-}

module EchoEpistemic where

open import EchoChoreo

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

-- Epistemic indistinguishability from a role-local observation.
Indist : Role → Global → Global → Set
Indist r g g' = obs r g ≡ obs r g'

indist-refl : ∀ {r : Role} {g : Global} → Indist r g g
indist-refl = refl

indist-sym : ∀ {r : Role} {g g' : Global} → Indist r g g' → Indist r g' g
indist-sym = sym

indist-trans :
  ∀ {r : Role} {g1 g2 g3 : Global} →
  Indist r g1 g2 → Indist r g2 g3 → Indist r g1 g3
indist-trans = trans

-- Knowledge at visible value y: P holds for every witness compatible with y.
Knows : Role → (Global → Set) → Bool → Set
Knows r P y = ∀ e → P (proj₁ (RoleEcho r y ∋ e))
  where
    infix 4 _∋_
    _∋_ : ∀ {ℓ} (A : Set ℓ) → A → A
    _ ∋ x = x

knows-from-preimage :
  ∀ {r : Role} {y : Bool} {P : Global → Set} →
  (∀ g → obs r g ≡ y → P g) →
  Knows r P y
knows-from-preimage pre (g , p) = pre g p

knowledge-monotone :
  ∀ {r : Role} {y : Bool} {P Q : Global → Set} →
  (∀ g → P g → Q g) →
  Knows r P y →
  Knows r Q y
knowledge-monotone pq k e = pq (proj₁ e) (k e)

ServerIsTrue : Global → Set
ServerIsTrue g = proj₂ g ≡ true

ServerIsFalse : Global → Set
ServerIsFalse g = proj₂ g ≡ false

-- Client observing `true` does not determine the hidden server bit.
not-knows-server-true-at-client-true : ¬ Knows Client ServerIsTrue true
not-knows-server-true-at-client-true k =
  true≢false (sym (k ((true , false) , refl)))

not-knows-server-false-at-client-true : ¬ Knows Client ServerIsFalse true
not-knows-server-false-at-client-true k =
  true≢false (k ((true , true) , refl))

-- If two globals are indistinguishable, they share a common visible echo value.
shared-echo-from-indist :
  ∀ {r : Role} {g g' : Global} →
  Indist r g g' →
  Σ Bool (λ y → RoleEcho r y × RoleEcho r y)
shared-echo-from-indist {r} {g} {g'} p =
  obs r g , (g , refl) , (g' , sym p)

-- Any two echoes at the same visible value induce indistinguishable states.
indist-from-two-echoes :
  ∀ {r : Role} {y : Bool} →
  (e1 e2 : RoleEcho r y) →
  Indist r (proj₁ e1) (proj₁ e2)
indist-from-two-echoes (g1 , p1) (g2 , p2) = trans p1 (sym p2)

-- Knowledge transport through choreography steps that preserve client visibility.
knowledge-along-client-stability :
  ∀ {y : Bool} {P : Global → Set} →
  (∀ g → P g → P (scramble-server g)) →
  Knows Client P y →
  ∀ e → P (proj₁ (client-stability e))
knowledge-along-client-stability inv k (g , p) = inv g (k (g , p))
