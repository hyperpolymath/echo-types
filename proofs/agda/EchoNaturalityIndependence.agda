{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

module EchoNaturalityIndependence where

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- A categorical independence countermodel, not an inhabitant of the
-- polymorphic Set → Set interface GradedComonadStructure. There is one
-- object and its endomorphisms are all Boolean functions. No type case
-- analysis or polymorphic Boolean negation is being assumed.
Obj : Set
Obj = ⊤

Endo : Set
Endo = Bool → Bool

Hom : Obj → Obj → Set
Hom _ _ = Endo

infix 4 _≈_
_≈_ : Endo → Endo → Set
f ≈ g = ∀ b → f b ≡ g b

≈-refl : ∀ {f} → f ≈ f
≈-refl b = refl

≈-sym : ∀ {f g} → f ≈ g → g ≈ f
≈-sym p b = sym (p b)

≈-trans : ∀ {f g h} → f ≈ g → g ≈ h → f ≈ h
≈-trans p q b = trans (p b) (q b)

compose-cong : ∀ {f f′ g g′ : Endo} → f ≈ f′ → g ≈ g′ →
  (f ∘ g) ≈ (f′ ∘ g′)
compose-cong {f′ = f′} {g = g} p q b = trans (p (g b)) (cong f′ (q b))

identity-left : ∀ (f : Endo) → (id ∘ f) ≈ f
identity-left f b = refl

identity-right : ∀ (f : Endo) → (f ∘ id) ≈ f
identity-right f b = refl

composition-assoc : ∀ (f g h : Endo) → ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h))
composition-assoc f g h b = refl

-- The singleton grade monoid and identity endofunctor.
Grade : Set
Grade = ⊤

unit : Grade
unit = tt

infixl 6 _∙_
_∙_ : Grade → Grade → Grade
_ ∙ _ = tt

grade-left-unit : ∀ g → unit ∙ g ≡ g
grade-left-unit tt = refl

grade-right-unit : ∀ g → g ∙ unit ≡ g
grade-right-unit tt = refl

grade-assoc : ∀ g h k → (g ∙ h) ∙ k ≡ g ∙ (h ∙ k)
grade-assoc g h k = refl

D₀ : Grade → Obj → Obj
D₀ _ o = o

mapD : Grade → Endo → Endo
mapD _ f = f

mapD-cong : ∀ g {f h} → f ≈ h → mapD g f ≈ mapD g h
mapD-cong g p = p

mapD-id : ∀ g → mapD g id ≈ id
mapD-id g b = refl

mapD-compose : ∀ g (f h : Endo) → mapD g (f ∘ h) ≈ (mapD g f ∘ mapD g h)
mapD-compose g f h b = refl

ε : Endo
ε = not

δ : Grade → Grade → Endo
δ _ _ = not

not-involutive : ∀ b → not (not b) ≡ b
not-involutive true = refl
not-involutive false = refl

counit-right : ∀ g → (ε ∘ δ unit g) ≈ id
counit-right g = not-involutive

counit-left : ∀ g → (mapD g ε ∘ δ g unit) ≈ id
counit-left g = not-involutive

coassoc : ∀ g h k → (δ g h ∘ δ (g ∙ h) k) ≈
  (mapD g (δ h k) ∘ δ g (h ∙ k))
coassoc g h k b = refl

constant-true : Endo
constant-true _ = true

-- Both proposed naturality squares fail on the same endomorphism.
ε-naturality-fails : ((ε ∘ mapD unit constant-true) ≈ (constant-true ∘ ε)) → ⊥
ε-naturality-fails natural with natural true
... | ()

δ-naturality-fails : ∀ g h →
  ((δ g h ∘ mapD (g ∙ h) constant-true) ≈
   (mapD g (mapD h constant-true) ∘ δ g h)) → ⊥
δ-naturality-fails g h natural with natural true
... | ()
