{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

module EchoGradedComonadNaturality where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import EchoGradedComonadInterface using (GradedComonadStructure)

-- Companion to the existing API. Morphisms are functions with pointwise
-- equality; no function extensionality or UIP for arbitrary types is used.
record NaturalGradedComonad (S : GradedComonadStructure) : Set₁ where
  open GradedComonadStructure S
  field
    mapD-cong : ∀ g {A B} {f h : A → B} →
      (∀ a → f a ≡ h a) → ∀ (x : D g A) → mapD g f x ≡ mapD g h x
    ε-natural : ∀ {A B} (f : A → B) (x : D 1G A) →
      ε (mapD 1G f x) ≡ f (ε x)
    δ-natural : ∀ g h {A B} (f : A → B) (x : D (g ·G h) A) →
      δ g h (mapD (g ·G h) f x) ≡ mapD g (mapD h f) (δ g h x)
    -- Equality of grades alone is proof irrelevant. This does not assert
    -- proof irrelevance for values, residues, or every type in Set.
    grade-isSet : ∀ {g h : G} (p q : g ≡ h) → p ≡ q
