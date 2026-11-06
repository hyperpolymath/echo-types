{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

module EchoThinPreorderExample where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Echo.Index.ThinPoset using (ThinPoset)

-- The legacy record requires a thin preorder, but no antisymmetry law.
-- Its name therefore does not justify equality of mutually reachable objects.
indiscrete : ThinPoset 0ℓ 0ℓ
indiscrete = record
  { Ix = Bool
  ; _≤_ = λ _ _ → ⊤
  ; ≤-refl = tt
  ; ≤-trans = λ _ _ → tt
  ; ≤-thin = λ { tt tt → refl }
  }

no-antisymmetry :
  (∀ (a b : Bool) → ⊤ → ⊤ → a ≡ b) → ⊥
no-antisymmetry antisym with antisym true false tt tt
... | ()
