{-# OPTIONS --safe --without-K #-}

module EchoLinear where

open import Echo
open import EchoCharacteristic using (collapse; echo-true; echo-false; echo-true≢echo-false)
open import EchoResidue
  using
    ( EchoR
    ; TrivialCert
    ; collapse-to-residue
    ; collapse-residue-same
    ; no-section-collapse-to-residue
    )

open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

data Mode : Set where
  linear : Mode
  affine : Mode

LEcho : Mode → Set
LEcho linear = Echo collapse tt
LEcho affine = EchoR ⊤ TrivialCert tt

weaken : LEcho linear → LEcho affine
weaken = collapse-to-residue

weaken-collapses-distinction : weaken echo-true ≡ weaken echo-false
weaken-collapses-distinction = collapse-residue-same

strict-linear-example :
  Σ (LEcho linear)
    (λ e1 → Σ (LEcho linear) (λ e2 → e1 ≢ e2 × weaken e1 ≡ weaken e2))
strict-linear-example = echo-true , echo-false , echo-true≢echo-false , collapse-residue-same

no-section-weaken :
  ¬ (Σ (LEcho affine → LEcho linear)
       (λ raise → ∀ e → raise (weaken e) ≡ e))
no-section-weaken = no-section-collapse-to-residue

affine-canonical : ∀ (e : LEcho affine) → e ≡ (tt , tt)
affine-canonical (tt , tt) = refl

affine-all-equal : ∀ (e1 e2 : LEcho affine) → e1 ≡ e2
affine-all-equal e1 e2 = trans (affine-canonical e1) (sym (affine-canonical e2))
