{-# OPTIONS --safe --without-K #-}

module EchoResidue where

open import Echo
open import EchoCharacteristic using (collapse; echo-true; echo-false; echo-true≢echo-false)

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

-- Weakened echo: keep residue r plus a certification relation to visible y.
EchoR :
  ∀ {b c r} {B : Set b} →
  (C : Set c) → (Cert : C → B → Set r) → B → Set (c ⊔ r)
EchoR C Cert y = Σ C (λ r → Cert r y)

-- Every full echo can be lowered to a residue echo, provided residue soundness.
echo-to-residue :
  ∀ {a b c r} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B)
  (κ : A → C)
  (Cert : C → B → Set r)
  (sound : ∀ x → Cert (κ x) (f x))
  {y : B} →
  Echo f y → EchoR C Cert y
echo-to-residue f κ Cert sound (x , p) = κ x , subst (Cert (κ x)) p (sound x)

-- Collapse-specific strict weakening counterexample.
TrivialCert : ⊤ → ⊤ → Set
TrivialCert _ _ = ⊤

collapse-kappa : Bool → ⊤
collapse-kappa _ = tt

collapse-sound : ∀ b → TrivialCert (collapse-kappa b) (collapse b)
collapse-sound _ = tt

collapse-to-residue : Echo collapse tt → EchoR ⊤ TrivialCert tt
collapse-to-residue =
  echo-to-residue collapse collapse-kappa TrivialCert collapse-sound

collapse-residue-same :
  collapse-to-residue echo-true ≡ collapse-to-residue echo-false
collapse-residue-same = refl

-- No section exists that recovers the original full echo after lowering.
no-section-collapse-to-residue :
  ¬ (Σ (EchoR ⊤ TrivialCert tt → Echo collapse tt)
       (λ reify → ∀ e → reify (collapse-to-residue e) ≡ e))
no-section-collapse-to-residue (reify , sec) =
  echo-true≢echo-false (trans (sym p-true) p-false')
  where
    p-true : reify (collapse-to-residue echo-true) ≡ echo-true
    p-true = sec echo-true

    p-false : reify (collapse-to-residue echo-false) ≡ echo-false
    p-false = sec echo-false

    p-false' : reify (collapse-to-residue echo-true) ≡ echo-false
    p-false' = trans (cong reify collapse-residue-same) p-false

-- M3 pass witness: explicit weakening with a proof of non-recoverability.
strict-weakening-collapse :
  Σ (Echo collapse tt → EchoR ⊤ TrivialCert tt)
    (λ lower →
      ¬ (Σ (EchoR ⊤ TrivialCert tt → Echo collapse tt)
           (λ raise → ∀ e → raise (lower e) ≡ e)))
strict-weakening-collapse = collapse-to-residue , no-section-collapse-to-residue
