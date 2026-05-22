{-# OPTIONS --safe --without-K #-}

module EchoEpistemicResidue where

open import Echo
open import EchoResidue using (EchoR; echo-to-residue)

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

-- Phase B: epistemic residues (weaker evidence than full witness).
data Magnitude : Set where
  m3 : Magnitude
  m4 : Magnitude

square-mag : Magnitude → ℕ
square-mag m3 = 9
square-mag m4 = 16

data Signed : Set where
  plus : Magnitude → Signed
  minus : Magnitude → Signed

square-signed : Signed → ℕ
square-signed (plus m) = square-mag m
square-signed (minus m) = square-mag m

kappa-mag : Signed → Magnitude
kappa-mag (plus m) = m
kappa-mag (minus m) = m

MagCert : Magnitude → ℕ → Set
MagCert m y = square-mag m ≡ y

square-sound : ∀ s → MagCert (kappa-mag s) (square-signed s)
square-sound (plus _) = refl
square-sound (minus _) = refl

to-epistemic :
  ∀ {y : ℕ} →
  Echo square-signed y → EchoR Magnitude MagCert y
to-epistemic =
  echo-to-residue square-signed kappa-mag MagCert square-sound

echo-plus3 : Echo square-signed 9
echo-plus3 = echo-intro square-signed (plus m3)

echo-minus3 : Echo square-signed 9
echo-minus3 = echo-intro square-signed (minus m3)

plus3≢minus3 : plus m3 ≢ minus m3
plus3≢minus3 ()

echo-plus3≢echo-minus3 : echo-plus3 ≢ echo-minus3
echo-plus3≢echo-minus3 p = plus3≢minus3 (cong proj₁ p)

epistemic-plus3 : EchoR Magnitude MagCert 9
epistemic-plus3 = to-epistemic echo-plus3

epistemic-minus3 : EchoR Magnitude MagCert 9
epistemic-minus3 = to-epistemic echo-minus3

epistemic-collision : epistemic-plus3 ≡ epistemic-minus3
epistemic-collision = refl

-- Residue still supports inference: for visible value 9, only m3 is certified.
epistemic-9-classifies :
  ∀ (e : EchoR Magnitude MagCert 9) → proj₁ e ≡ m3
epistemic-9-classifies (m3 , refl) = refl
epistemic-9-classifies (m4 , ())

no-section-to-epistemic :
  ¬ (Σ (EchoR Magnitude MagCert 9 → Echo square-signed 9)
       (λ raise → ∀ e → raise (to-epistemic e) ≡ e))
no-section-to-epistemic (raise , sec) =
  echo-plus3≢echo-minus3 (trans (sym p-plus3) p-minus3')
  where
    p-plus3 : raise (to-epistemic echo-plus3) ≡ echo-plus3
    p-plus3 = sec echo-plus3

    p-minus3 : raise (to-epistemic echo-minus3) ≡ echo-minus3
    p-minus3 = sec echo-minus3

    p-minus3' : raise (to-epistemic echo-plus3) ≡ echo-minus3
    p-minus3' = trans (cong raise epistemic-collision) p-minus3

strict-epistemic-weakening :
  Σ (Echo square-signed 9 → EchoR Magnitude MagCert 9)
    (λ lower →
      ¬ (Σ (EchoR Magnitude MagCert 9 → Echo square-signed 9)
           (λ raise → ∀ e → raise (lower e) ≡ e)))
strict-epistemic-weakening = to-epistemic , no-section-to-epistemic
