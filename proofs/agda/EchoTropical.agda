{-# OPTIONS --safe --without-K #-}

module EchoTropical where

open import Echo

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

data Candidate : Set where
  a : Candidate
  b : Candidate
  c : Candidate

a≢b : a ≢ b
a≢b ()

score : Candidate → ℕ
score a = zero
score b = zero
score c = suc zero

tropical-non-injective :
  Σ Candidate (λ x1 → Σ Candidate (λ x2 → x1 ≢ x2 × score x1 ≡ score x2))
tropical-non-injective = a , b , a≢b , refl

echo-a : Echo score zero
echo-a = echo-intro score a

echo-b : Echo score zero
echo-b = echo-intro score b

echo-a≢echo-b : echo-a ≢ echo-b
echo-a≢echo-b q = a≢b (cong proj₁ q)

-- Tropical residue: a candidate plus an optimality certificate.
IsArgmin : Candidate → ℕ → Set
IsArgmin x y = score x ≡ y × (∀ z → y ≤ score z)

TropEcho : ℕ → Set
TropEcho y = Σ Candidate (λ x → IsArgmin x y)

zero≤score : ∀ z → zero ≤ score z
zero≤score a = z≤n
zero≤score b = z≤n
zero≤score c = z≤n

residue-a : TropEcho zero
residue-a = a , refl , zero≤score

residue-b : TropEcho zero
residue-b = b , refl , zero≤score

residue-a≢residue-b : residue-a ≢ residue-b
residue-a≢residue-b q = a≢b (cong proj₁ q)

echo0-to-tropical : Echo score zero → TropEcho zero
echo0-to-tropical (x , p) = x , p , zero≤score

tropical-collapse-visible : score a ≡ score b
tropical-collapse-visible = refl

distinct-candidates-same-visible-distinct-echo :
  score a ≡ score b × echo-a ≢ echo-b
distinct-candidates-same-visible-distinct-echo = refl , echo-a≢echo-b
