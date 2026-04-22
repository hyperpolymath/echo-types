{-# OPTIONS --safe --without-K #-}

-- Stage E7 bridge scaffold for docs/buchholz-plan.adoc.
--
-- Collapse a Buchholz term to a visible Ω-index marker and exhibit
-- non-injectivity at the plain-output level.

module EchoOrdinal where

open import Echo using (Echo; echo-intro)

open import Data.Product.Base using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Ordinal.OmegaMarkers using (OmegaIndex; Omega0)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)

ordinal-collapse : BT → OmegaIndex
ordinal-collapse bzero       = Omega0
ordinal-collapse (bOmega μ)  = μ
ordinal-collapse (bplus x y) = ordinal-collapse x
ordinal-collapse (bpsi μ α)  = μ

ordinal-left : BT
ordinal-left = bOmega Omega0

ordinal-right : BT
ordinal-right = bpsi Omega0 bzero

ordinal-left≢ordinal-right : ordinal-left ≢ ordinal-right
ordinal-left≢ordinal-right ()

ordinal-collapse-non-injective :
  Σ BT (λ t1 → Σ BT (λ t2 → t1 ≢ t2 × ordinal-collapse t1 ≡ ordinal-collapse t2))
ordinal-collapse-non-injective =
  ordinal-left , ordinal-right , ordinal-left≢ordinal-right , refl

ordinal-echo-left : Echo ordinal-collapse Omega0
ordinal-echo-left = echo-intro ordinal-collapse ordinal-left

ordinal-echo-right : Echo ordinal-collapse Omega0
ordinal-echo-right = echo-intro ordinal-collapse ordinal-right

ordinal-echo-left≢ordinal-echo-right : ordinal-echo-left ≢ ordinal-echo-right
ordinal-echo-left≢ordinal-echo-right p = ordinal-left≢ordinal-right (cong proj₁ p)
