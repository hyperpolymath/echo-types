{-# OPTIONS --safe --without-K #-}

-- Lexicographic target that keeps the current Buchholz order on the
-- first coordinate, but relaxes the equality side-condition to
-- "same comparison binder" for the deferred shared-binder shapes.

module Ordinal.Buchholz.VeblenComparisonTarget where

open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded')
open import Data.Sum.Base using (inj₁; inj₂)
open import Induction.WellFounded using (WellFounded)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (_Respectsʳ_)

open import Ordinal.OmegaMarkers using (OmegaIndex)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<ᵇ_
  ; <ᵇ-0-+
  ; <ᵇ-0-ψ
  ; <ᵇ-Ω+
  ; <ᵇ-Ωψ
  ; <ᵇ-ψ+
  ; <ᵇ-ψΩ
  ; <ᵇ-+1
  ; <ᵇ-+ψ
  )
open import Ordinal.Buchholz.WellFounded using (wf-<ᵇ)

ComparisonMeasure : Set
ComparisonMeasure = BT × BT

infix 4 _≈ᶜ_ _≺C_

data _≈ᶜ_ : BT → BT → Set where
  ≈ᶜ-zero : bzero ≈ᶜ bzero
  ≈ᶜ-Ω    : ∀ {μ : OmegaIndex} → bOmega μ ≈ᶜ bOmega μ
  ≈ᶜ-+    : ∀ {x y z} → bplus x y ≈ᶜ bplus x z
  ≈ᶜ-ψ    : ∀ {ν α β} → bpsi ν α ≈ᶜ bpsi ν β

≈ᶜ-trans : ∀ {x y z} → x ≈ᶜ y → y ≈ᶜ z → x ≈ᶜ z
≈ᶜ-trans ≈ᶜ-zero ≈ᶜ-zero = ≈ᶜ-zero
≈ᶜ-trans ≈ᶜ-Ω    ≈ᶜ-Ω    = ≈ᶜ-Ω
≈ᶜ-trans ≈ᶜ-+    ≈ᶜ-+    = ≈ᶜ-+
≈ᶜ-trans ≈ᶜ-ψ    ≈ᶜ-ψ    = ≈ᶜ-ψ

<ᵇ-respʳ-≈ᶜ : _<ᵇ_ Respectsʳ _≈ᶜ_
<ᵇ-respʳ-≈ᶜ ≈ᶜ-zero ()
<ᵇ-respʳ-≈ᶜ ≈ᶜ-Ω    x<Ω            = x<Ω
<ᵇ-respʳ-≈ᶜ ≈ᶜ-+    <ᵇ-0-+         = <ᵇ-0-+
<ᵇ-respʳ-≈ᶜ ≈ᶜ-+    (<ᵇ-Ω+ Ω<x)    = <ᵇ-Ω+ Ω<x
<ᵇ-respʳ-≈ᶜ ≈ᶜ-+    (<ᵇ-ψ+ ψ<x)    = <ᵇ-ψ+ ψ<x
<ᵇ-respʳ-≈ᶜ ≈ᶜ-+    (<ᵇ-+1 x<y)    = <ᵇ-+1 x<y
<ᵇ-respʳ-≈ᶜ ≈ᶜ-ψ    <ᵇ-0-ψ         = <ᵇ-0-ψ
<ᵇ-respʳ-≈ᶜ ≈ᶜ-ψ    (<ᵇ-Ωψ μ<ν)    = <ᵇ-Ωψ μ<ν
<ᵇ-respʳ-≈ᶜ ≈ᶜ-ψ    (<ᵇ-ψΩ μ<ν)    = <ᵇ-ψΩ μ<ν
<ᵇ-respʳ-≈ᶜ ≈ᶜ-ψ    (<ᵇ-+ψ x<ψ)    = <ᵇ-+ψ (<ᵇ-respʳ-≈ᶜ ≈ᶜ-ψ x<ψ)

_≺C_ : Rel ComparisonMeasure _
_≺C_ = ×-Lex _≈ᶜ_ _<ᵇ_ _<ᵇ_

by-first : ∀ {x y α β} → x <ᵇ y → (x , α) ≺C (y , β)
by-first = inj₁

by-second : ∀ {x y α β} → x ≈ᶜ y → α <ᵇ β → (x , α) ≺C (y , β)
by-second x≈y α<β = inj₂ (x≈y , α<β)

≺C-wf : WellFounded _≺C_
≺C-wf = ×-wellFounded' ≈ᶜ-trans <ᵇ-respʳ-≈ᶜ wf-<ᵇ wf-<ᵇ
