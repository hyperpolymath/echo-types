{-# OPTIONS --safe --without-K #-}

-- Lexicographic target that keeps the current Buchholz order on the
-- first coordinate, but relaxes the equality side-condition along
-- recursive ψ-rooted comparison spines and uses a tagged payload
-- order for the deferred shared-binder shapes.

module Ordinal.Buchholz.VeblenComparisonTarget where

open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded')
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded; module Subrelation)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Construct.On as On using (wellFounded)
open import Relation.Binary.Definitions using (_Respectsʳ_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

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
  ; <ᵇ-inv-+Ω
  ; <ᵇ-inv-+ψ
  )
open import Ordinal.Buchholz.WellFounded using (wf-<ᵇ)

ComparisonMeasure : Set
data Payload : Set where
  payload-neutral : Payload
  payload-psi     : BT → Payload
  payload-plus    : BT → BT → Payload

ComparisonMeasure = BT × Payload

infix 4 _≈ᶜ_ _≺C_
infix 4 _≺P_

data _≈ᶜ_ : BT → BT → Set where
  ≈ᶜ-zero : bzero ≈ᶜ bzero
  ≈ᶜ-Ω    : ∀ {μ : OmegaIndex} → bOmega μ ≈ᶜ bOmega μ
  ≈ᶜ-+    : ∀ {x y z} → bplus x y ≈ᶜ bplus x z
  ≈ᶜ-ψ    : ∀ {ν α β} → bpsi ν α ≈ᶜ bpsi ν β
  ≈ᶜ-ψ+   : ∀ {ν α x y} → bpsi ν α ≈ᶜ x → bpsi ν α ≈ᶜ bplus x y

data _≺P_ : Payload → Payload → Set where
  pPsiPsi   : ∀ {α β} → α <ᵇ β → payload-psi α ≺P payload-psi β
  pPsiPlus  : ∀ {α β y} → α <ᵇ β → payload-psi α ≺P payload-plus β y
  pPlusPlus : ∀ {a y z} → y <ᵇ z → payload-plus a y ≺P payload-plus a z

≈ᶜ-trans : ∀ {x y z} → x ≈ᶜ y → y ≈ᶜ z → x ≈ᶜ z
≈ᶜ-trans ≈ᶜ-zero ≈ᶜ-zero = ≈ᶜ-zero
≈ᶜ-trans ≈ᶜ-Ω    ≈ᶜ-Ω    = ≈ᶜ-Ω
≈ᶜ-trans ≈ᶜ-+    ≈ᶜ-+    = ≈ᶜ-+
≈ᶜ-trans ≈ᶜ-ψ    ≈ᶜ-ψ    = ≈ᶜ-ψ
≈ᶜ-trans ≈ᶜ-ψ    (≈ᶜ-ψ+ x≈y) = ≈ᶜ-ψ+ (≈ᶜ-trans ≈ᶜ-ψ x≈y)
≈ᶜ-trans (≈ᶜ-ψ+ x≈y) ≈ᶜ-+ = ≈ᶜ-ψ+ x≈y

<ᵇ-respʳ-≡ : _<ᵇ_ Respectsʳ _≡_
<ᵇ-respʳ-≡ refl x<y = x<y

payload-rank : Payload → BT × BT
payload-rank payload-neutral    = bzero , bzero
payload-rank (payload-psi α)    = α , bzero
payload-rank (payload-plus a y) = a , y

_≺PL_ : Rel (BT × BT) _
_≺PL_ = ×-Lex _≡_ _<ᵇ_ _<ᵇ_

payload-embed : _≺P_ ⇒ (_≺PL_ on payload-rank)
payload-embed (pPsiPsi α<β)   = inj₁ α<β
payload-embed (pPsiPlus α<β)  = inj₁ α<β
payload-embed (pPlusPlus y<z) = inj₂ (refl , y<z)

≺PL-wf : WellFounded _≺PL_
≺PL-wf = ×-wellFounded' (λ where refl refl → refl) <ᵇ-respʳ-≡ wf-<ᵇ wf-<ᵇ

≺P-wf : WellFounded _≺P_
≺P-wf =
  let module SR = Subrelation payload-embed
  in SR.wellFounded (wellFounded payload-rank ≺PL-wf)

<ᵇ-lift-plus : ∀ {x y z} → x <ᵇ y → x <ᵇ bplus y z
<ᵇ-lift-plus {x} {y} {z} = lift x y z
  where
  lift : ∀ x y z → x <ᵇ y → x <ᵇ bplus y z
  lift bzero        y              z _            = <ᵇ-0-+
  lift (bOmega μ)   y              z x<y          = <ᵇ-Ω+ x<y
  lift (bpsi ν α)   y              z x<y          = <ᵇ-ψ+ x<y
  lift (bplus x₁ x₂) (bOmega μ)    z x<Ω          = <ᵇ-+1 (<ᵇ-inv-+Ω x<Ω)
  lift (bplus x₁ x₂) (bpsi ν α)    z x<ψ          = <ᵇ-+1 (<ᵇ-inv-+ψ x<ψ)
  lift (bplus x₁ x₂) (bplus y₁ y₂) z (<ᵇ-+1 x<y)  =
    <ᵇ-+1 (lift x₁ y₁ y₂ x<y)

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
<ᵇ-respʳ-≈ᶜ (≈ᶜ-ψ+ ψ≈x) x<ψ       = <ᵇ-lift-plus (<ᵇ-respʳ-≈ᶜ ψ≈x x<ψ)

_≺C_ : Rel ComparisonMeasure _
_≺C_ = ×-Lex _≈ᶜ_ _<ᵇ_ _≺P_

by-first : ∀ {x y α β} → x <ᵇ y → (x , α) ≺C (y , β)
by-first = inj₁

by-second : ∀ {x y α β} → x ≈ᶜ y → α ≺P β → (x , α) ≺C (y , β)
by-second x≈y α<β = inj₂ (x≈y , α<β)

by-payload-ψψ : ∀ {α β} → α <ᵇ β → payload-psi α ≺P payload-psi β
by-payload-ψψ = pPsiPsi

by-payload-ψ+ : ∀ {α β y} → α <ᵇ β → payload-psi α ≺P payload-plus β y
by-payload-ψ+ = pPsiPlus

by-payload-++ : ∀ {a y z} → y <ᵇ z → payload-plus a y ≺P payload-plus a z
by-payload-++ = pPlusPlus

≺C-wf : WellFounded _≺C_
≺C-wf = ×-wellFounded' ≈ᶜ-trans <ᵇ-respʳ-≈ᶜ wf-<ᵇ ≺P-wf
