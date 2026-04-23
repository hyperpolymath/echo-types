{-# OPTIONS --safe --without-K #-}

-- One-level lift of the closed comparison wrapper.
--
-- `_<ᵇ⁺_` is too weak to be stable under the recursive same-binder
-- lifts needed for a self-contained surface recursion. This module
-- records the next honest step: lift those same-binder moves from the
-- current wrapper into a new well-founded wrapper one level up.

module Ordinal.Buchholz.LiftedExtendedOrder where

open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded; ×-wellFounded')
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded; wf⇒asym; module Subrelation)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Construct.On as On using (wellFounded)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Ordinal.Buchholz.Syntax using (BT; bzero; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_; <ᵇ-trans)
open import Ordinal.Buchholz.WellFounded using (wf-<ᵇ)
open import Ordinal.Buchholz.ExtendedOrder using
  ( _<ᵇ⁺_
  ; <ᵇ⇒<ᵇ⁺
  ; <ᵇ⁺-+2
  ; <ᵇ⁺-trans
  ; wf-<ᵇ⁺
  )
open import Ordinal.Buchholz.VeblenComparisonTarget using
  ( Payload
  ; payload-neutral
  ; payload-psi
  ; payload-plus
  ; _≈ᶜ_
  ; _≺P_
  ; pPsiPsi
  ; pPsiPlus
  ; pPlusPlus
  ; ≈ᶜ-+
  ; ≈ᶜ-ψ
  ; ≈ᶜ-trans
  ; <ᵇ-respʳ-≈ᶜ
  ; <ᵇ-chain-≈ᶜ
  )
open import Ordinal.Buchholz.VeblenComparisonModel using (cmp-measure)

infix 4 _≺P⁺¹_ _≺C⁺¹_ _<ᵇ⁺¹_

data _≺P⁺¹_ : Payload → Payload → Set where
  pPsiPsi⁺¹   : ∀ {α β} → α <ᵇ⁺ β → payload-psi α ≺P⁺¹ payload-psi β
  pPsiPlus⁺¹  : ∀ {α β y} → α <ᵇ⁺ β → payload-psi α ≺P⁺¹ payload-plus β y
  pPlusPlus⁺¹ : ∀ {a y z} → y <ᵇ⁺ z → payload-plus a y ≺P⁺¹ payload-plus a z

payload-rank : Payload → BT × BT
payload-rank payload-neutral    = bzero , bzero
payload-rank (payload-psi α)    = α , bzero
payload-rank (payload-plus a y) = a , y

_≺PL⁺¹_ : Rel (BT × BT) _
_≺PL⁺¹_ = ×-Lex _≡_ _<ᵇ⁺_ _<ᵇ⁺_

payload-embed⁺¹ : _≺P⁺¹_ ⇒ (_≺PL⁺¹_ on payload-rank)
payload-embed⁺¹ (pPsiPsi⁺¹ α<β)   = inj₁ α<β
payload-embed⁺¹ (pPsiPlus⁺¹ α<β)  = inj₁ α<β
payload-embed⁺¹ (pPlusPlus⁺¹ y<z) = inj₂ (refl , y<z)

≺PL⁺¹-wf : WellFounded _≺PL⁺¹_
≺PL⁺¹-wf = ×-wellFounded wf-<ᵇ⁺ wf-<ᵇ⁺

≺P⁺¹-wf : WellFounded _≺P⁺¹_
≺P⁺¹-wf =
  let module SR = Subrelation payload-embed⁺¹
  in SR.wellFounded (wellFounded payload-rank ≺PL⁺¹-wf)

≺P⁺¹-trans : Transitive _≺P⁺¹_
≺P⁺¹-trans (pPsiPsi⁺¹ α<β)   (pPsiPsi⁺¹ β<γ)   = pPsiPsi⁺¹ (<ᵇ⁺-trans α<β β<γ)
≺P⁺¹-trans (pPsiPsi⁺¹ α<β)   (pPsiPlus⁺¹ β<γ)  = pPsiPlus⁺¹ (<ᵇ⁺-trans α<β β<γ)
≺P⁺¹-trans (pPsiPlus⁺¹ α<β)  (pPlusPlus⁺¹ _)   = pPsiPlus⁺¹ α<β
≺P⁺¹-trans (pPlusPlus⁺¹ y<z) (pPlusPlus⁺¹ z<w) = pPlusPlus⁺¹ (<ᵇ⁺-trans y<z z<w)

_≺C⁺¹_ : Rel (BT × Payload) _
_≺C⁺¹_ = ×-Lex _≈ᶜ_ _<ᵇ_ _≺P⁺¹_

≺C⁺¹-trans : Transitive _≺C⁺¹_
≺C⁺¹-trans (inj₁ x<y)           (inj₁ y<z)            = inj₁ (<ᵇ-trans x<y y<z)
≺C⁺¹-trans (inj₁ x<y)           (inj₂ (y≈z , _))      = inj₁ (<ᵇ-respʳ-≈ᶜ y≈z x<y)
≺C⁺¹-trans (inj₂ (x≈y , _))     (inj₁ y<z)            = inj₁ (<ᵇ-chain-≈ᶜ x≈y y<z)
≺C⁺¹-trans (inj₂ (x≈y , px<qy)) (inj₂ (y≈z , qy<rz)) =
  inj₂ (≈ᶜ-trans x≈y y≈z , ≺P⁺¹-trans px<qy qy<rz)

≺C⁺¹-wf : WellFounded _≺C⁺¹_
≺C⁺¹-wf = ×-wellFounded' ≈ᶜ-trans <ᵇ-respʳ-≈ᶜ wf-<ᵇ ≺P⁺¹-wf

_<ᵇ⁺¹_ : Rel BT _
_<ᵇ⁺¹_ = _≺C⁺¹_ on cmp-measure

payload-lift⁺¹ : _≺P_ ⇒ _≺P⁺¹_
payload-lift⁺¹ (pPsiPsi α<β)   = pPsiPsi⁺¹ (<ᵇ⇒<ᵇ⁺ α<β)
payload-lift⁺¹ (pPsiPlus α<β)  = pPsiPlus⁺¹ (<ᵇ⇒<ᵇ⁺ α<β)
payload-lift⁺¹ (pPlusPlus y<z) = pPlusPlus⁺¹ (<ᵇ⇒<ᵇ⁺ y<z)

<ᵇ⁺⇒<ᵇ⁺¹ : _<ᵇ⁺_ ⇒ _<ᵇ⁺¹_
<ᵇ⁺⇒<ᵇ⁺¹ (inj₁ x<y)       = inj₁ x<y
<ᵇ⁺⇒<ᵇ⁺¹ (inj₂ (x≈y , p)) = inj₂ (x≈y , payload-lift⁺¹ p)

<ᵇ⁺¹-ψα : ∀ {ν α β} → α <ᵇ⁺ β → bpsi ν α <ᵇ⁺¹ bpsi ν β
<ᵇ⁺¹-ψα α<β = inj₂ (≈ᶜ-ψ , pPsiPsi⁺¹ α<β)

<ᵇ⁺¹-+2 : ∀ {x y z} → y <ᵇ⁺ z → bplus x y <ᵇ⁺¹ bplus x z
<ᵇ⁺¹-+2 y<z = inj₂ (≈ᶜ-+ , pPlusPlus⁺¹ y<z)

<ᵇ⁺¹-ψ+2 : ∀ {ν x y z} → y <ᵇ z → bpsi ν (bplus x y) <ᵇ⁺¹ bpsi ν (bplus x z)
<ᵇ⁺¹-ψ+2 y<z = <ᵇ⁺¹-ψα (<ᵇ⁺-+2 y<z)

wf-<ᵇ⁺¹ : WellFounded _<ᵇ⁺¹_
wf-<ᵇ⁺¹ = On.wellFounded cmp-measure ≺C⁺¹-wf

<ᵇ⁺¹-irreflexive : ∀ {x} → ¬ (x <ᵇ⁺¹ x)
<ᵇ⁺¹-irreflexive {x} x<x = wf⇒asym wf-<ᵇ⁺¹ x<x x<x
