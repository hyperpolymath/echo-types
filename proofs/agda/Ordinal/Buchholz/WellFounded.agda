{-# OPTIONS --safe --without-K #-}

-- WF-1 skeleton: prove accessibility by term constructor, with
-- predecessor inversion lemmas separated out. The two recursive bridge
-- lemmas are intentionally left as the remaining obligations.

module Ordinal.Buchholz.WellFounded where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Induction.WellFounded using (Acc; acc; WellFounded; wf⇒asym)

open import Ordinal.OmegaMarkers using (OmegaIndex)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<Ω_
  ; _<ᵇ_
  ; <ᵇ-0Ω
  ; <ᵇ-0+
  ; <ᵇ-0ψ
  ; <ᵇ-Ω+
  ; <ᵇ-Ωψ
  ; <ᵇ-+1
  ; <ᵇ-ψν
  )

<ᵇ-inv-bzero : ∀ {x} → x <ᵇ bzero → ⊥
<ᵇ-inv-bzero ()

<ᵇ-pred-bzero : ∀ {x} → x <ᵇ bzero → Acc _<ᵇ_ x
<ᵇ-pred-bzero x<0 = ⊥-elim (<ᵇ-inv-bzero x<0)

<ᵇ-rec-+1 : ∀ {α β γ} → α <ᵇ β → Acc _<ᵇ_ (bplus α γ)
<ᵇ-rec-+1 α<β = {!!}

<ᵇ-rec-ψν : ∀ {μ ν α} → μ <Ω ν → Acc _<ᵇ_ (bpsi μ α)
<ᵇ-rec-ψν μ<ν = {!!}

<ᵇ-acc-bzero : Acc _<ᵇ_ bzero
<ᵇ-acc-bzero = acc <ᵇ-pred-bzero

<ᵇ-pred-bOmega : ∀ {μ x} → x <ᵇ bOmega μ → Acc _<ᵇ_ x
<ᵇ-pred-bOmega <ᵇ-0Ω = <ᵇ-acc-bzero

<ᵇ-acc-bOmega : (μ : OmegaIndex) → Acc _<ᵇ_ (bOmega μ)
<ᵇ-acc-bOmega μ = acc <ᵇ-pred-bOmega

<ᵇ-pred-bplus : ∀ {α β x} → x <ᵇ bplus α β → Acc _<ᵇ_ x
<ᵇ-pred-bplus <ᵇ-0+ = <ᵇ-acc-bzero
<ᵇ-pred-bplus (<ᵇ-Ω+ {κ = κ}) = <ᵇ-acc-bOmega κ
<ᵇ-pred-bplus (<ᵇ-+1 α<β) = <ᵇ-rec-+1 α<β

<ᵇ-pred-bpsi : ∀ {μ α x} → x <ᵇ bpsi μ α → Acc _<ᵇ_ x
<ᵇ-pred-bpsi <ᵇ-0ψ = <ᵇ-acc-bzero
<ᵇ-pred-bpsi (<ᵇ-Ωψ {κ = κ}) = <ᵇ-acc-bOmega κ
<ᵇ-pred-bpsi (<ᵇ-ψν μ<ν) = <ᵇ-rec-ψν μ<ν

<ᵇ-acc-bplus : (α β : BT) → Acc _<ᵇ_ (bplus α β)
<ᵇ-acc-bplus α β = acc <ᵇ-pred-bplus

<ᵇ-acc-bpsi : (μ : OmegaIndex) (α : BT) → Acc _<ᵇ_ (bpsi μ α)
<ᵇ-acc-bpsi μ α = acc <ᵇ-pred-bpsi

wf-<ᵇ : WellFounded _<ᵇ_
wf-<ᵇ bzero       = <ᵇ-acc-bzero
wf-<ᵇ (bOmega μ)  = <ᵇ-acc-bOmega μ
wf-<ᵇ (bplus α β) = <ᵇ-acc-bplus α β
wf-<ᵇ (bpsi μ α)  = <ᵇ-acc-bpsi μ α

<ᵇ-irreflexive : ∀ {x} → ¬ (x <ᵇ x)
<ᵇ-irreflexive {x} x<x = wf⇒asym wf-<ᵇ x<x x<x
