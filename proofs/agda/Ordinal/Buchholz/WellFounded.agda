{-# OPTIONS --safe --without-K #-}

-- WF-1 skeleton: prove accessibility by term constructor, with
-- predecessor inversion lemmas separated out. Recursive predecessor
-- bridges are discharged through a small rank-to-ℕ subrelation proof.

module Ordinal.Buchholz.WellFounded where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; _<_; z≤n; s≤s; zero; suc)
open import Data.Nat.Induction as NatInd using (<-wellFounded)
open import Function.Base using (_on_)
open import Relation.Nullary using (¬_)
open import Induction.WellFounded as WF using (Acc; acc; WellFounded; wf⇒asym)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin; ω)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<Ω_
  ; _<ᵇ_
  ; <Ω-fin
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

rankΩ : OmegaIndex → ℕ
rankΩ (fin n) = n
rankΩ ω       = zero

rankBT : BT → ℕ
rankBT bzero       = zero
rankBT (bOmega μ)  = suc zero
rankBT (bplus α β) = suc (suc (rankBT α))
rankBT (bpsi μ α)  = suc (suc (suc (rankΩ μ)))

<Ω⇒<rankΩ : ∀ {μ ν} → μ <Ω ν → rankΩ μ < rankΩ ν
<Ω⇒<rankΩ (<Ω-fin m<n) = m<n

<ᵇ⇒<rankBT : ∀ {x y} → x <ᵇ y → rankBT x < rankBT y
<ᵇ⇒<rankBT <ᵇ-0Ω = s≤s z≤n
<ᵇ⇒<rankBT <ᵇ-0+ = s≤s z≤n
<ᵇ⇒<rankBT <ᵇ-0ψ = s≤s z≤n
<ᵇ⇒<rankBT <ᵇ-Ω+ = s≤s (s≤s z≤n)
<ᵇ⇒<rankBT <ᵇ-Ωψ = s≤s (s≤s z≤n)
<ᵇ⇒<rankBT (<ᵇ-+1 α<β) = s≤s (s≤s (<ᵇ⇒<rankBT α<β))
<ᵇ⇒<rankBT (<ᵇ-ψν μ<ν) = s≤s (s≤s (s≤s (<Ω⇒<rankΩ μ<ν)))

wf-rankBT : WellFounded (_<_ on rankBT)
wf-rankBT = WF.InverseImage.wellFounded rankBT NatInd.<-wellFounded

wf-<ᵇ-rank : WellFounded _<ᵇ_
wf-<ᵇ-rank = WF.Subrelation.wellFounded <ᵇ⇒<rankBT wf-rankBT

<ᵇ-rec-+1 : ∀ {α β γ} → α <ᵇ β → Acc _<ᵇ_ (bplus α γ)

<ᵇ-rec-ψν : ∀ {μ ν α} → μ <Ω ν → Acc _<ᵇ_ (bpsi μ α)

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

<ᵇ-rec-+1 {α = α} {γ = γ} _ = wf-<ᵇ-rank (bplus α γ)

<ᵇ-rec-ψν {μ = μ} {α = α} _ = wf-<ᵇ-rank (bpsi μ α)

wf-<ᵇ : WellFounded _<ᵇ_
wf-<ᵇ bzero       = <ᵇ-acc-bzero
wf-<ᵇ (bOmega μ)  = <ᵇ-acc-bOmega μ
wf-<ᵇ (bplus α β) = <ᵇ-acc-bplus α β
wf-<ᵇ (bpsi μ α)  = <ᵇ-acc-bpsi μ α

<ᵇ-irreflexive : ∀ {x} → ¬ (x <ᵇ x)
<ᵇ-irreflexive {x} x<x = wf⇒asym wf-<ᵇ x<x x<x
