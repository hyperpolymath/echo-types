{-# OPTIONS --safe --without-K #-}

-- WF-1 skeleton: prove accessibility by term constructor, with
-- predecessor/inversion lemmas separated from the top-level theorem.

module Ordinal.Buchholz.WellFounded where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; _<_)
open import Data.Nat.Induction as NatInd using (<-wellFounded)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Induction.WellFounded using (Acc; acc; WellFounded; wf⇒asym)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; _≤Ω_
  ; fin
  ; ω
  ; _<Ω_
  ; fin<fin
  ; fin<ω
  ; ≤Ω-split
  )
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<ᵇ_
  ; <ᵇ-0-Ω
  ; <ᵇ-0-+
  ; <ᵇ-0-ψ
  ; <ᵇ-ΩΩ
  ; <ᵇ-Ωψ
  ; <ᵇ-ψΩ
  ; <ᵇ-ψΩ≤
  ; <ᵇ-+ω
  ; <ᵇ-+ψω
  ; <ᵇ-+1
  )

<ᵇ-inv-bzero : ∀ {x} → x <ᵇ bzero → ⊥
<ᵇ-inv-bzero ()

<ᵇ-pred-bzero : ∀ {x} → x <ᵇ bzero → Acc _<ᵇ_ x
<ᵇ-pred-bzero x<0 = ⊥-elim (<ᵇ-inv-bzero x<0)

<Ω-acc-fin : (n : ℕ) → Acc _<Ω_ (fin n)
<Ω-acc-fin n = fromNat (NatInd.<-wellFounded n)
  where
  fromNat : ∀ {m} → Acc _<_ m → Acc _<Ω_ (fin m)
  fromNat (acc rs) = acc λ where
    (fin<fin k<m) → fromNat (rs k<m)

<Ω-wf : WellFounded _<Ω_
<Ω-wf (fin n) = <Ω-acc-fin n
<Ω-wf ω       = acc λ where
  (fin<ω {m}) → <Ω-acc-fin m

<ᵇ-acc-bzero : Acc _<ᵇ_ bzero
<ᵇ-acc-bzero = acc <ᵇ-pred-bzero

mutual

  <ᵇ-pred-bplus-from : ∀ {α β x} → Acc _<ᵇ_ α → x <ᵇ bplus α β → Acc _<ᵇ_ x
  <ᵇ-pred-bplus-from _          <ᵇ-0-+                  = <ᵇ-acc-bzero
  <ᵇ-pred-bplus-from (acc rsα)  (<ᵇ-+1 {x₂ = x₂} x₁<α)  = <ᵇ-acc-bplus-from (rsα x₁<α) x₂

  <ᵇ-acc-bplus-from : ∀ {α} → Acc _<ᵇ_ α → (β : BT) → Acc _<ᵇ_ (bplus α β)
  <ᵇ-acc-bplus-from aα β = acc (<ᵇ-pred-bplus-from aα)

ΩBundle : OmegaIndex → Set
ΩBundle μ = Acc _<ᵇ_ (bOmega μ) × ((α : BT) → Acc _<ᵇ_ (bpsi μ α))

<ᵇ-bundle-fromΩ : ∀ {μ} → Acc _<Ω_ μ → ΩBundle μ
<ᵇ-bundle-fromΩ {μ} aμ@(acc rsμ) = omegaAcc , psiAcc
  where
  mutual

    omegaAcc : Acc _<ᵇ_ (bOmega μ)
    omegaAcc = acc predOmega

    predOmega : ∀ {x} → x <ᵇ bOmega μ → Acc _<ᵇ_ x
    predOmega <ᵇ-0-Ω = <ᵇ-acc-bzero
    predOmega (<ᵇ-ΩΩ κ<μ) = proj₁ (<ᵇ-bundle-fromΩ (rsμ κ<μ))
    predOmega (<ᵇ-ψΩ≤ {α = α} ν≤μ) with ≤Ω-split ν≤μ
    ... | inj₁ ν<μ = proj₂ (<ᵇ-bundle-fromΩ (rsμ ν<μ)) α
    ... | inj₂ refl = psiAcc α
    predOmega (<ᵇ-+ω {x = x} {y = y} x<ω) = <ᵇ-acc-bplus-from (predOmega x<ω) y

    predPsi : (α : BT) → ∀ {x} → x <ᵇ bpsi μ α → Acc _<ᵇ_ x
    predPsi α <ᵇ-0-ψ = <ᵇ-acc-bzero
    predPsi α (<ᵇ-Ωψ κ<μ) = proj₁ (<ᵇ-bundle-fromΩ (rsμ κ<μ))
    predPsi α (<ᵇ-ψΩ {α = β} κ<μ) = proj₂ (<ᵇ-bundle-fromΩ (rsμ κ<μ)) β
    predPsi α (<ᵇ-+ψω {x = x} {y = y} x<ψω) = <ᵇ-acc-bplus-from (predPsi α x<ψω) y

    psiAcc : (α : BT) → Acc _<ᵇ_ (bpsi μ α)
    psiAcc α = acc (predPsi α)

mutual

  <ᵇ-acc-bOmega : (μ : OmegaIndex) → Acc _<ᵇ_ (bOmega μ)
  <ᵇ-acc-bOmega μ = proj₁ (<ᵇ-bundle-fromΩ (<Ω-wf μ))

  <ᵇ-acc-bplus : (α β : BT) → Acc _<ᵇ_ (bplus α β)
  <ᵇ-acc-bplus α β = <ᵇ-acc-bplus-from (wf-<ᵇ α) β

  <ᵇ-acc-bpsi : (μ : OmegaIndex) (α : BT) → Acc _<ᵇ_ (bpsi μ α)
  <ᵇ-acc-bpsi μ α = proj₂ (<ᵇ-bundle-fromΩ (<Ω-wf μ)) α

  wf-<ᵇ : WellFounded _<ᵇ_
  wf-<ᵇ bzero       = <ᵇ-acc-bzero
  wf-<ᵇ (bOmega μ)  = <ᵇ-acc-bOmega μ
  wf-<ᵇ (bplus α β) = <ᵇ-acc-bplus α β
  wf-<ᵇ (bpsi μ α)  = <ᵇ-acc-bpsi μ α

<ᵇ-irreflexive : ∀ {x} → ¬ (x <ᵇ x)
<ᵇ-irreflexive {x} x<x = wf⇒asym wf-<ᵇ x<x x<x
