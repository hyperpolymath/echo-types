{-# OPTIONS --safe --without-K #-}

-- WF-1 skeleton: prove accessibility by term constructor, with
-- predecessor/inversion lemmas separated from the top-level theorem.

module Ordinal.Buchholz.WellFounded where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; _<_)
open import Data.Nat.Induction as NatInd using (<-wellFounded)
open import Relation.Nullary using (¬_)
open import Induction.WellFounded using (Acc; acc; WellFounded; wf⇒asym)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; fin
  ; ω
  ; _<Ω_
  ; fin<fin
  ; fin<ω
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

  <ᵇ-pred-bOmega-fromΩ : ∀ {μ x} → Acc _<Ω_ μ → x <ᵇ bOmega μ → Acc _<ᵇ_ x
  <ᵇ-pred-bOmega-fromΩ _              <ᵇ-0-Ω         = <ᵇ-acc-bzero
  <ᵇ-pred-bOmega-fromΩ (acc rsμ)      (<ᵇ-ΩΩ κ<μ)    = <ᵇ-acc-bOmega-fromΩ (rsμ κ<μ)

  <ᵇ-acc-bOmega-fromΩ : ∀ {μ} → Acc _<Ω_ μ → Acc _<ᵇ_ (bOmega μ)
  <ᵇ-acc-bOmega-fromΩ aμ = acc (<ᵇ-pred-bOmega-fromΩ aμ)

mutual

  <ᵇ-pred-bplus-from : ∀ {α β x} → Acc _<ᵇ_ α → x <ᵇ bplus α β → Acc _<ᵇ_ x
  <ᵇ-pred-bplus-from _               <ᵇ-0-+                    = <ᵇ-acc-bzero
  <ᵇ-pred-bplus-from (acc rsα)       (<ᵇ-+1 {x₂ = x₂} x₁<α)    = <ᵇ-acc-bplus-from (rsα x₁<α) x₂

  <ᵇ-acc-bplus-from : ∀ {α} → Acc _<ᵇ_ α → (β : BT) → Acc _<ᵇ_ (bplus α β)
  <ᵇ-acc-bplus-from aα β = acc (<ᵇ-pred-bplus-from aα)

mutual

  <ᵇ-pred-bpsi-fromΩ : ∀ {μ α x} → Acc _<Ω_ μ → x <ᵇ bpsi μ α → Acc _<ᵇ_ x
  <ᵇ-pred-bpsi-fromΩ _              <ᵇ-0-ψ                 = <ᵇ-acc-bzero
  <ᵇ-pred-bpsi-fromΩ (acc rsμ)      (<ᵇ-Ωψ κ<μ)            = <ᵇ-acc-bOmega-fromΩ (rsμ κ<μ)
  <ᵇ-pred-bpsi-fromΩ (acc rsμ)      (<ᵇ-ψΩ {α = β} κ<μ)    = <ᵇ-acc-bpsi-fromΩ (rsμ κ<μ) β

  <ᵇ-acc-bpsi-fromΩ : ∀ {μ} → Acc _<Ω_ μ → (α : BT) → Acc _<ᵇ_ (bpsi μ α)
  <ᵇ-acc-bpsi-fromΩ aμ α = acc (<ᵇ-pred-bpsi-fromΩ aμ)

mutual

  <ᵇ-acc-bOmega : (μ : OmegaIndex) → Acc _<ᵇ_ (bOmega μ)
  <ᵇ-acc-bOmega μ = <ᵇ-acc-bOmega-fromΩ (<Ω-wf μ)

  <ᵇ-acc-bplus : (α β : BT) → Acc _<ᵇ_ (bplus α β)
  <ᵇ-acc-bplus α β = <ᵇ-acc-bplus-from (wf-<ᵇ α) β

  <ᵇ-acc-bpsi : (μ : OmegaIndex) (α : BT) → Acc _<ᵇ_ (bpsi μ α)
  <ᵇ-acc-bpsi μ α = <ᵇ-acc-bpsi-fromΩ (<Ω-wf μ) α

  wf-<ᵇ : WellFounded _<ᵇ_
  wf-<ᵇ bzero       = <ᵇ-acc-bzero
  wf-<ᵇ (bOmega μ)  = <ᵇ-acc-bOmega μ
  wf-<ᵇ (bplus α β) = <ᵇ-acc-bplus α β
  wf-<ᵇ (bpsi μ α)  = <ᵇ-acc-bpsi μ α

<ᵇ-irreflexive : ∀ {x} → ¬ (x <ᵇ x)
<ᵇ-irreflexive {x} x<x = wf⇒asym wf-<ᵇ x<x x<x
