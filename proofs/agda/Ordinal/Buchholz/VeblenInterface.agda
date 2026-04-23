{-# OPTIONS --safe --without-K #-}

-- Veblen-route interface for Buchholz WF follow-up work.
--
-- This module is intentionally small: it does not implement a concrete
-- measure. Instead it states, in one place, the obligations required
-- to prove `WellFounded _<ᵇ_` via a measure into a well-founded target.
--
-- The final two fields (`dec-ψα`, `dec-+2`) are the historical
-- same-binder obligations corresponding to the blocked shared-binder
-- shapes. The closed comparison route now discharges them internally;
-- they remain here because this record packages the generic interface.

module Ordinal.Buchholz.VeblenInterface where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Function.Base using (_on_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Induction.WellFounded as WF using (WellFounded; module Subrelation)
open import Relation.Binary.Construct.On as On using (wellFounded)

open import Ordinal.OmegaMarkers using (OmegaIndex; _<Ω_; _≤Ω_; ω)
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
  ; <ᵇ-Ω+
  ; <ᵇ-ψ+
  ; <ᵇ-+Ω
  ; <ᵇ-+ψ
  ; <ᵇ-+1
  )

record VeblenWFInterface {ℓm ℓr : Level}
                         (M : Set ℓm)
                         (_≺_ : Rel M ℓr)
                         : Set (lsuc (ℓm ⊔ ℓr)) where
  field
    measure : BT → M
    ≺-wf    : WellFounded _≺_

    -- Constructor-by-constructor decrease obligations for the current core.
    dec-0-Ω  : ∀ {μ} → measure bzero ≺ measure (bOmega μ)
    dec-0-+  : ∀ {x y} → measure bzero ≺ measure (bplus x y)
    dec-0-ψ  : ∀ {ν α} → measure bzero ≺ measure (bpsi ν α)

    dec-ΩΩ   : ∀ {μ ν} → μ <Ω ν → measure (bOmega μ) ≺ measure (bOmega ν)
    dec-Ωψ   : ∀ {μ ν α} → μ <Ω ν → measure (bOmega μ) ≺ measure (bpsi ν α)
    dec-ψΩ   : ∀ {μ ν α β} → μ <Ω ν → measure (bpsi μ α) ≺ measure (bpsi ν β)
    dec-ψΩ≤  : ∀ {ν μ α} → ν ≤Ω μ → measure (bpsi ν α) ≺ measure (bOmega μ)
    dec-Ω+   : ∀ {μ x y} → measure (bOmega μ) ≺ measure x →
               measure (bOmega μ) ≺ measure (bplus x y)
    dec-ψ+   : ∀ {ν α x y} → measure (bpsi ν α) ≺ measure x →
               measure (bpsi ν α) ≺ measure (bplus x y)

    dec-+Ω   : ∀ {x y μ} → x <ᵇ bOmega μ → measure (bplus x y) ≺ measure (bOmega μ)
    dec-+ψ   : ∀ {x y ν α} → x <ᵇ bpsi ν α → measure (bplus x y) ≺ measure (bpsi ν α)
    dec-+1   : ∀ {x₁ x₂ y₁ y₂} → x₁ <ᵇ y₁ → measure (bplus x₁ x₂) ≺ measure (bplus y₁ y₂)

    -- Deferred same-binder obligations for the extended comparison layer.
    dec-ψα   : ∀ {ν α β} → α <ᵇ β → measure (bpsi ν α) ≺ measure (bpsi ν β)
    dec-+2   : ∀ {x y₂ z₂} → y₂ <ᵇ z₂ → measure (bplus x y₂) ≺ measure (bplus x z₂)

  core-monotone : _<ᵇ_ ⇒ (_≺_ on measure)
  core-monotone <ᵇ-0-Ω = dec-0-Ω
  core-monotone <ᵇ-0-+ = dec-0-+
  core-monotone <ᵇ-0-ψ = dec-0-ψ
  core-monotone (<ᵇ-ΩΩ μ<ν) = dec-ΩΩ μ<ν
  core-monotone (<ᵇ-Ωψ μ<ν) = dec-Ωψ μ<ν
  core-monotone (<ᵇ-ψΩ μ<ν) = dec-ψΩ μ<ν
  core-monotone (<ᵇ-ψΩ≤ ν≤μ) = dec-ψΩ≤ ν≤μ
  core-monotone (<ᵇ-Ω+ Ω<x) = dec-Ω+ (core-monotone Ω<x)
  core-monotone (<ᵇ-ψ+ ψ<x) = dec-ψ+ (core-monotone ψ<x)
  core-monotone (<ᵇ-+Ω x<Ω) = dec-+Ω x<Ω
  core-monotone (<ᵇ-+ψ x<ψ) = dec-+ψ x<ψ
  core-monotone (<ᵇ-+1 x₁<y₁) = dec-+1 x₁<y₁

  -- Generic derivation route: well-founded target + constructor monotonicity
  -- gives well-foundedness of the current `_ <ᵇ _` core via subrelation.
  core-wf : WellFounded _<ᵇ_
  core-wf =
    let module SR = Subrelation core-monotone
    in SR.wellFounded (wellFounded measure ≺-wf)
