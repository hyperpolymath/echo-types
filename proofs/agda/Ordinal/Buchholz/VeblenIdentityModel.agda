{-# OPTIONS --safe --without-K #-}

-- Minimal concrete instantiation of the Veblen WF interface.
--
-- This uses the identity measure on BT as a bootstrap model to confirm
-- interface coherence. The two same-binder obligations remain explicit
-- parameters (`dec-ψα`, `dec-+2`), matching the currently deferred hard
-- cases.

module Ordinal.Buchholz.VeblenIdentityModel where

open import Induction.WellFounded using (WellFounded)

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
open import Ordinal.Buchholz.WellFounded using (wf-<ᵇ)
open import Ordinal.Buchholz.VeblenInterface using (VeblenWFInterface)

identity-interface :
  (dec-ψα : ∀ {ν α β} → α <ᵇ β → bpsi ν α <ᵇ bpsi ν β) →
  (dec-+2 : ∀ {x y₂ z₂} → y₂ <ᵇ z₂ → bplus x y₂ <ᵇ bplus x z₂) →
  VeblenWFInterface BT _<ᵇ_
identity-interface dec-ψα dec-+2 = record
  { measure = λ x → x
  ; ≺-wf = wf-<ᵇ
  ; dec-0-Ω = <ᵇ-0-Ω
  ; dec-0-+ = <ᵇ-0-+
  ; dec-0-ψ = <ᵇ-0-ψ
  ; dec-ΩΩ = <ᵇ-ΩΩ
  ; dec-Ωψ = <ᵇ-Ωψ
  ; dec-ψΩ = <ᵇ-ψΩ
  ; dec-ψΩ≤ = <ᵇ-ψΩ≤
  ; dec-Ω+ = <ᵇ-Ω+
  ; dec-ψ+ = <ᵇ-ψ+
  ; dec-+Ω = <ᵇ-+Ω
  ; dec-+ψ = <ᵇ-+ψ
  ; dec-+1 = <ᵇ-+1
  ; dec-ψα = dec-ψα
  ; dec-+2 = dec-+2
  }

core-wf-from-identity :
  (dec-ψα : ∀ {ν α β} → α <ᵇ β → bpsi ν α <ᵇ bpsi ν β) →
  (dec-+2 : ∀ {x y₂ z₂} → y₂ <ᵇ z₂ → bplus x y₂ <ᵇ bplus x z₂) →
  WellFounded _<ᵇ_
core-wf-from-identity dec-ψα dec-+2 =
  VeblenWFInterface.core-wf (identity-interface dec-ψα dec-+2)
