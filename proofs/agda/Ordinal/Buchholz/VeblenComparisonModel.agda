{-# OPTIONS --safe --without-K #-}

-- Comparison-model follow-up for the Veblen route.
--
-- This packages the new lexicographic comparison target into a
-- near-concrete interface instantiation. The two original deferred
-- same-binder obligations are discharged internally; the remaining
-- assumption is the lifted same-index ψ-to-plus case.

module Ordinal.Buchholz.VeblenComparisonModel where

open import Induction.WellFounded using (WellFounded)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)

open import Ordinal.OmegaMarkers using (_<Ω_; _≤Ω_)
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
open import Ordinal.Buchholz.VeblenInterface using (VeblenWFInterface)
open import Ordinal.Buchholz.VeblenComparisonTarget using
  ( ComparisonMeasure
  ; _≈ᶜ_
  ; ≈ᶜ-+
  ; ≈ᶜ-ψ
  ; ≈ᶜ-Ω
  ; _≺C_
  ; by-first
  ; by-second
  ; ≺C-wf
  )

cmp-payload : BT → BT
cmp-payload bzero       = bzero
cmp-payload (bOmega _)  = bzero
cmp-payload (bplus _ y) = y
cmp-payload (bpsi _ α)  = α

cmp-measure : BT → ComparisonMeasure
cmp-measure t = t , cmp-payload t

cmp-dec-Ω+ :
  ∀ {μ x y} →
  cmp-measure (bOmega μ) ≺C cmp-measure x →
  cmp-measure (bOmega μ) ≺C cmp-measure (bplus x y)
cmp-dec-Ω+ (inj₁ Ω<x)            = by-first (<ᵇ-Ω+ Ω<x)
cmp-dec-Ω+ (inj₂ (≈ᶜ-Ω , ()))

cmp-dec-ψ+ :
  (dec-ψ+-same-index :
    ∀ {ν α β y} →
    α <ᵇ β →
    cmp-measure (bpsi ν α) ≺C cmp-measure (bplus (bpsi ν β) y)) →
  ∀ {ν α x y} →
  cmp-measure (bpsi ν α) ≺C cmp-measure x →
  cmp-measure (bpsi ν α) ≺C cmp-measure (bplus x y)
cmp-dec-ψ+ dec-ψ+-same-index (inj₁ ψ<x)          = by-first (<ᵇ-ψ+ ψ<x)
cmp-dec-ψ+ dec-ψ+-same-index (inj₂ (≈ᶜ-ψ , α<β)) = dec-ψ+-same-index α<β

comparison-interface :
  (dec-ψ+-same-index :
    ∀ {ν α β y} →
    α <ᵇ β →
    cmp-measure (bpsi ν α) ≺C cmp-measure (bplus (bpsi ν β) y)) →
  VeblenWFInterface ComparisonMeasure _≺C_
comparison-interface dec-ψ+-same-index = record
  { measure = cmp-measure
  ; ≺-wf = ≺C-wf
  ; dec-0-Ω = by-first <ᵇ-0-Ω
  ; dec-0-+ = by-first <ᵇ-0-+
  ; dec-0-ψ = by-first <ᵇ-0-ψ
  ; dec-ΩΩ = λ μ<ν → by-first (<ᵇ-ΩΩ μ<ν)
  ; dec-Ωψ = λ μ<ν → by-first (<ᵇ-Ωψ μ<ν)
  ; dec-ψΩ = λ μ<ν → by-first (<ᵇ-ψΩ μ<ν)
  ; dec-ψΩ≤ = λ ν≤μ → by-first (<ᵇ-ψΩ≤ ν≤μ)
  ; dec-Ω+ = cmp-dec-Ω+
  ; dec-ψ+ = cmp-dec-ψ+ dec-ψ+-same-index
  ; dec-+Ω = λ x<Ω → by-first (<ᵇ-+Ω x<Ω)
  ; dec-+ψ = λ x<ψ → by-first (<ᵇ-+ψ x<ψ)
  ; dec-+1 = λ x₁<y₁ → by-first (<ᵇ-+1 x₁<y₁)
  ; dec-ψα = λ α<β → by-second ≈ᶜ-ψ α<β
  ; dec-+2 = λ y₂<z₂ → by-second ≈ᶜ-+ y₂<z₂
  }

core-wf-from-comparison :
  (dec-ψ+-same-index :
    ∀ {ν α β y} →
    α <ᵇ β →
    cmp-measure (bpsi ν α) ≺C cmp-measure (bplus (bpsi ν β) y)) →
  WellFounded _<ᵇ_
core-wf-from-comparison dec-ψ+-same-index =
  VeblenWFInterface.core-wf (comparison-interface dec-ψ+-same-index)
