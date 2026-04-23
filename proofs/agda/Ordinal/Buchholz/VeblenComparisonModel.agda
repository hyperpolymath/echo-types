{-# OPTIONS --safe --without-K #-}

-- Comparison-model follow-up for the Veblen route.
--
-- This packages the new lexicographic comparison target into a
-- concrete interface instantiation. The original deferred same-binder
-- obligations and the lifted same-index ψ-to-plus case are all
-- discharged internally.

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
  ; Payload
  ; payload-neutral
  ; payload-psi
  ; payload-plus
  ; _≈ᶜ_
  ; ≈ᶜ-+
  ; ≈ᶜ-ψ
  ; ≈ᶜ-ψ+
  ; _≺C_
  ; _≺P_
  ; pPsiPsi
  ; pPsiPlus
  ; by-first
  ; by-second
  ; by-payload-ψψ
  ; by-payload-ψ+
  ; by-payload-++
  ; ≺C-wf
  )

cmp-anchor : BT → BT
cmp-anchor bzero        = bzero
cmp-anchor (bOmega μ)   = bOmega μ
cmp-anchor (bpsi _ α)   = α
cmp-anchor (bplus x _)  = cmp-anchor x

cmp-payload : BT → Payload
cmp-payload bzero       = payload-neutral
cmp-payload (bOmega _)  = payload-neutral
cmp-payload (bplus x y) = payload-plus (cmp-anchor x) y
cmp-payload (bpsi _ α)  = payload-psi α

cmp-measure : BT → ComparisonMeasure
cmp-measure t = t , cmp-payload t

cmp-dec-Ω+ :
  ∀ {μ x y} →
  cmp-measure (bOmega μ) ≺C cmp-measure x →
  cmp-measure (bOmega μ) ≺C cmp-measure (bplus x y)
cmp-dec-Ω+ (inj₁ Ω<x) = by-first (<ᵇ-Ω+ Ω<x)
cmp-dec-Ω+ {x = bzero}      (inj₂ ())
cmp-dec-Ω+ {x = bOmega _}   (inj₂ (_ , ()))
cmp-dec-Ω+ {x = bplus _ _}  (inj₂ ())
cmp-dec-Ω+ {x = bpsi _ _}   (inj₂ ())

cmp-payload-step :
  ∀ {ν α x y} →
  bpsi ν α ≈ᶜ x →
  cmp-payload (bpsi ν α) ≺P cmp-payload x →
  cmp-payload (bpsi ν α) ≺P cmp-payload (bplus x y)
cmp-payload-step ≈ᶜ-ψ          (pPsiPsi α<β)  = by-payload-ψ+ α<β
cmp-payload-step (≈ᶜ-ψ+ _)     (pPsiPlus α<β) = by-payload-ψ+ α<β

cmp-dec-ψ+-same-index :
  ∀ {ν α β y} →
  α <ᵇ β →
  cmp-measure (bpsi ν α) ≺C cmp-measure (bplus (bpsi ν β) y)
cmp-dec-ψ+-same-index α<β =
  by-second (≈ᶜ-ψ+ ≈ᶜ-ψ) (by-payload-ψ+ α<β)

cmp-dec-ψ+ :
  ∀ {ν α x y} →
  cmp-measure (bpsi ν α) ≺C cmp-measure x →
  cmp-measure (bpsi ν α) ≺C cmp-measure (bplus x y)
cmp-dec-ψ+ (inj₁ ψ<x)             = by-first (<ᵇ-ψ+ ψ<x)
cmp-dec-ψ+ (inj₂ (ψ≈x , ψ<x)) = by-second (≈ᶜ-ψ+ ψ≈x) (cmp-payload-step ψ≈x ψ<x)

comparison-interface :
  VeblenWFInterface ComparisonMeasure _≺C_
comparison-interface = record
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
  ; dec-ψ+ = cmp-dec-ψ+
  ; dec-+Ω = λ x<Ω → by-first (<ᵇ-+Ω x<Ω)
  ; dec-+ψ = λ x<ψ → by-first (<ᵇ-+ψ x<ψ)
  ; dec-+1 = λ x₁<y₁ → by-first (<ᵇ-+1 x₁<y₁)
  ; dec-ψα = λ α<β → by-second ≈ᶜ-ψ (by-payload-ψψ α<β)
  ; dec-+2 = λ y₂<z₂ → by-second ≈ᶜ-+ (by-payload-++ y₂<z₂)
  }

core-wf-from-comparison : WellFounded _<ᵇ_
core-wf-from-comparison =
  VeblenWFInterface.core-wf comparison-interface
