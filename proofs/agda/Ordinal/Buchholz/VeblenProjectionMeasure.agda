{-# OPTIONS --safe --without-K #-}

-- Projection-style concrete measure into the current Veblen target.
--
-- This module is retained as an explanatory scaffold, not the final
-- route. Its role is narrower: make the target images used by the
-- shared-binder follow-up explicit, and discharge those two deferred
-- obligations in `≺M` itself. The assumption-free closure now happens
-- in `VeblenComparisonModel`.

module Ordinal.Buchholz.VeblenProjectionMeasure where

open import Data.Product.Base using (_,_)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; Omega0
  ; _<Ω_
  )
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_)
open import Ordinal.Buchholz.VeblenMeasureTarget using
  ( Measure
  ; _≺M_
  ; by-index
  ; by-term
  )
open import Ordinal.Buchholz.VeblenObligations using (plus-right; psi-arg)

proj-index : BT → OmegaIndex
proj-index bzero       = Omega0
proj-index (bOmega μ)  = μ
proj-index (bplus x _) = proj-index x
proj-index (bpsi ν _)  = ν

proj-term : BT → BT
proj-term bzero       = bzero
proj-term (bOmega _)  = bzero
proj-term (bplus x y) = plus-right (bplus x y)
proj-term (bpsi ν α)  = psi-arg (bpsi ν α)

proj-measure : BT → Measure
proj-measure t = proj-index t , proj-term t

-- The same-binder target obligations now become direct lexicographic
-- decreases on the projected payload.
proj-dec-+2 :
  ∀ {x y₂ z₂} →
  y₂ <ᵇ z₂ →
  proj-measure (bplus x y₂) ≺M proj-measure (bplus x z₂)
proj-dec-+2 y₂<z₂ = by-term y₂<z₂

proj-dec-ψα :
  ∀ {ν α β} →
  α <ᵇ β →
  proj-measure (bpsi ν α) ≺M proj-measure (bpsi ν β)
proj-dec-ψα α<β = by-term α<β

-- The index-driven cases already fit the first lexicographic
-- component of the same target.
proj-dec-ΩΩ :
  ∀ {μ ν} →
  μ <Ω ν →
  proj-measure (bOmega μ) ≺M proj-measure (bOmega ν)
proj-dec-ΩΩ μ<ν = by-index μ<ν

proj-dec-Ωψ :
  ∀ {μ ν α} →
  μ <Ω ν →
  proj-measure (bOmega μ) ≺M proj-measure (bpsi ν α)
proj-dec-Ωψ μ<ν = by-index μ<ν

proj-dec-ψΩ :
  ∀ {μ ν α β} →
  μ <Ω ν →
  proj-measure (bpsi μ α) ≺M proj-measure (bpsi ν β)
proj-dec-ψΩ μ<ν = by-index μ<ν

proj-dec-ψΩ< :
  ∀ {ν μ α} →
  ν <Ω μ →
  proj-measure (bpsi ν α) ≺M proj-measure (bOmega μ)
proj-dec-ψΩ< ν<μ = by-index ν<μ
