{-# OPTIONS --safe --without-K #-}

-- Buchholz-layer manifest. Keeps load-bearing names pinned so that
-- accidental renames fail quickly in a focused module.

module Ordinal.Buchholz.Smoke where

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; fin
  ; ω
  ; _≤Ω_
  ; fin≤fin
  ; fin≤ω
  ; ω≤ω
  ; ≤Ω-refl
  ; ≤Ω-trans
  ; Omega0
  ; Omega1
  ; Omegaω
  ; Omega0≤Omega1
  ; Omega0≤Omegaω
  ; Omega1≤Omegaω
  )

open import Ordinal.Buchholz.Syntax using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  ; psi0
  )

open import Ordinal.Buchholz.Closure using
  ( Cν
  ; cν-zero
  ; cν-omega
  ; cν-plus
  ; cν-psi
  ; Cν-monotone
  ; Cν-index-monotone
  ; Cν-monotone-both
  ; cν-omega-index
  ; cν-psi-index
  ; cν-psi-decompose
  )

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
  ; <ᵇ-+ω
  ; <ᵇ-+ψω
  ; <ᵇ-+1
  ; <ᵇ-irrefl
  ; <ᵇ-trans
  ; <ᵇ-inv-Ω+
  ; <ᵇ-inv-+Ω
  ; <ᵇ-inv-+Ωfin
  ; <ᵇ-inv-+Ωω
  ; <ᵇ-inv-ψ+
  ; <ᵇ-inv-+ψ
  ; <ᵇ-inv-+ψfin
  ; <ᵇ-inv-+ψω
  )

open import Ordinal.Buchholz.Psi using
  ( psiν-notin-Cν
  ; psiν-stage-lb
  ; psiν-index-bound
  )

open import Ordinal.Buchholz.Examples using
  ( bh-psi0-omega1
  ; bh-psi0-omegaω
  ; psi0-expands
  ; psi0-Omega1-target
  ; omega1-in-C1-at-0
  ; psi0-omega1-at-1-in-C1
  ; psi0-omega1-not-at-0-in-C1
  ; psi0-omega1-stage-lb-in-C1
  ; omega1-in-Cω-at-0
  ; psi0-omega1-at-1
  ; psi0-omega1-not-at-0
  )

open import Ordinal.Buchholz.WellFounded using
  ( <Ω-wf
  ; wf-<ᵇ
  ; <ᵇ-irreflexive
  )

open import Ordinal.Buchholz.WellFormed using
  ( WfΩ
  ; WfBT
  ; wf-fin
  ; wf-ω
  ; wf-bzero
  ; wf-bomega
  ; wf-bplus
  ; wf-bpsi
  ; BH
  ; BH-wf
  ; psi-OmegaOmega
  ; psi-OmegaOmega-wf
  )

open import Ordinal.Buchholz.VeblenInterface using
  ( VeblenWFInterface
  )

open import Ordinal.Buchholz.VeblenIdentityModel using
  ( identity-interface
  ; core-wf-from-identity
  )

open import Ordinal.Buchholz.VeblenMeasureTarget using
  ( Measure
  ; _≺M_
  ; by-index
  ; by-term
  ; ≺M-wf
  )

open import Ordinal.Buchholz.VeblenProjectionMeasure using
  ( proj-index
  ; proj-term
  ; proj-measure
  ; proj-dec-+2
  ; proj-dec-ψα
  ; proj-dec-ΩΩ
  ; proj-dec-Ωψ
  ; proj-dec-ψΩ
  ; proj-dec-ψΩ<
  )

open import Ordinal.Buchholz.VeblenComparisonTarget using
  ( ComparisonMeasure
  ; _≈ᶜ_
  ; _≺C_
  ; ≈ᶜ-+
  ; ≈ᶜ-ψ
  ; ≈ᶜ-ψ+
  ; ≺P-trans
  ; ≺C-trans
  ; by-first
  ; by-second
  ; ≺C-wf
  )

open import Ordinal.Buchholz.VeblenComparisonModel using
  ( cmp-payload
  ; cmp-measure
  ; cmp-dec-Ω+
  ; cmp-dec-ψ+-same-index
  ; cmp-dec-ψ+
  ; comparison-interface
  ; core-wf-from-comparison
  )

open import Ordinal.Buchholz.ExtendedOrder using
  ( _<ᵇ⁺_
  ; <ᵇ⇒<ᵇ⁺
  ; <ᵇ⁺-ψα
  ; <ᵇ⁺-+2
  ; <ᵇ⁺-trans
  ; wf-<ᵇ⁺
  ; <ᵇ⁺-irreflexive
  )

open import Ordinal.Buchholz.LiftedExtendedOrder using
  ( _<ᵇ⁺¹_
  ; <ᵇ⁺⇒<ᵇ⁺¹
  ; <ᵇ⁺¹-ψα
  ; <ᵇ⁺¹-+2
  ; <ᵇ⁺¹-ψ+2
  ; wf-<ᵇ⁺¹
  ; <ᵇ⁺¹-irreflexive
  )

open import Ordinal.Buchholz.IteratedExtendedOrder using
  ( LiftedOrder
  ; LiftedOrder-wf
  ; LiftedOrder-trans
  ; LiftedOrder-lift
  ; lift-ψα
  ; lift-+2
  ; lift-ψ+2
  ; LiftedOrder-irreflexive
  ; SurfaceDepth
  ; surf-core
  ; surf-ψα
  ; surf-+2
  ; surface⇒lifted
  ; SurfaceDepth-irreflexive
  )

open import Ordinal.Buchholz.SurfaceOrder using
  ( _<ᵇˢ_
  ; <ᵇˢ-core
  ; <ᵇˢ-ψα
  ; <ᵇˢ-+2
  ; <ᵇˢ⇒<ᵇ⁺
  ; wf-<ᵇˢ
  ; <ᵇˢ-irreflexive
  ; SurfaceLiftInterface
  ; _<ᵇʳ_
  ; <ᵇʳ-core
  ; <ᵇʳ-ψα
  ; <ᵇʳ-+2
  ; <ᵇʳ⇒<ᵇ⁺
  ; wf-<ᵇʳ
  ; <ᵇʳ-irreflexive
  ; <ᵇ⁺-no-ψ-bzero-plus
  ; surfaceLiftPremise
  ; surfaceLiftBlocked
  )

open import Ordinal.Buchholz.VeblenObligations using
  ( plus-right
  ; psi-arg
  ; dec-+2-plus-right
  ; dec-ψα-psi-arg
  )
