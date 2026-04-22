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
  )

open import Ordinal.Buchholz.Psi using
  ( psiν-notin-Cν
  ; psiν-stage-lb
  )

open import Ordinal.Buchholz.Examples using
  ( bh-psi0-omega1
  ; bh-psi0-omegaω
  ; psi0-expands
  ; omega1-in-Cω-at-0
  ; psi0-omega1-at-1
  ; psi0-omega1-not-at-0
  )
