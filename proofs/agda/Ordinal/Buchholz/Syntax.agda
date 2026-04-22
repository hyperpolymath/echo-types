{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Pure Buchholz-style term syntax over Ω-indices. This module is only
-- structural syntax; ordering, normal forms, and semantics are staged
-- in later milestones.

module Ordinal.Buchholz.Syntax where

open import Ordinal.OmegaMarkers using (OmegaIndex; Omega0)

data BT : Set where
  bzero  : BT
  bOmega : OmegaIndex → BT
  bplus  : BT → BT → BT
  bpsi   : OmegaIndex → BT → BT

-- The common ψ₀ abbreviation.

psi0 : BT → BT
psi0 α = bpsi Omega0 α
