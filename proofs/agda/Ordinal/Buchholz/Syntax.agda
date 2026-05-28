{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

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
