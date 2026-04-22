{-# OPTIONS --safe --without-K #-}

-- Stage S2/S3 scaffolding for docs/buchholz-plan.adoc.
--
-- A lightweight well-formedness layer for Buchholz terms. This module
-- keeps the shape explicit while the full normal-form / ordering theory
-- is still under construction.

module Ordinal.Buchholz.WellFormed where

open import Data.Nat.Base using (ℕ)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin; ω; Omega0; Omegaω)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)

data WfΩ : OmegaIndex → Set where
  wf-fin : ∀ {n : ℕ} → WfΩ (fin n)
  wf-ω   : WfΩ ω

data WfBT : BT → Set where
  wf-bzero  : WfBT bzero
  wf-bomega : ∀ {μ} → WfΩ μ → WfBT (bOmega μ)
  wf-bplus  : ∀ {x y} → WfBT x → WfBT y → WfBT (bplus x y)
  wf-bpsi   : ∀ {μ α} → WfΩ μ → WfBT α → WfBT (bpsi μ α)

-- Stage-S2 target witness term: ψ₀(Ω_ω) (Bachmann–Howard marker form).

BH : BT
BH = bpsi Omega0 (bOmega Omegaω)

BH-wf : WfBT BH
BH-wf = wf-bpsi wf-fin (wf-bomega wf-ω)

-- Stage-S3 proxy witness in the current marker language.
-- We do not yet have Ω_{Ω_ω} as a distinct index constructor, so we use
-- a nested ψ-shape that is already representable and non-trivial.

psi-OmegaOmega : BT
psi-OmegaOmega = bpsi Omega0 (bpsi Omegaω (bOmega Omegaω))

psi-OmegaOmega-wf : WfBT psi-OmegaOmega
psi-OmegaOmega-wf = wf-bpsi wf-fin (wf-bpsi wf-ω (wf-bomega wf-ω))
