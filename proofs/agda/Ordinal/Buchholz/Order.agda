{-# OPTIONS --safe --without-K #-}

-- WF-1 core order for Buchholz terms.
--
-- This keeps the seven constructors that do not use the blocked
-- shared-binder cases `<ᵇ-ψα` and `<ᵇ-+2`.

module Ordinal.Buchholz.Order where

open import Data.Nat.Base using (ℕ; _<_)

open import Ordinal.OmegaMarkers using (OmegaIndex; fin)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)

data _<Ω_ : OmegaIndex → OmegaIndex → Set where
  <Ω-fin : ∀ {m n : ℕ} → m < n → fin m <Ω fin n

infix 4 _<Ω_

data _<ᵇ_ : BT → BT → Set where
  <ᵇ-0Ω : ∀ {μ} → bzero <ᵇ bOmega μ
  <ᵇ-0+ : ∀ {α β} → bzero <ᵇ bplus α β
  <ᵇ-0ψ : ∀ {μ α} → bzero <ᵇ bpsi μ α
  <ᵇ-Ω+ : ∀ {κ α β} → bOmega κ <ᵇ bplus α β
  <ᵇ-Ωψ : ∀ {κ μ α} → bOmega κ <ᵇ bpsi μ α
  <ᵇ-+1 : ∀ {α β γ} → α <ᵇ β → bplus α γ <ᵇ bplus β γ
  <ᵇ-ψν : ∀ {μ ν α} → μ <Ω ν → bpsi μ α <ᵇ bpsi ν α

infix 4 _<ᵇ_
