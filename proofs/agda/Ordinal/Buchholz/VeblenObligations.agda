{-# OPTIONS --safe --without-K #-}

-- Step 7a (Veblen-route obligations): isolate the deferred same-binder
-- obligations and prove the easiest one first.
--
-- This module does not yet provide a full Veblen measure model. It
-- records/proves obligation-shaped lemmas that can be reused when the
-- final measure is assembled.

module Ordinal.Buchholz.VeblenObligations where

open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_)

-- Project the right summand of a plus-term; non-plus heads map to bzero.
plus-right : BT → BT
plus-right bzero        = bzero
plus-right (bOmega _)   = bzero
plus-right (bpsi _ _)   = bzero
plus-right (bplus _ y₂) = y₂

-- First discharged same-binder obligation shape:
-- if y₂ <ᵇ z₂ then right-projection decreases across bplus x _.
dec-+2-plus-right :
  ∀ {x y₂ z₂} →
  y₂ <ᵇ z₂ →
  plus-right (bplus x y₂) <ᵇ plus-right (bplus x z₂)
dec-+2-plus-right y₂<z₂ = y₂<z₂

-- Project the ψ argument; non-ψ heads map to bzero.
psi-arg : BT → BT
psi-arg bzero      = bzero
psi-arg (bOmega _) = bzero
psi-arg (bplus _ _) = bzero
psi-arg (bpsi _ α) = α

-- Sibling same-binder obligation shape:
-- if α <ᵇ β then ψ-argument projection decreases across bpsi ν _.
dec-ψα-psi-arg :
  ∀ {ν α β} →
  α <ᵇ β →
  psi-arg (bpsi ν α) <ᵇ psi-arg (bpsi ν β)
dec-ψα-psi-arg α<β = α<β
