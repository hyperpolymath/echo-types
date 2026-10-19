{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL aggregate root for CI only.
--
-- Typechecking this one file typechecks the whole echo-additive tree in a
-- single pass, so a cold (--ignore-interfaces) run builds the shared standard
-- library once instead of once per module.
--
-- NOT imported by proofs/agda/All.agda or Smoke.agda, and nothing in shipped
-- code imports from experimental/ (D-2026-06-14-R1 firewall; R-2026-05-18
-- stands). It adds no claim to the shipped closure.
--
-- Add any new module under experimental/echo-additive/ here, or CI will not
-- check it.

module experimental.echo-additive.All where

open import experimental.echo-additive.Grade
open import experimental.echo-additive.VarianceGate
open import experimental.echo-additive.GradedCarrier
open import experimental.echo-additive.GradedCarrierFaithful
open import experimental.echo-additive.GradedMonad
open import experimental.echo-additive.GradedComonad
open import experimental.echo-additive.GradedAdjunction
