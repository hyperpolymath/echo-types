{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

------------------------------------------------------------------------
-- Gate 2 audit: VisibleConstraintAudit
--
-- Falsifier exhibit for nominee N1 — `visible-constraint` from
-- `EchoCharacteristic`, listed in `roadmap-gates.adoc` as one of three
-- candidate "characteristic" theorems.
--
-- Claim: `visible-constraint` is the second Σ-projection after
-- definitional unfolding of `visible := proj₁`. It therefore survives
-- only as "fiber lemma with renamed components" — a phrasing
-- `roadmap-gates.adoc` explicitly disallows.
--
-- This module makes the reduction formal: the nominee reduces to
-- `proj₂` by `refl`. See `docs/gate-2-characteristic.adoc` §3 for the
-- prose audit and §6 for the threshold consequence.
------------------------------------------------------------------------

module characteristic.VisibleConstraintAudit where

open import Data.Bool.Base                        using (Bool)
open import Data.Product.Base                     using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo                                  using (Echo)
open import EchoCharacteristic                    using (visible; visible-constraint)

------------------------------------------------------------------------
-- The reduction
--
-- `visible := proj₁ : State → Bool`. Therefore `Echo visible y` unfolds
-- to `Σ State (λ s → proj₁ s ≡ y)`. The standard second projection
-- `proj₂ : (e : Σ State (λ s → proj₁ s ≡ y)) → proj₁ (proj₁ e) ≡ y`
-- returns the same value, on the same input, as `visible-constraint`.
--
-- Both compute by `refl`. The function `visible-constraint` adds no
-- content beyond what `proj₂` already does on the underlying Σ.
------------------------------------------------------------------------

visible-constraint-is-proj₂ :
  ∀ {y : Bool} (e : Echo visible y) →
  visible-constraint e ≡ proj₂ e
visible-constraint-is-proj₂ (_ , _) = refl

------------------------------------------------------------------------
-- Gate-2 consequence (prose; the formal content is the lemma above)
--
-- `roadmap-gates.adoc` Gate 2:
--
--   "A theorem that survives only as 'fiber lemma X with renamed
--    components' does not count."
--
-- `visible-constraint` is `proj₂` with renamed components. Per the
-- audit in `docs/gate-2-characteristic.adoc`, this nominee fails the
-- strict reading of the test. The Gate-2 threshold (≥ 2 of 3 survive)
-- is then carried by N2 and N3 alone.
--
-- Note: the strict reading does *not* erase the lemma's expository
-- value. It states cleanly *what* the residue retains, in the
-- vocabulary of structured loss. The strict reading only denies it the
-- status of an echo-shaped *theorem* — it is a Σ-projection in
-- echo-shaped *prose*.
------------------------------------------------------------------------
