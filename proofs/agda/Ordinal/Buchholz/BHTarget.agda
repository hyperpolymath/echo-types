{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Bachmann–Howard TARGET STRUCTURE — the real, postulate-free part of
-- the order-type fidelity target (open problem D-2026-06-14). 2026-06-15.
--
-- ## What this module IS
--
-- The `BHNotation` interface (an abstract well-founded strict order with
-- a distinguished element) TOGETHER WITH a concrete, postulate-free
-- constructor `bh-notation-from` that builds a genuine instance from the
-- repo's existing Brouwer ordinal order:
--
--   𝒪         := Ord                (Ordinal.Brouwer)
--   _<𝒪_      := _<′_               (Ordinal.Brouwer.Phase13)
--   wf-<𝒪     := wf-<′              (PROVED, postulate-free, --safe)
--   bh-height := the supplied Ord   (the only free choice)
--
-- ## Why this matters (trust-boundary reduction)
--
-- `Fidelity.agda` previously postulated the WHOLE `bh-notation :
-- BHNotation` opaquely — assuming a Set, an order, ITS WELL-FOUNDEDNESS,
-- and a distinguished element. This module discharges three of those
-- four obligations FOR REAL inside the --safe kernel: the target order
-- and its well-foundedness are now the genuine Brouwer `_<′_` / `wf-<′`,
-- not assumptions. Only the distinguished `bh-height` (i.e. WHICH `Ord`
-- value is ψ₀(Ω_ω)) remains a free input — handed to `Fidelity` as an
-- explicit module parameter, with its ψ₀(Ω_ω)-meaning pinned downstream
-- by the (still-open) `denotation.pins-BH` field, not by fiat. See
-- Fidelity-OPEN-postulates.md.
--
-- ## What this module is NOT
--
--   * It does NOT claim the Brouwer order `_<′_` HAS order type ψ₀(Ω_ω),
--     nor that any particular `Ord` value IS ψ₀(Ω_ω). Brouwer ordinals
--     reach far past ψ₀(Ω_ω); identifying the right value and proving the
--     initial-segment order type is exactly the faithful `denotation`
--     work that remains OPEN (D-2026-06-14).
--   * It does NOT reuse `rank2`. The faithful denotation must be
--     height-preserving; `rank2` collapses heights. `bh-notation-from`
--     fixes only the ORDER, not the embedding, so it does not prejudge
--     `denotation`.

module Ordinal.Buchholz.BHTarget where

open import Induction.WellFounded using (WellFounded)

open import Ordinal.Brouwer using (Ord)
open import Ordinal.Brouwer.Phase13 using (_<′_; wf-<′)

----------------------------------------------------------------------
-- The Bachmann–Howard target INTERFACE
----------------------------------------------------------------------

-- An abstract well-founded strict order with a distinguished element
-- `bh-height` standing for the order type ψ₀(Ω_ω). (Whether a given
-- instance's `bh-height` REALLY has that initial segment is the content
-- of the fidelity embedding, not of this interface.)
record BHNotation : Set₁ where
  field
    𝒪         : Set
    _<𝒪_      : 𝒪 → 𝒪 → Set
    wf-<𝒪     : WellFounded _<𝒪_
    bh-height : 𝒪

----------------------------------------------------------------------
-- A concrete, postulate-free instance from the Brouwer order
----------------------------------------------------------------------

-- Given any `Ord` value as the candidate BH height, the Brouwer order
-- `(Ord, _<′_, wf-<′)` furnishes a genuine `BHNotation`. The order and
-- its well-foundedness are REAL (no postulate); only the height is the
-- caller's choice.
bh-notation-from : Ord → BHNotation
bh-notation-from h = record
  { 𝒪         = Ord
  ; _<𝒪_      = _<′_
  ; wf-<𝒪     = wf-<′
  ; bh-height = h
  }
