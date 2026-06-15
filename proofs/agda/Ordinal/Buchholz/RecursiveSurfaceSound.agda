{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Unbudgeted recursive-surface descent over the SOUND carrier
-- (2026-06-14).
--
-- ## What this lands
--
-- `_<ᵇʳᶠ²_` — the recursive same-binder closure over the doubled-ladder
-- sound carrier `_<ᵇ²_` (`RankDoubledLadderUmbrella`) instead of native
-- `_<ᵇ_`, with its UNBUDGETED well-foundedness:
--
--   * `rank2-mono-<ᵇʳᶠ² : s <ᵇʳᶠ² t → rank2 s <′ rank2 t`
--   * `wf-<ᵇʳᶠ² : WellFounded _<ᵇʳᶠ²_`
--
-- ## Why the budget is no longer needed
--
-- The existing `RecursiveSurfaceBudget._<ᵇʳᶠᵇ_` carries an explicit ℕ
-- depth budget precisely because its `_<ᵇʳᶠ_` is built over NATIVE
-- `_<ᵇ_`, whose `<ᵇʳᶠ-core` case is ordinally UNSOUND: no rank embeds
-- it (the `<ᵇ-+Ω` counterexample `bplus bzero (bOmega (fin 1)) <ᵇ
-- bOmega (fin 0)` forces `rank-mono` to invert).  See
-- `RankBrouwer.agda`'s preamble and `buchholz-rank-obstruction.adoc`:
-- the rank / direct-mutual / lex / tower / inverse-image routes to the
-- GLOBAL unbudgeted `wf-<ᵇʳᶠ` over native `_<ᵇ_` are all walled, and
-- `rank2` does not escape it (the same counterexample defeats `rank2`).
--
-- The documented "recommended next move 1" is the WF-RESTRICTED
-- relation.  This module realises it: building the recursive surface
-- over the SOUND carrier `_<ᵇ²_` makes all three cases rank2-embeddable,
-- so well-foundedness follows by the standard rank transport WITHOUT a
-- budget:
--
--   * `<ᵇʳᶠ²-core` — `rank2-mono-<ᵇ²` (this session's umbrella);
--   * `<ᵇʳᶠ²-ψα`   — `⊕-mono-<-right` on `rank2 α <′ rank2 β`
--                    (`rank2 (bpsi ν α) = ω-rank-pow (double ν) ⊕ rank2 α`);
--   * `<ᵇʳᶠ²-+2`   — `⊕-mono-<-right` on `rank2 y <′ rank2 z`
--                    (`rank2 (bplus x y) = rank2 x ⊕ rank2 y`).
--
-- The latter two are exactly the two congruence cases the
-- `RankBrouwer` preamble already identified as discharged by
-- `⊕-mono-<-right`; the doubled ladder supplies the missing core case.
--
-- ## Honest scope
--
-- `_<ᵇʳᶠ²_` is the sound-carrier recursive surface — it is to
-- `_<ᵇʳᶠ_` what `_<ᵇ²_` is to native `_<ᵇ_`: the ordinally-sound
-- restriction.  It does NOT claim the GLOBAL unbudgeted `wf-<ᵇʳᶠ` over
-- native `_<ᵇ_` (that remains walled per the obstruction note).  Its
-- contribution is that the recursive-surface route is well-founded
-- WITHOUT the ℕ budget once the core is the sound carrier — the budget
-- was an artefact of native unsoundness, not of the same-binder
-- recursion itself.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `_<ᵇʳᶠ²_`
--   * `rank2-mono-<ᵇʳᶠ²`
--   * `wf-<ᵇʳᶠ²`

module Ordinal.Buchholz.RecursiveSurfaceSound where

open import Induction.WellFounded               using (WellFounded; module Subrelation)
open import Relation.Binary.Construct.On as On  using (wellFounded)

open import Ordinal.Brouwer                     using (Ord)
open import Ordinal.Brouwer.Phase13             using (_<′_; ⊕-mono-<-right; wf-<′)
open import Ordinal.Brouwer.Arithmetic          using (_⊕_)
open import Ordinal.Buchholz.Syntax             using (BT; bpsi; bplus)
open import Ordinal.Buchholz.RankPow            using (ω-rank-pow)
open import Ordinal.Buchholz.RankDoubledLadder  using (rank2; double)
open import Ordinal.Buchholz.RankDoubledLadderUmbrella using
  ( _<ᵇ²_
  ; rank2-mono-<ᵇ²
  )

----------------------------------------------------------------------
-- The sound-carrier recursive surface `_<ᵇʳᶠ²_`
----------------------------------------------------------------------

-- Native `_<ᵇ_` replaced by the sound carrier `_<ᵇ²_` in the core
-- rule; the two same-binder congruence rules are unchanged.
infix 4 _<ᵇʳᶠ²_

data _<ᵇʳᶠ²_ : BT → BT → Set where
  <ᵇʳᶠ²-core : ∀ {x y}   → x <ᵇ² y       → x <ᵇʳᶠ² y
  <ᵇʳᶠ²-ψα   : ∀ {ν α β} → α <ᵇʳᶠ² β     → bpsi ν α <ᵇʳᶠ² bpsi ν β
  <ᵇʳᶠ²-+2   : ∀ {x y z} → y <ᵇʳᶠ² z     → bplus x y <ᵇʳᶠ² bplus x z

----------------------------------------------------------------------
-- rank2 strict-monotonicity — no budget
----------------------------------------------------------------------

-- All three cases land directly: the core via the doubled-ladder
-- umbrella, the two congruences via right-strict-monotonicity of `⊕`
-- (the ψ-block leading power / the bplus head are the fixed left
-- summand).  Structural recursion on the `_<ᵇʳᶠ²_` derivation.
rank2-mono-<ᵇʳᶠ² : ∀ {s t} → s <ᵇʳᶠ² t → rank2 s <′ rank2 t
rank2-mono-<ᵇʳᶠ² (<ᵇʳᶠ²-core p)         = rank2-mono-<ᵇ² p
rank2-mono-<ᵇʳᶠ² (<ᵇʳᶠ²-ψα {ν} {α} {β} p) =
  ⊕-mono-<-right {ω-rank-pow (double ν)} {rank2 α} {rank2 β}
    (rank2-mono-<ᵇʳᶠ² p)
rank2-mono-<ᵇʳᶠ² (<ᵇʳᶠ²-+2 {x} {y} {z} p) =
  ⊕-mono-<-right {rank2 x} {rank2 y} {rank2 z}
    (rank2-mono-<ᵇʳᶠ² p)

----------------------------------------------------------------------
-- Unbudgeted well-foundedness via the rank2 embedding
----------------------------------------------------------------------

-- Step 1 — InverseImage transport of `wf-<′` along `rank2`.
wf-rank2-pullback : WellFounded (λ x y → rank2 x <′ rank2 y)
wf-rank2-pullback = On.wellFounded rank2 wf-<′

-- Step 2 — Subrelation transport: `rank2-mono-<ᵇʳᶠ²` witnesses that
-- `_<ᵇʳᶠ²_` is a sub-relation of the pullback.  NO ℕ budget.
wf-<ᵇʳᶠ² : WellFounded _<ᵇʳᶠ²_
wf-<ᵇʳᶠ² = Subrelation.wellFounded rank2-mono-<ᵇʳᶠ² wf-rank2-pullback
