{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Sound-carrier extended order — the K-limited shared-binder cases,
-- unbudgeted (2026-06-14).
--
-- ## What this lands
--
-- `_<ᵇ⁺²_` — the doubled-ladder sound-carrier analogue of
-- `Ordinal.Buchholz.OrderExtended._<ᵇ⁺_`: the sound core `_<ᵇ²_` plus
-- the two K-limited shared-binder constructors (`<ᵇ⁺²-ψα`,
-- `<ᵇ⁺²-+2`), each a ONE-step extension whose inner premise is `_<ᵇ²_`
-- (not the native `_<ᵇ_` that `OrderExtended` uses).  Its
-- well-foundedness `wf-<ᵇ⁺²` is UNBUDGETED.
--
-- ## Why this closes roadmap item #2 in its achievable form
--
-- The native `_<ᵇ⁺_` (`OrderExtended`) carries the same two
-- shared-binder rules but over native `_<ᵇ_`; its well-foundedness is
-- OPEN (only the budgeted `OrderExtendedBudget.wf-<ᵇ⁺ᵇ` exists),
-- walled for the same reason as everything native: `_<ᵇ_` is
-- ordinally unsound (the `<ᵇ-+Ω` counterexample), so no rank embeds
-- it.  Restating the shared-binder extension over the SOUND carrier
-- `_<ᵇ²_` removes the obstruction: every `_<ᵇ⁺²_` derivation is a
-- `_<ᵇʳᶠ²_` derivation (the one-step shared-binder case is the
-- `<ᵇʳᶠ²-core`-headed instance of the recursive congruence), so
-- `wf-<ᵇ⁺²` follows by `Subrelation` from the unbudgeted
-- `RecursiveSurfaceSound.wf-<ᵇʳᶠ²` — NO ℕ budget.
--
-- ## Honest scope
--
-- `_<ᵇ⁺²_` is to `_<ᵇ⁺_` what `_<ᵇ²_` is to native `_<ᵇ_` — the
-- ordinally-sound restriction.  It does NOT claim well-foundedness of
-- the native `_<ᵇ⁺_` (still walled; `OrderExtendedBudget`'s budgeted
-- form remains the native state of the art).  The contribution is that
-- the K-limited shared-binder extension is well-founded WITHOUT a
-- budget once its core + inner premises are the sound carrier.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `_<ᵇ⁺²_`
--   * `<ᵇ⁺²⇒<ᵇʳᶠ²`
--   * `wf-<ᵇ⁺²`

module Ordinal.Buchholz.OrderExtendedSound where

open import Induction.WellFounded using (WellFounded; module Subrelation)

open import Ordinal.Brouwer.Phase13 using (_<′_)
open import Ordinal.Buchholz.Syntax using (BT; bpsi; bplus)
open import Ordinal.Buchholz.RankDoubledLadder using (rank2)
open import Ordinal.Buchholz.RankDoubledLadderUmbrella using (_<ᵇ²_)
open import Ordinal.Buchholz.RecursiveSurfaceSound using
  ( _<ᵇʳᶠ²_
  ; <ᵇʳᶠ²-core
  ; <ᵇʳᶠ²-ψα
  ; <ᵇʳᶠ²-+2
  ; rank2-mono-<ᵇʳᶠ²
  ; wf-<ᵇʳᶠ²
  )

----------------------------------------------------------------------
-- The sound-carrier extended order `_<ᵇ⁺²_`
----------------------------------------------------------------------

-- Mirrors `OrderExtended._<ᵇ⁺_` with native `_<ᵇ_` replaced by the
-- sound carrier `_<ᵇ²_` in the base AND the shared-binder inner
-- premises.  Same-binder shape (single ν / single head x), as in
-- `_<ᵇʳᶠ²_` — no explicit equality witness needed under `--without-K`.
infix 4 _<ᵇ⁺²_

data _<ᵇ⁺²_ : BT → BT → Set where
  <ᵇ⁺²-base : ∀ {x y}   → x <ᵇ² y → x <ᵇ⁺² y
  <ᵇ⁺²-ψα   : ∀ {ν α β} → α <ᵇ² β → bpsi ν α <ᵇ⁺² bpsi ν β
  <ᵇ⁺²-+2   : ∀ {x y z} → y <ᵇ² z → bplus x y <ᵇ⁺² bplus x z

----------------------------------------------------------------------
-- Embedding into the recursive surface `_<ᵇʳᶠ²_`
----------------------------------------------------------------------

-- The one-step shared-binder extension is the `<ᵇʳᶠ²-core`-headed
-- instance of the recursive congruence: a `_<ᵇ²_` inner premise is a
-- single-step `_<ᵇʳᶠ²_` derivation via `<ᵇʳᶠ²-core`.
<ᵇ⁺²⇒<ᵇʳᶠ² : ∀ {x y} → x <ᵇ⁺² y → x <ᵇʳᶠ² y
<ᵇ⁺²⇒<ᵇʳᶠ² (<ᵇ⁺²-base p) = <ᵇʳᶠ²-core p
<ᵇ⁺²⇒<ᵇʳᶠ² (<ᵇ⁺²-ψα p)   = <ᵇʳᶠ²-ψα (<ᵇʳᶠ²-core p)
<ᵇ⁺²⇒<ᵇʳᶠ² (<ᵇ⁺²-+2 p)   = <ᵇʳᶠ²-+2 (<ᵇʳᶠ²-core p)

----------------------------------------------------------------------
-- rank2 monotonicity + unbudgeted well-foundedness
----------------------------------------------------------------------

-- rank2-mono via the embedding into the recursive surface.
rank2-mono-<ᵇ⁺² : ∀ {x y} → x <ᵇ⁺² y → rank2 x <′ rank2 y
rank2-mono-<ᵇ⁺² p = rank2-mono-<ᵇʳᶠ² (<ᵇ⁺²⇒<ᵇʳᶠ² p)

-- Well-foundedness: `_<ᵇ⁺²_` is a sub-relation of the already-WF
-- recursive surface `_<ᵇʳᶠ²_`.  NO ℕ budget.
wf-<ᵇ⁺² : WellFounded _<ᵇ⁺²_
wf-<ᵇ⁺² = Subrelation.wellFounded <ᵇ⁺²⇒<ᵇʳᶠ² wf-<ᵇʳᶠ²
