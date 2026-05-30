{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- WfCNF-wrapped variant of the union rank-mono umbrella (2026-05-30).
--
-- ## What this lands
--
-- Mirrors `Ordinal.Buchholz.RankMonoUmbrellaSlice4._<ᵇ⁻ⁿ_`'s
-- WfCNF-bundling pattern over the union umbrella's `_<ᵇᵘ_` from
-- `Ordinal.Buchholz.RankMonoUnion`.  The narrowed relation
-- `_<ᵇᵘⁿ_` bundles:
--
--   * `wf-x  : WfCNF x`        — source-side canonical-form witness
--   * `wf-y  : WfCNF y`        — target-side canonical-form witness
--   * `<ᵇᵘ-d : x <ᵇᵘ y`        — the union derivation
--
-- The narrowed relation's `rank-pow-mono-<ᵇᵘⁿ` discharges via
-- `rank-pow-mono-<ᵇᵘ` on the bundled derivation.
--
-- ## Why this exists
--
-- Downstream Buchholz consumers (e.g., the surface-route well-
-- foundedness work in `Ordinal.Buchholz.RecursiveSurfaceOrder`)
-- need the WfCNF invariant carried alongside the rank-relation
-- so they don't have to re-discover it via separate proof
-- structure.  Slice 4's `_<ᵇ⁻ⁿ_` provides this for the strict-
-- head joint-bplus extension; this module provides the
-- analogous wrap for the full union umbrella.
--
-- ## Mechanical extension
--
-- This module is the WfCNF-wrap template for any future union
-- extension that adds new source-rule slots.  The recipe:
--
--   1. Add the new disjunct to `_<ᵇᵘ_` in `RankMonoUnion`.
--   2. The mediator `rank-pow-mono-<ᵇᵘ` extends with the new
--      case via `[_,_]`.
--   3. THIS MODULE updates AUTOMATICALLY because the record
--      embeds the union's relation — no edit needed here.
--
-- The architectural payoff documented in `RankMonoUnion`'s
-- preamble holds across the WfCNF wrap as well: per-extension
-- proof work + structural composition.

module Ordinal.Buchholz.RankMonoUnionWfCNF where

open import Ordinal.Brouwer.Phase13                using (_<′_)
open import Ordinal.Buchholz.Syntax                using (BT)
open import Ordinal.Buchholz.RankPow               using (rank-pow)
open import Ordinal.Buchholz.WellFormedCNF         using (WfCNF)
open import Ordinal.Buchholz.RankMonoUmbrella      using (_<ᵇ⁰_)
open import Ordinal.Buchholz.RankMonoUmbrellaSlice3 using (_<ᵇ¹_)
open import Ordinal.Buchholz.RankMonoSameLeft      using (_<ᵇ⁺²_)
open import Ordinal.Buchholz.RankMonoUnion         using
  ( _<ᵇᵘ_
  ; rank-pow-mono-<ᵇᵘ
  ; <ᵇᵘ-from-<ᵇ¹
  ; <ᵇᵘ-from-<ᵇ⁺²
  ; <ᵇᵘ-from-<ᵇ⁰
  )

----------------------------------------------------------------------
-- The WfCNF-narrowed union relation `_<ᵇᵘⁿ_`
----------------------------------------------------------------------

-- Bundles WfCNF endpoints together with a `_<ᵇᵘ_` derivation.
-- Same shape as `RankMonoUmbrellaSlice4._<ᵇ⁻ⁿ_` but over the
-- union umbrella.  The WfCNF fields are unused inside the
-- rank-pow-mono closure but available to consumers reasoning
-- about the canonical-form invariant of the endpoints (e.g.,
-- downstream well-foundedness work).

record _<ᵇᵘⁿ_ (x y : BT) : Set where
  constructor mk<ᵇᵘⁿ
  field
    wf-x  : WfCNF x
    wf-y  : WfCNF y
    <ᵇᵘ-d : x <ᵇᵘ y

open _<ᵇᵘⁿ_ public

infix 4 _<ᵇᵘⁿ_

----------------------------------------------------------------------
-- Constructor-level embeddings
----------------------------------------------------------------------

-- Inherit any `_<ᵇ⁰_` derivation as a narrowed `_<ᵇᵘⁿ_`
-- derivation under WfCNF endpoints.  Forwards through the
-- canonical `<ᵇ¹` embedding path of `_<ᵇᵘ_`.

<ᵇᵘⁿ-from-<ᵇ⁰ :
  ∀ {x y} → WfCNF x → WfCNF y → x <ᵇ⁰ y → x <ᵇᵘⁿ y
<ᵇᵘⁿ-from-<ᵇ⁰ wf-x wf-y p =
  mk<ᵇᵘⁿ wf-x wf-y (<ᵇᵘ-from-<ᵇ⁰ p)

-- Embed an `_<ᵇ¹_` derivation as a narrowed `_<ᵇᵘⁿ_` derivation.
-- Covers the strict-head joint-bplus case via `<ᵇ¹-+1-+`.

<ᵇᵘⁿ-from-<ᵇ¹ :
  ∀ {x y} → WfCNF x → WfCNF y → x <ᵇ¹ y → x <ᵇᵘⁿ y
<ᵇᵘⁿ-from-<ᵇ¹ wf-x wf-y p =
  mk<ᵇᵘⁿ wf-x wf-y (<ᵇᵘ-from-<ᵇ¹ p)

-- Embed an `_<ᵇ⁺²_` derivation as a narrowed `_<ᵇᵘⁿ_` derivation.
-- Covers the Path-3 same-left joint-bplus case via
-- `<ᵇ⁺²-same-left`.

<ᵇᵘⁿ-from-<ᵇ⁺² :
  ∀ {x y} → WfCNF x → WfCNF y → x <ᵇ⁺² y → x <ᵇᵘⁿ y
<ᵇᵘⁿ-from-<ᵇ⁺² wf-x wf-y p =
  mk<ᵇᵘⁿ wf-x wf-y (<ᵇᵘ-from-<ᵇ⁺² p)

----------------------------------------------------------------------
-- Rank-pow monotonicity
----------------------------------------------------------------------

-- Forwards directly to `rank-pow-mono-<ᵇᵘ` via the bundled
-- derivation.  The WfCNF fields are unused inside the proof
-- but available to consumers reasoning about the endpoints.
-- Same shape as `RankMonoUmbrellaSlice4.rank-pow-mono-<ᵇ⁻ⁿ`.

rank-pow-mono-<ᵇᵘⁿ : ∀ {x y} → x <ᵇᵘⁿ y → rank-pow x <′ rank-pow y
rank-pow-mono-<ᵇᵘⁿ p = rank-pow-mono-<ᵇᵘ (<ᵇᵘ-d p)
