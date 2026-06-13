{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Well-foundedness of the union rank-mono umbrella (2026-05-30).
--
-- ## What this lands
--
-- `wf-<ᵇᵘ : WellFounded _<ᵇᵘ_` — every union-derivation chain
-- terminates.  Derived mechanically from `rank-pow-mono-<ᵇᵘ`
-- (PR #168) and the well-foundedness of Brouwer's `_<′_` (already
-- proved in `Ordinal.Brouwer.Phase13.wf-<′`) via the standard
-- Subrelation + InverseImage combinators from
-- `Induction.WellFounded` / `Relation.Binary.Construct.On`.
--
-- ## The rank-embedding recipe
--
-- This is the standard rank-WF transport pattern documented in
-- `Ordinal.Buchholz.RankBrouwer`'s preamble:
--
--   wf-<ᵇᵘ = Subrelation.wellFounded rank-pow-mono-<ᵇᵘ
--              (On.wellFounded rank-pow wf-<′)
--
-- 1. `On.wellFounded rank-pow wf-<′` lifts well-foundedness of
--    `_<′_` on `Ord` to the pullback `_<′_ on rank-pow` on `BT`
--    — InverseImage transport.
-- 2. `Subrelation.wellFounded rank-pow-mono-<ᵇᵘ` then transports
--    well-foundedness from the pullback to `_<ᵇᵘ_` itself,
--    consuming `rank-pow-mono-<ᵇᵘ : x <ᵇᵘ y → rank-pow x <′ rank-pow y`
--    as the witness that `_<ᵇᵘ_` is a sub-relation of the pullback.
--
-- The recipe is purely structural: zero new proof obligations.
-- Closure follows from the existing `rank-pow-mono-<ᵇᵘ` (#168)
-- + the existing `wf-<′` (`Phase13`).
--
-- ## Slice 3+4 Route A gate 2 closure
--
-- Per #168's closing note, three gates remained open at the
-- architectural-realisation moment.  This module discharges
-- **Gate 2** (well-foundedness of `_<ᵇᵘ_`) via the rank-embedding
-- transport, leaving:
--
--   * Gate 1 — tail-rank-equality discharge for the cross-head
--     rank-equal case (structural ordinal-arithmetic blocker).
--   * Gate 3 — Path-4 + further source-rule extensions
--     (future-work, mechanical per the extension recipe).
--
-- ## Scope notes
--
-- * The WfCNF-narrowed `_<ᵇᵘⁿ_` (PR #169) well-foundedness,
--   previously deferred here, is now provided as `wf-<ᵇᵘⁿ`
--   below — the same Subrelation transport routed through its
--   `rank-pow-mono-<ᵇᵘⁿ` mediator (equivalently, through the
--   canonical `<ᵇᵘⁿ → <ᵇᵘ` projection).  This serves the
--   surface-route WF consumer in `RecursiveSurfaceOrder`.
-- * Does NOT add a Brouwer-rank embedding stronger than
--   `rank-pow` — `rank-pow` is K-free + lands in `Ord` (Brouwer
--   ordinals) + already discharges the WF transport.  Nothing
--   more sophisticated is needed for this consumer.

module Ordinal.Buchholz.RankMonoUnionWF where

open import Induction.WellFounded               using
  ( WellFounded
  ; module Subrelation
  )
open import Relation.Binary.Construct.On as On  using (wellFounded)

open import Ordinal.Brouwer                     using (Ord)
open import Ordinal.Brouwer.Phase13             using (_<′_; wf-<′)
open import Ordinal.Buchholz.Syntax             using (BT)
open import Ordinal.Buchholz.RankPow            using (rank-pow)
open import Ordinal.Buchholz.RankMonoUnion      using
  ( _<ᵇᵘ_
  ; rank-pow-mono-<ᵇᵘ
  )
open import Ordinal.Buchholz.RankMonoUnionWfCNF using
  ( _<ᵇᵘⁿ_
  ; rank-pow-mono-<ᵇᵘⁿ
  )

----------------------------------------------------------------------
-- Well-foundedness of `_<ᵇᵘ_`
----------------------------------------------------------------------

-- Step 1 — InverseImage transport: well-foundedness of `_<′_` on
-- `Ord` lifts to well-foundedness of `_<′_ on rank-pow` on `BT`.
-- Note that the pullback relation has the same shape as
-- `rank-pow x <′ rank-pow y` but is named `_<′_ on rank-pow`.

wf-rank-pow-pullback : WellFounded (λ x y → rank-pow x <′ rank-pow y)
wf-rank-pow-pullback = On.wellFounded rank-pow wf-<′

-- Step 2 — Subrelation transport: any sub-relation of a well-
-- founded relation is well-founded.  `rank-pow-mono-<ᵇᵘ` is the
-- witness that `_<ᵇᵘ_` is a sub-relation of `_<′_ on rank-pow`,
-- so `_<ᵇᵘ_` inherits well-foundedness.

wf-<ᵇᵘ : WellFounded _<ᵇᵘ_
wf-<ᵇᵘ = Subrelation.wellFounded rank-pow-mono-<ᵇᵘ wf-rank-pow-pullback

----------------------------------------------------------------------
-- Well-foundedness of the WfCNF-narrowed `_<ᵇᵘⁿ_`
----------------------------------------------------------------------

-- The consumer-facing bundled form (`RankMonoUnionWfCNF._<ᵇᵘⁿ_`)
-- carries the WfCNF endpoint witnesses alongside the union
-- derivation.  Its well-foundedness is the same two-step transport
-- as `wf-<ᵇᵘ`: the bundled `rank-pow-mono-<ᵇᵘⁿ` mediator witnesses
-- that `_<ᵇᵘⁿ_` is a sub-relation of `_<′_ on rank-pow`, so it
-- inherits well-foundedness from `wf-rank-pow-pullback`.  (The WfCNF
-- fields ride along unused in the WF proof, exactly as they do in
-- the rank-mono mediator.)

wf-<ᵇᵘⁿ : WellFounded _<ᵇᵘⁿ_
wf-<ᵇᵘⁿ = Subrelation.wellFounded rank-pow-mono-<ᵇᵘⁿ wf-rank-pow-pullback
