{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Slice 3 headline of the head-Ω route — `rank-mono-<ᵇ-+1-via-head-Ω`.
--
-- Closes the joint-bplus rank-mono case for `_<ᵇ-+1_` UNDER A
-- STRICT-HEAD PREMISE supplied externally.  The premise
-- `head-Ω x₁ <Ω head-Ω y₁` lets the chain go through cleanly via
-- the Slice 3 prerequisites that landed in `RankPowSlice3`:
--
--   rank-pow (bplus x₁ x₂)
--     <′ ω-rank-pow-succ (head-Ω x₁)    -- rank-pow-dominated-by-head-Ω
--                                        --   + head-Ω-bplus (= head-Ω x₁)
--     ≤′ ω-rank-pow (head-Ω y₁)         -- ω-rank-pow-succ-≤-via-<Ω
--                                        --   (strict-head premise)
--     ≤′ rank-pow y₁                    -- head-Ω-lower-bound
--     ≤′ rank-pow (bplus y₁ y₂)         -- ⊕-left-≤-sum
--
-- The strict-head premise is the BURDEN this primitive bumps up to
-- the caller (Route A from `RankPowSlice3`'s design note).  The
-- caller — typically an extended `_<ᵇ¹_` umbrella with a new
-- joint-bplus constructor — derives it from:
--
--   * x₁ = bOmega μ:  `head-Ω-inv-bOmega` gives `μ <Ω head-Ω y₁`
--                     directly (strict for all three `<ᵇ-Ω_`
--                     constructors).
--   * x₁ = bpsi ν α:  `head-Ω-inv-bpsi` gives only `ν ≤Ω head-Ω y₁`
--                     (non-strict; `<ᵇ-ψΩ≤` permits equal markers).
--                     The strict jump must come from rank-adm /
--                     rank-lex second-component info (Route A
--                     combination).  When `ν = head-Ω y₁`, the
--                     caller dispatches to `rank-mono-<ᵇ-ψΩ≤-lex`
--                     instead of this headline; otherwise (strict
--                     ν <Ω head-Ω y₁) this headline applies.
--   * x₁ = bplus a b: `head-Ω (bplus a b) = head-Ω a`; recurse on
--                     the leftmost-leaf shape.
--
-- ## What this lands
--
--   * `rank-mono-<ᵇ-+1-via-head-Ω` — the headline, parametric in
--     the strict-head premise.
--
-- ## What this does NOT discharge
--
-- The bpsi-source-at-equality (`ν = head-Ω y₁`) case still requires
-- a rank-adm / rank-lex combination.  This module makes the headline
-- AVAILABLE for the strict-head cases; the umbrella's case-split is
-- where the caller decides which discharge to use.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `rank-mono-<ᵇ-+1-via-head-Ω`

module Ordinal.Buchholz.RankPowSlice3Headline where

open import Ordinal.Brouwer using (Ord; osuc)
open import Ordinal.Brouwer.Phase13 using
  ( _≤′_
  ; _<′_
  ; ≤′-trans
  ; osuc-mono-≤′
  ; ⊕-left-≤-sum
  )
open import Ordinal.OmegaMarkers using (_<Ω_)
open import Ordinal.Buchholz.Syntax using (BT; bplus)
open import Ordinal.Buchholz.WellFormedCNF using
  ( WfCNF
  ; wf-cnf-bplus
  )
open import Ordinal.Buchholz.HeadOmega using (head-Ω)
open import Ordinal.Buchholz.RankPow using
  ( rank-pow
  ; ω-rank-pow
  ; ω-rank-pow-succ
  )
open import Ordinal.Buchholz.RankPowDomination using
  ( rank-pow-dominated-by-head-Ω
  )
open import Ordinal.Buchholz.RankPowSlice3 using
  ( NonBzero
  ; ω-rank-pow-succ-≤-via-<Ω
  ; head-Ω-lower-bound
  )

----------------------------------------------------------------------
-- The Slice 3 headline
----------------------------------------------------------------------

-- For `bplus x₁ x₂ <ᵇ bplus y₁ y₂` from `x₁ <ᵇ y₁` (the `<ᵇ-+1`
-- constructor's source-strict case), the rank-mono conclusion
-- holds UNDER a strict-head premise on the source's and target's
-- leading Ω-markers.
--
-- The strict-head premise `head-Ω x₁ <Ω head-Ω y₁` is what the
-- caller's case-split on `x₁ <ᵇ y₁` provides.  By head-Ω-bplus,
-- `head-Ω (bplus x₁ x₂) = head-Ω x₁` (the source's leading marker
-- — definitional), so the strict-head step buys exactly the room
-- needed to fit the source under the target's `ω-rank-pow (head-Ω
-- y₁)` lower bound.
--
-- The chain (composing the prerequisites; no structural recursion):
--   1. `rank-pow (bplus x₁ x₂) <′ ω-rank-pow-succ (head-Ω x₁)` —
--      Slice 2-bplus (`rank-pow-dominated-by-head-Ω`); `head-Ω
--      (bplus x₁ x₂) = head-Ω x₁` definitionally.
--   2. `ω-rank-pow-succ (head-Ω x₁) ≤′ ω-rank-pow (head-Ω y₁)` —
--      strict-jump bridge (`ω-rank-pow-succ-≤-via-<Ω`) applied to
--      the strict-head premise.
--   3. `ω-rank-pow (head-Ω y₁) ≤′ rank-pow y₁` — head-Ω lower
--      bound (`head-Ω-lower-bound`) under WfCNF y₁ + NonBzero y₁.
--   4. `rank-pow y₁ ≤′ rank-pow (bplus y₁ y₂) = rank-pow y₁ ⊕
--      rank-pow y₂` — `⊕-left-≤-sum`.
--
-- All four steps compose via `≤′-trans` (recall `α <′ β` is just
-- `osuc α ≤′ β`, so the chain stays within `≤′` after the first
-- step's `osuc` shift).

rank-mono-<ᵇ-+1-via-head-Ω : ∀ {x₁ x₂ y₁ y₂}
  → WfCNF (bplus x₁ x₂)
  → WfCNF (bplus y₁ y₂)
  → NonBzero y₁
  → head-Ω x₁ <Ω head-Ω y₁
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
rank-mono-<ᵇ-+1-via-head-Ω
  {x₁} {x₂} {y₁} {y₂}
  wf-src
  (wf-cnf-bplus wf-y₁ _ _ _)
  nz-y₁
  strict-head
  =
  -- Step 1: rank-pow source <′ ω-rank-pow-succ (head-Ω source) =
  -- (definitionally) ω-rank-pow-succ (head-Ω x₁) by head-Ω-bplus.
  -- Concretely: `α <′ β = osuc α ≤′ β`, so the conclusion is
  -- `osuc (rank-pow (bplus x₁ x₂)) ≤′ rank-pow (bplus y₁ y₂)`.
  --
  -- The chain in `≤′` form:
  --   osuc (rank-pow (bplus x₁ x₂))
  --     ≤′ ω-rank-pow-succ (head-Ω x₁)        -- step 1 (rank-pow-dominated-...)
  --     ≤′ ω-rank-pow (head-Ω y₁)             -- step 2 (ω-rank-pow-succ-≤-via-<Ω)
  --     ≤′ rank-pow y₁                        -- step 3 (head-Ω-lower-bound)
  --     ≤′ rank-pow (bplus y₁ y₂)             -- step 4 (⊕-left-≤-sum)
  ≤′-trans
    {osuc (rank-pow (bplus x₁ x₂))}
    {ω-rank-pow (head-Ω y₁)}
    {rank-pow (bplus y₁ y₂)}
    (≤′-trans
      {osuc (rank-pow (bplus x₁ x₂))}
      {ω-rank-pow-succ (head-Ω x₁)}
      {ω-rank-pow (head-Ω y₁)}
      (rank-pow-dominated-by-head-Ω wf-src)
      (ω-rank-pow-succ-≤-via-<Ω strict-head))
    (≤′-trans
      {ω-rank-pow (head-Ω y₁)}
      {rank-pow y₁}
      {rank-pow (bplus y₁ y₂)}
      (head-Ω-lower-bound wf-y₁ nz-y₁)
      (⊕-left-≤-sum {rank-pow y₁} (rank-pow y₂)))
