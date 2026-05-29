{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- The Slice-3 extension of the rank-soundness-ready umbrella.
--
-- `Ordinal.Buchholz.RankMonoUmbrella._<ᵇ⁰_` closes 10 of the 13
-- constructors of `Ordinal.Buchholz.Order._<ᵇ_` via direct structural
-- recursion.  The bplus-target joint-bplus case (where the target's
-- left summand is itself a `bplus`, NOT atomic — i.e., `<ᵇ-+1` with
-- both `x₁` and `y₁` being `bplus`) is excluded from `_<ᵇ⁰_`
-- because the `<ᵇ⁰-+1-Ω` / `<ᵇ⁰-+1-ψ` constructors restrict the
-- target's left summand to be `bOmega μ` / `bpsi ν α`.
--
-- This slice extends the umbrella with a NEW joint-bplus constructor
-- `<ᵇ¹-+1-+` and dispatches it via the Slice 3 headline
-- `rank-mono-<ᵇ-+1-via-head-Ω` from `Ordinal.Buchholz.RankPowSlice3Headline`.
-- That headline closes the bplus-target case UNDER A STRICT-HEAD
-- PREMISE `head-Ω x₁ <Ω head-Ω y₁`.  The new constructor bakes the
-- premise (together with the required WfCNF / NonBzero side
-- conditions) in.
--
-- ## What's in / what's out
--
-- IN (11 = 10 inherited + 1 new):
--
--   * `<ᵇ¹-from-<ᵇ⁰` — embedding of every `_<ᵇ⁰_` derivation as a
--     `_<ᵇ¹_` derivation (single constructor; the umbrella below
--     dispatches via `rank-pow-mono-<ᵇ⁰` directly).
--   * `<ᵇ¹-+1-+` — the new joint-bplus constructor: requires
--     `WfCNF (bplus x₁ x₂)`, `WfCNF (bplus y₁ y₂)`, `NonBzero y₁`,
--     and the strict-head premise `head-Ω x₁ <Ω head-Ω y₁`.
--
-- OUT (deliberately deferred, see "Equality sub-case" below):
--
--   * Joint-bplus at `head-Ω x₁ ≡ head-Ω y₁` — the bpsi-source-at-
--     equality sub-case where x₁'s leading marker matches y₁'s.
--     The Slice 3 headline cannot fire (it needs strict `<Ω`); a
--     rank-adm / rank-lex combination would close it but no such
--     primitive currently exists for `<ᵇ-+1` (`rank-lex` only
--     discharges `<ᵇ-ψΩ≤`).  When that primitive lands, add a
--     second constructor (e.g., `<ᵇ¹-+1-+-eq`) carrying the rank-lex
--     witness and extend `rank-pow-mono-<ᵇ¹` to dispatch on it.
--
-- ## Why a thin embedding constructor
--
-- The natural shape would inline all 10 constructors of `_<ᵇ⁰_` into
-- `_<ᵇ¹_`.  That would duplicate `_<ᵇ⁰_`'s definition and force the
-- umbrella's structural recursion to redo the dispatch for every
-- inherited case.  Embedding via `<ᵇ¹-from-<ᵇ⁰` keeps `_<ᵇ¹_`
-- minimal (two constructors), preserves the existing umbrella as the
-- inherited workhorse, and adds the new case as a single targeted
-- extension.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `_<ᵇ¹_`                    -- the extended relation
--   * `<ᵇ¹-from-<ᵇ⁰`             -- the embedding constructor
--   * `<ᵇ¹-+1-+`                 -- the new joint-bplus constructor
--   * `rank-pow-mono-<ᵇ¹`        -- THE UMBRELLA (strict)

module Ordinal.Buchholz.RankMonoUmbrellaSlice3 where

open import Ordinal.OmegaMarkers                  using (_<Ω_)
open import Ordinal.Buchholz.Syntax               using (BT; bplus)
open import Ordinal.Buchholz.WellFormedCNF        using (WfCNF)
open import Ordinal.Buchholz.HeadOmega            using (head-Ω)
open import Ordinal.Buchholz.RankPow              using (rank-pow)
open import Ordinal.Brouwer.Phase13               using (_<′_)
open import Ordinal.Buchholz.RankPowSlice3        using (NonBzero)
open import Ordinal.Buchholz.RankPowSlice3Headline using
  ( rank-mono-<ᵇ-+1-via-head-Ω
  )
open import Ordinal.Buchholz.RankMonoUmbrella     using
  ( _<ᵇ⁰_
  ; rank-pow-mono-<ᵇ⁰
  )

----------------------------------------------------------------------
-- The extended relation `_<ᵇ¹_`
----------------------------------------------------------------------

-- Two constructors:
--
--   1. `<ᵇ¹-from-<ᵇ⁰` — every `_<ᵇ⁰_` derivation is a `_<ᵇ¹_`
--      derivation.  Inherits all 10 closed constructors of `_<ᵇ⁰_`
--      without duplication.
--   2. `<ᵇ¹-+1-+` — the new joint-bplus case with target's left
--      summand itself a `bplus`.  Carries the strict-head premise
--      and WfCNF / NonBzero side conditions required by the
--      Slice 3 headline.

data _<ᵇ¹_ : BT → BT → Set where
  <ᵇ¹-from-<ᵇ⁰ : ∀ {x y} → x <ᵇ⁰ y → x <ᵇ¹ y

  <ᵇ¹-+1-+ : ∀ {x₁ x₂ y₁ y₂}
    → WfCNF (bplus x₁ x₂)
    → WfCNF (bplus y₁ y₂)
    → NonBzero y₁
    → head-Ω x₁ <Ω head-Ω y₁
    → bplus x₁ x₂ <ᵇ¹ bplus y₁ y₂

infix 4 _<ᵇ¹_

----------------------------------------------------------------------
-- The extended umbrella theorem
----------------------------------------------------------------------

-- Direct structural recursion on `_<ᵇ¹_`.  The inherited case
-- forwards to `rank-pow-mono-<ᵇ⁰`; the new joint-bplus case forwards
-- to the Slice 3 headline `rank-mono-<ᵇ-+1-via-head-Ω`.

rank-pow-mono-<ᵇ¹ : ∀ {x y} → x <ᵇ¹ y → rank-pow x <′ rank-pow y
rank-pow-mono-<ᵇ¹ (<ᵇ¹-from-<ᵇ⁰ p)              = rank-pow-mono-<ᵇ⁰ p
rank-pow-mono-<ᵇ¹ (<ᵇ¹-+1-+ wf-src wf-tgt nz-y₁ strict-head) =
  rank-mono-<ᵇ-+1-via-head-Ω wf-src wf-tgt nz-y₁ strict-head
