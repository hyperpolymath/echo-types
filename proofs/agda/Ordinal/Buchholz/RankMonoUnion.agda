{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Union umbrella over source-rule rank-mono extensions (2026-05-30).
--
-- ## The architectural recommendation realised
--
-- PR #167's closing observation: "the future bplus-chain rank-mono
-- umbrella may want to be designed as a UNION OF SOURCE-RULE
-- EXTENSIONS (Path-3 style for cleanly-decomposable cases) rather
-- than a single enriched rank function (rank-lex-jb style for
-- cross-head cases)".
--
-- This module mechanises that pattern.  The UNION RELATION
-- `_<ᵇᵘ_` combines:
--
--   1. `_<ᵇ¹_` (Slice 3 extension, `RankMonoUmbrellaSlice3`) — 10
--      inherited K-free cases via `<ᵇ¹-from-<ᵇ⁰` + the strict-head
--      joint-bplus case `<ᵇ¹-+1-+` (`PR #142`).
--   2. `_<ᵇ⁺²_` (Path-3 extension, `RankMonoSameLeft`) — 10
--      inherited K-free cases via `<ᵇ⁺²-from-<ᵇ⁰` + the same-left
--      joint-bplus case `<ᵇ⁺²-same-left` (PR #167).
--
-- The union is the SUM of the two relations.  Rank-pow monotonicity
-- on the union dispatches by case-analysis: either the relation is
-- witnessed by the `<ᵇ¹` umbrella (which `rank-pow-mono-<ᵇ¹`
-- discharges) or by the `<ᵇ⁺²` umbrella (which `rank-pow-mono-<ᵇ⁺²`
-- discharges).  Zero new proof obligations: the union is purely
-- structural.
--
-- ## Why this architectural shape
--
-- Three observations from the Slice 3+4 Route A session arc:
--
-- 1. Different sub-cases of `<ᵇ-+1`-style joint-bplus close at
--    DIFFERENT rank-relation levels.  The strict-head case
--    (`<ᵇ¹-+1-+`) closes via head-Ω inversion + `ω-rank-pow-succ`.
--    The same-left case (`<ᵇ⁺²-same-left`) closes via
--    `rank-pow-bplus-right-mono` on the tail.  The cross-head
--    rank-equal case (`bpsi ν α` vs `bOmega ν`) closes at the
--    LEX-RANK level via `rank-lex-jb`.  Each sub-case prefers a
--    DIFFERENT rank-mono machinery.
--
-- 2. A SINGLE enriched rank function (rank-lex-jb) tries to handle
--    multiple sub-cases via a uniform second-component
--    discriminator, but the consumer-side first-eq derivation is
--    structurally simpler when the source rule itself carries the
--    enrichment (Path-3 verdict, PR #167).
--
-- 3. UNION OF EXTENSIONS scales: every new sub-case added to the
--    bplus-chain rank-mono programme can ship as a new extension
--    `_<ᵇⁿ_` with its own `rank-pow-mono-<ᵇⁿ`, then be unioned
--    in mechanically via Sum + `[_,_]`.  No interference between
--    extensions; the closure is local to each extension's
--    structural recursion.
--
-- ## What this module does NOT do
--
-- * Does NOT wrap with WfCNF endpoints (à la
--   `RankMonoUmbrellaSlice4._<ᵇ⁻ⁿ_`).  Consumers needing WfCNF
--   compose with the predicates separately, or extend this union
--   with a WfCNF-bundled variant.
-- * Does NOT include `rank-lex-jb` discharge — the cross-head
--   rank-equal case discharges at LEX-RANK level, not at rank-pow
--   level, so it lives in a different rank-relation.  The union
--   here is over `rank-pow <′` discharges only.
-- * Does NOT prove well-foundedness of the union — orthogonal to
--   rank-mono; would need a single Brouwer-rank embedding.
--   `rank-pow` provides the seed.
--
-- ## Extension recipe (for future contributors)
--
-- To add a new source-rule extension `_<ᵇⁿ_` with `rank-pow-mono-<ᵇⁿ`:
--
--   1. Define the relation + the rank-pow-mono theorem in its own
--      module (use `RankMonoSameLeft` as the canonical template).
--   2. Re-export the headlines through `Ordinal/Buchholz/Smoke.agda`
--      with their own `using` block.
--   3. Update this module to extend `_<ᵇᵘ_` with the new disjunct
--      and extend `rank-pow-mono-<ᵇᵘ` with the new case via `[_,_]`.
--      Both edits are mechanical; no new proof obligations.
--
-- The mechanical-ness of the union extension is the architectural
-- payoff: per-extension proof work + structural composition, vs
-- proof obligations multiplying as the rank function gains
-- discriminators.

module Ordinal.Buchholz.RankMonoUnion where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])

open import Ordinal.Brouwer.Phase13 using (_<′_)
open import Ordinal.Buchholz.Syntax using (BT)
open import Ordinal.Buchholz.RankPow using (rank-pow)
open import Ordinal.Buchholz.RankMonoUmbrella using (_<ᵇ⁰_)
open import Ordinal.Buchholz.RankMonoUmbrellaSlice3 using
  ( _<ᵇ¹_
  ; <ᵇ¹-from-<ᵇ⁰
  ; rank-pow-mono-<ᵇ¹
  )
open import Ordinal.Buchholz.RankMonoSameLeft using
  ( _<ᵇ⁺²_
  ; <ᵇ⁺²-from-<ᵇ⁰
  ; rank-pow-mono-<ᵇ⁺²
  )

----------------------------------------------------------------------
-- The union relation `_<ᵇᵘ_`
----------------------------------------------------------------------

-- Disjoint sum of `_<ᵇ¹_` and `_<ᵇ⁺²_`.  Either extension's witness
-- is accepted; rank-pow-mono dispatches accordingly.

_<ᵇᵘ_ : BT → BT → Set
x <ᵇᵘ y = (x <ᵇ¹ y) ⊎ (x <ᵇ⁺² y)

infix 4 _<ᵇᵘ_

----------------------------------------------------------------------
-- Rank-pow monotonicity by case analysis
----------------------------------------------------------------------

-- The union's rank-mono is the COPRODUCT MEDIATOR of the two
-- per-extension umbrellas.  Each disjunct's discharge is the
-- existing rank-mono theorem for that extension — no new proof
-- obligation.  The mediator `[_,_]` is purely structural.

rank-pow-mono-<ᵇᵘ : ∀ {x y} → x <ᵇᵘ y → rank-pow x <′ rank-pow y
rank-pow-mono-<ᵇᵘ = [ rank-pow-mono-<ᵇ¹ , rank-pow-mono-<ᵇ⁺² ]

----------------------------------------------------------------------
-- Convenience embeddings
----------------------------------------------------------------------

-- Direct embeddings from each contributing relation into the union.
-- These are `inj₁` / `inj₂` specialised, but named for readability
-- at consumer call sites.

<ᵇᵘ-from-<ᵇ¹ : ∀ {x y} → x <ᵇ¹ y → x <ᵇᵘ y
<ᵇᵘ-from-<ᵇ¹ = inj₁

<ᵇᵘ-from-<ᵇ⁺² : ∀ {x y} → x <ᵇ⁺² y → x <ᵇᵘ y
<ᵇᵘ-from-<ᵇ⁺² = inj₂

-- Transitive embedding from the 10-constructor closed umbrella
-- via either path.  The choice between `<ᵇ¹` and `<ᵇ⁺²` is
-- definitionally irrelevant for `<ᵇ⁰` derivations (both embed
-- the same witness); we choose `<ᵇ¹` as the canonical path so
-- consumers reasoning about the strict-head joint-bplus case
-- don't need to switch disjuncts mid-proof.

<ᵇᵘ-from-<ᵇ⁰ : ∀ {x y} → x <ᵇ⁰ y → x <ᵇᵘ y
<ᵇᵘ-from-<ᵇ⁰ p = <ᵇᵘ-from-<ᵇ¹ (<ᵇ¹-from-<ᵇ⁰ p)

-- Symmetric alternative: embed via `<ᵇ⁺²` instead.  Same content;
-- offered for consumer call sites where the `<ᵇ⁺²` path is
-- already in scope.

<ᵇᵘ-from-<ᵇ⁰-via-<ᵇ⁺² : ∀ {x y} → x <ᵇ⁰ y → x <ᵇᵘ y
<ᵇᵘ-from-<ᵇ⁰-via-<ᵇ⁺² p = <ᵇᵘ-from-<ᵇ⁺² (<ᵇ⁺²-from-<ᵇ⁰ p)
