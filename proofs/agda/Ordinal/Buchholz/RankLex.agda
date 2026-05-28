{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Lex-pair rank for Buchholz terms (Lane 3 follow-on slice, 2026-05-27).
--
-- ## Where this sits
--
-- `Ordinal.Buchholz.RankAdm.rank-adm` discharged the `<ᵇ⁺-ψα`
-- (shared-Ω-index lex) constructor by shifting the ψ-rank from
-- `ω-rank-pow ν` (α-blind) to `ω-rank-pow ν ⊕ rank-pow α`
-- (α-discriminating).  That fixed `<ᵇ⁺-ψα` cleanly, but it surfaced
-- a new gap: the `<ᵇ-ψΩ≤` constructor at the ν = μ boundary case is
-- *structurally impossible* under any scalar `Ord`-valued rank with
-- `ω-rank-pow ν ≤ rank-adm (bpsi ν α)` — that monotonicity forces
-- the goal `rank-adm (bpsi ν α) <′ ω-rank-pow ν` to imply the absurd
-- `ω-rank-pow ν <′ ω-rank-pow ν` (see `RankAdm.agda`
-- §"<ᵇ-ψΩ≤-still-open" for the full diagnostic).
--
-- The recommended follow-up there was option (A): a two-component
-- lex rank.  This module lands it as a *thin* slice: the lex pair
-- exists alongside `rank-pow` and `rank-adm`, only for the headline
-- `<ᵇ-ψΩ≤` close-out.  The existing 10 + 1 = 11 closed cases
-- continue to consume the scalar `rank-pow` / `rank-adm` infrastructure
-- unchanged.
--
-- ## What this slice closes
--
-- 1. `RankLex` record with two `Ord` fields (`first`, `second`).
-- 2. `_<lex_` strict order: lex on first, fall through to second on
--    *syntactic* first-component equality (the second-strict
--    constructor pattern-matches the same implicit `a` on both
--    sides, so equality is by unification, not propositional).
-- 3. `rank-lex : BT → RankLex`:
--      bzero         ↦ mkLex oz             oz
--      bOmega ν      ↦ mkLex (ω-rank-pow ν) (ω-rank-pow ν)
--      bpsi   ν α    ↦ mkLex (ω-rank-pow ν) (rank-pow α)
--      bplus  x y    ↦ mkLex (rank-pow (bplus x y)) oz
--    The `bOmega ν` second-component placeholder is `ω-rank-pow ν`
--    itself — large enough to dominate any admissible `rank-pow α`
--    bound by `<′ ω-rank-pow ν`.
-- 4. `rank-mono-<ᵇ-ψΩ≤-lex` — the headline.  Both the ν <Ω μ strict
--    case (closes via `<lex-first` + `ω-rank-pow-mono`) and the
--    ν = μ boundary case (closes via `<lex-second` + the
--    admissibility bound `rank-pow α <′ ω-rank-pow ν`).
--
-- ## What this slice deliberately does NOT close
--
-- * `<ᵇ-+1` joint-bplus.  Unchanged from `RankAdm.agda` / `RankPow.agda`
--   deferral — needs a coarser dominator (leading-Ω-index) or a
--   richer rank shape on `bplus`.  See `RankPow.agda` and
--   `docs/echo-types/buchholz-rank-obstruction.adoc`.
-- * Full `rank-lex-mono-<ᵇ⁻` umbrella.  The 11 existing constructor
--   primitives in `RankPow` / `RankAdm` are scalar; lifting them to
--   the lex form would require re-stating each (per design note A in
--   `RankAdm.agda`).  This slice ships ONLY the headline lex-mono
--   for the boundary-case constructor; the umbrella will compose
--   `rank-pow-mono-<ᵇ⁰` (10 cases) + `rank-mono-<ᵇ⁺-ψα-from-pow`
--   (`<ᵇ⁺-ψα` via `rank-adm`) + this slice's
--   `rank-mono-<ᵇ-ψΩ≤-lex` (`<ᵇ-ψΩ≤`) under a single dispatch.
--   Deferred to the consumer-side umbrella refresh.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `RankLex` / `mkLex`                -- the carrier
--   * `_<lex_` / `<lex-first` / `<lex-second`  -- the strict order
--   * `rank-lex`                         -- the lex rank
--   * `rank-lex-bzero`, `rank-lex-bOmega`,
--     `rank-lex-bplus`, `rank-lex-bpsi`  -- definitional sanity
--   * `rank-mono-<ᵇ-ψΩ≤-lex`             -- the slice's headline

module Ordinal.Buchholz.RankLex where

open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers      using
  ( OmegaIndex
  ; _≤Ω_
  ; _<Ω_
  ; ≤Ω-split
  )
open import Ordinal.Brouwer           using (Ord; oz; osuc)
open import Ordinal.Brouwer.Phase13   using (_<′_; _≤′_)
open import Ordinal.Buchholz.Syntax   using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.RankPow  using
  ( rank-pow
  ; ω-rank-pow
  ; ω-rank-pow-mono
  )

----------------------------------------------------------------------
-- The lex-pair carrier
----------------------------------------------------------------------

record RankLex : Set where
  constructor mkLex
  field
    first  : Ord
    second : Ord

open RankLex public

----------------------------------------------------------------------
-- Lex strict order
----------------------------------------------------------------------

-- Two constructors.  `<lex-first` covers the strict-on-first case.
-- `<lex-second` covers the same-first-strict-on-second case; the
-- shared implicit `a` on both sides makes the equality syntactic,
-- so callers do not need to thread an `_≡_` witness.

data _<lex_ : RankLex → RankLex → Set where
  <lex-first  : ∀ {a₁ a₂ b₁ b₂}
              → a₁ <′ a₂
              → mkLex a₁ b₁ <lex mkLex a₂ b₂
  <lex-second : ∀ {a b₁ b₂}
              → b₁ <′ b₂
              → mkLex a b₁ <lex mkLex a b₂

infix 4 _<lex_

----------------------------------------------------------------------
-- The lex rank
----------------------------------------------------------------------

-- Diverges from `rank-pow` and `rank-adm` only in how it records
-- the boundary information.  For `bOmega ν` the second-component
-- placeholder is `ω-rank-pow ν` itself — large enough to dominate
-- any admissible `rank-pow α` (which the admissibility predicate
-- bounds by `<′ ω-rank-pow ν`).

rank-lex : BT → RankLex
rank-lex bzero       = mkLex oz                       oz
rank-lex (bOmega ν)  = mkLex (ω-rank-pow ν)           (ω-rank-pow ν)
rank-lex (bpsi ν α)  = mkLex (ω-rank-pow ν)           (rank-pow α)
rank-lex (bplus x y) = mkLex (rank-pow (bplus x y))   oz
  -- The `bplus` case uses scalar `rank-pow` on the first component
  -- and `oz` on the second; we have no lex headline that fires on
  -- the `bplus` constructor in this slice (the `<ᵇ-+1` joint-bplus
  -- gap is unchanged).  Consumers wanting a lex bplus-mono primitive
  -- would extend this case to `mkLex (rank-pow (bplus x y)) (...)`
  -- with their chosen second-component bound.

----------------------------------------------------------------------
-- Definitional sanity
----------------------------------------------------------------------

rank-lex-bzero  : rank-lex bzero ≡ mkLex oz oz
rank-lex-bzero = refl

rank-lex-bOmega : ∀ ν → rank-lex (bOmega ν) ≡ mkLex (ω-rank-pow ν) (ω-rank-pow ν)
rank-lex-bOmega _ = refl

rank-lex-bpsi   : ∀ ν α → rank-lex (bpsi ν α) ≡ mkLex (ω-rank-pow ν) (rank-pow α)
rank-lex-bpsi _ _ = refl

rank-lex-bplus  : ∀ x y → rank-lex (bplus x y) ≡ mkLex (rank-pow (bplus x y)) oz
rank-lex-bplus _ _ = refl

----------------------------------------------------------------------
-- Headline: `<ᵇ-ψΩ≤` rank-mono under `rank-lex`
----------------------------------------------------------------------

-- The boundary-case constructor.  Hypotheses are exactly what
-- `<ᵇ-ψΩ≤` carries (`ν ≤Ω μ`) plus the admissibility predicate's
-- rank bound on ψ-arguments (`rank-pow α <′ ω-rank-pow ν`, which
-- `WfAdm (bpsi ν α)` supplies via its `wf-adm-bpsi` constructor).
--
-- Both sub-cases close:
--   * `inj₁ ν<μ`  — strict on first component via `ω-rank-pow-mono`.
--   * `inj₂ refl` — ν = μ; first components are syntactically equal,
--     so `<lex-second` fires with the admissibility bound on the
--     second component.

rank-mono-<ᵇ-ψΩ≤-lex : ∀ {ν μ α}
  → ν ≤Ω μ
  → rank-pow α <′ ω-rank-pow ν
  → rank-lex (bpsi ν α) <lex rank-lex (bOmega μ)
rank-mono-<ᵇ-ψΩ≤-lex {ν} {μ} {α} ν≤μ adm with ≤Ω-split ν≤μ
... | inj₁ ν<μ  = <lex-first  (ω-rank-pow-mono ν<μ)
... | inj₂ refl = <lex-second adm
