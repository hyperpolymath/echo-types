{-# OPTIONS --safe --without-K #-}

-- Deliberately-narrowed `_<ᵇ⁻_` umbrella covering the
-- strict-head-closed slice (Slice 4, 2026-05-28).
--
-- ## Where this sits
--
-- `Ordinal.Buchholz.OrderRestricted._<ᵇ⁻_` is the WfCNF-restricted
-- form of `_<ᵇ_` — a record bundling source-WfCNF, target-WfCNF,
-- and an underlying `<ᵇ` derivation.  The full umbrella
-- `rank-pow-mono-<ᵇ⁻ : x <ᵇ⁻ y → rank-pow x <′ rank-pow y` over
-- all 13 `_<ᵇ_` constructors is the open Slice 4 goal in
-- `docs/echo-types/buchholz-rank-obstruction.adoc`.
--
-- Status of the per-constructor closures, post-Slice-3 (after PR
-- #141 / #142 / #143):
--
--   * 10 constructors closed under `_<ᵇ⁰_` via
--     `Ordinal.Buchholz.RankMonoUmbrella.rank-pow-mono-<ᵇ⁰`.
--   * 11th constructor (`<ᵇ-+1` joint-bplus) closed under the
--     STRICT-HEAD premise (`head-Ω x₁ <Ω head-Ω y₁`) via
--     `Ordinal.Buchholz.RankMonoUmbrellaSlice3._<ᵇ¹_` /
--     `rank-pow-mono-<ᵇ¹`.
--   * `<ᵇ-ψΩ≤` (boundary) closed AT THE LEX-RANK LEVEL via
--     `Ordinal.Buchholz.RankLex.rank-mono-<ᵇ-ψΩ≤-lex`, NOT at the
--     rank-pow level (structurally impossible per `RankAdm.agda`
--     §"<ᵇ-ψΩ≤-still-open"; only available as a lex-second-component
--     witness, not as a `_<′_` over `Ord`).
--   * `<ᵇ-+1` at `head-Ω x₁ ≡ head-Ω y₁` (the bpsi-source-at-equality
--     sub-case) GATED on the rank-lex-jb pivot (`Ordinal.Buchholz.
--     RankLexJointBplus`, PR #147 scaffold): the closure requires
--     the (a)+(b)+(c) assembly documented there.
--
-- This module ships the deliberately-narrowed umbrella covering
-- ALL CASES THAT CLOSE AT THE RANK-POW LEVEL TODAY — i.e., the
-- 10 inherited cases plus the strict-head `<ᵇ-+1` case.  The
-- two-case shortfall (`<ᵇ-ψΩ≤` and `<ᵇ-+1` at equal-head) is
-- documented in-file with explicit pointers to where each
-- shortfall closes (the lex-rank level / the rank-lex-jb pivot
-- scaffold) so future sessions can extend the umbrella without
-- re-deriving the analysis.
--
-- ## What this slice lands
--
-- 1. `_<ᵇ⁻ⁿ_` — the narrowed WfCNF-restricted relation: a record
--    bundling source-WfCNF, target-WfCNF, and an underlying
--    `_<ᵇ¹_` derivation (NOT `_<ᵇ_` — the narrowing is exactly
--    the restriction to `_<ᵇ¹_`-expressible derivations).
-- 2. `mk<ᵇ⁻ⁿ`               — record constructor.
-- 3. `<ᵇ⁻ⁿ-from-<ᵇ⁰`         — embed `_<ᵇ⁰_` derivations under
--                              WfCNF endpoints.
-- 4. `<ᵇ⁻ⁿ-+1-+`             — embed the strict-head `_<ᵇ¹_-+1-+`
--                              constructor under WfCNF endpoints.
-- 5. `rank-pow-mono-<ᵇ⁻ⁿ`    — THE NARROWED UMBRELLA.  Dispatches
--                              via `rank-pow-mono-<ᵇ¹`.
--
-- ## What this slice deliberately DOES NOT close (honest scope)
--
-- Two constructor-level shortfalls remain, BOTH documented in the
-- preamble of this module (and re-stated at the end of the file as
-- `<ᵇ⁻ⁿ-shortfall-{lex,equal-head}` matched-negative `⊤`-aliases
-- for greppability):
--
--   (i)  `<ᵇ-ψΩ≤` (boundary).  Closes at the LEX-RANK LEVEL via
--        `RankLex.rank-mono-<ᵇ-ψΩ≤-lex`; the rank-pow-level closure
--        is structurally impossible under the present rank shape
--        (see `RankAdm.agda` §"<ᵇ-ψΩ≤-still-open" for the analysis
--        + the two design follow-up options recorded there).
--   (ii) `<ᵇ-+1` at `head-Ω x₁ ≡ head-Ω y₁`.  Closes at the
--        ψ-rank level via `RankLexSlice3.rank-adm-bpsi-strict-at-
--        equality`; the bplus-chain-level extension is GATED on
--        the rank-lex-jb pivot (`RankLexJointBplus`, PR #147
--        scaffold).  The (a)+(b)+(c) assembly is the next-session
--        task per that module's preamble.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `_<ᵇ⁻ⁿ_`               — the narrowed relation
--   * `mk<ᵇ⁻ⁿ`               — record constructor
--   * `<ᵇ⁻ⁿ-from-<ᵇ⁰`        — embedding 10 inherited cases
--   * `<ᵇ⁻ⁿ-+1-+`            — embedding strict-head joint-bplus
--   * `rank-pow-mono-<ᵇ⁻ⁿ`   — THE NARROWED UMBRELLA

module Ordinal.Buchholz.RankMonoUmbrellaSlice4 where

open import Data.Unit                              using (⊤; tt)

open import Ordinal.OmegaMarkers                   using (_<Ω_)
open import Ordinal.Brouwer.Phase13                using (_<′_)
open import Ordinal.Buchholz.Syntax                using (BT; bplus)
open import Ordinal.Buchholz.WellFormedCNF         using (WfCNF)
open import Ordinal.Buchholz.HeadOmega             using (head-Ω)
open import Ordinal.Buchholz.RankPow               using (rank-pow)
open import Ordinal.Buchholz.RankPowSlice3         using (NonBzero)
open import Ordinal.Buchholz.RankMonoUmbrella      using
  ( _<ᵇ⁰_
  )
open import Ordinal.Buchholz.RankMonoUmbrellaSlice3 using
  ( _<ᵇ¹_
  ; <ᵇ¹-from-<ᵇ⁰
  ; <ᵇ¹-+1-+
  ; rank-pow-mono-<ᵇ¹
  )

----------------------------------------------------------------------
-- The narrowed relation `_<ᵇ⁻ⁿ_`
----------------------------------------------------------------------

-- Bundles WfCNF endpoints together with a `_<ᵇ¹_` derivation.  The
-- narrowing IS the restriction to `_<ᵇ¹_`-expressible derivations:
-- consumers handing a `_<ᵇ⁻_` record over have already proved both
-- endpoints WfCNF; the additional `<ᵇ¹` (vs `<ᵇ`) restriction is
-- exactly what this slice scopes itself to.
--
-- The WfCNF fields are kept even though `_<ᵇ¹_`'s `<ᵇ¹-+1-+`
-- constructor already carries them, because the inherited
-- `<ᵇ¹-from-<ᵇ⁰` constructor does NOT carry WfCNF witnesses (the
-- `_<ᵇ⁰_` relation predates the WfCNF restriction).  Bundling at
-- the record level lets consumers treat the WfCNF data uniformly
-- across both `_<ᵇ¹_` constructor cases.

record _<ᵇ⁻ⁿ_ (x y : BT) : Set where
  constructor mk<ᵇ⁻ⁿ
  field
    wf-x  : WfCNF x
    wf-y  : WfCNF y
    <ᵇ¹-d : x <ᵇ¹ y

open _<ᵇ⁻ⁿ_ public

infix 4 _<ᵇ⁻ⁿ_

----------------------------------------------------------------------
-- Constructor-level embeddings
----------------------------------------------------------------------

-- Embed any `_<ᵇ⁰_` derivation as a narrowed `_<ᵇ⁻ⁿ_` derivation,
-- once both endpoints are WfCNF.  Inherits all 10 of `_<ᵇ⁰_`'s
-- closed constructors at the narrowed level.

<ᵇ⁻ⁿ-from-<ᵇ⁰ : ∀ {x y}
  → WfCNF x → WfCNF y → x <ᵇ⁰ y → x <ᵇ⁻ⁿ y
<ᵇ⁻ⁿ-from-<ᵇ⁰ wf-x wf-y p = mk<ᵇ⁻ⁿ wf-x wf-y (<ᵇ¹-from-<ᵇ⁰ p)

-- Embed the strict-head joint-bplus case directly.  The `_<ᵇ¹_-+1-+`
-- constructor's WfCNF witnesses double as the record's `wf-x` /
-- `wf-y` here; we keep them inline so the embedding is a single
-- pass rather than requiring callers to destructure.

<ᵇ⁻ⁿ-+1-+ : ∀ {x₁ x₂ y₁ y₂}
  → (wf-src : WfCNF (bplus x₁ x₂))
  → (wf-tgt : WfCNF (bplus y₁ y₂))
  → NonBzero y₁
  → head-Ω x₁ <Ω head-Ω y₁
  → bplus x₁ x₂ <ᵇ⁻ⁿ bplus y₁ y₂
<ᵇ⁻ⁿ-+1-+ wf-src wf-tgt nz-y₁ strict-head =
  mk<ᵇ⁻ⁿ wf-src wf-tgt (<ᵇ¹-+1-+ wf-src wf-tgt nz-y₁ strict-head)

----------------------------------------------------------------------
-- THE NARROWED UMBRELLA
----------------------------------------------------------------------

-- The headline.  Forwards directly to `rank-pow-mono-<ᵇ¹` via the
-- bundled `<ᵇ¹` derivation.  The WfCNF fields are unused inside
-- the proof but available to consumers reasoning about the
-- endpoints.

rank-pow-mono-<ᵇ⁻ⁿ : ∀ {x y} → x <ᵇ⁻ⁿ y → rank-pow x <′ rank-pow y
rank-pow-mono-<ᵇ⁻ⁿ {x} {y} p = rank-pow-mono-<ᵇ¹ (<ᵇ¹-d p)

----------------------------------------------------------------------
-- Matched-negative shortfall markers (greppable)
----------------------------------------------------------------------

-- Pin the two `_<ᵇ_`-constructor-level shortfalls as `⊤`-aliases
-- so `grep <ᵇ⁻ⁿ-shortfall` discovers them.  Each name includes a
-- block comment pointing at exactly where the closure lives in the
-- repo (when one exists at a non-`rank-pow` level) or what would
-- unblock it.

-- `<ᵇ-ψΩ≤` shortfall.  Closes at the LEX-RANK LEVEL via
-- `Ordinal.Buchholz.RankLex.rank-mono-<ᵇ-ψΩ≤-lex`; the rank-pow
-- level is structurally impossible per `RankAdm.agda`
-- §"<ᵇ-ψΩ≤-still-open" — `ω-rank-pow ν ⊕ rank-pow α <′ ω-rank-pow ν`
-- would force the absurd `ω-rank-pow ν <′ ω-rank-pow ν` via
-- `⊕-left-≤-sum`.  Consumers at the rank-pow level cannot dispatch
-- this case; they must lift to the lex rank.

<ᵇ⁻ⁿ-shortfall-lex : ⊤
<ᵇ⁻ⁿ-shortfall-lex = tt

-- `<ᵇ-+1` at `head-Ω x₁ ≡ head-Ω y₁` shortfall.  Closes at the
-- ψ-rank level via `Ordinal.Buchholz.RankLexSlice3.rank-adm-bpsi-
-- strict-at-equality`; the bplus-chain-level extension is GATED on
-- the rank-lex-jb pivot scaffolded by
-- `Ordinal.Buchholz.RankLexJointBplus` (PR #147).  The (a)+(b)+(c)
-- assembly documented in that module's preamble is the multi-PR
-- closure path.

<ᵇ⁻ⁿ-shortfall-equal-head : ⊤
<ᵇ⁻ⁿ-shortfall-equal-head = tt
