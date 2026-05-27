{-# OPTIONS --safe --without-K #-}

-- Admissibility-aware rank for Buchholz terms (Lane 3 active-push
-- slice, 2026-05-26).
--
-- ## Where this sits
--
-- `Ordinal.Buchholz.RankPow.rank-pow` uses the provisional shape
-- `rank-pow (bpsi ν _) = ω-rank-pow ν`, which is α-blind and so
-- cannot discriminate the shared-Ω-index lex constructor
-- `<ᵇ⁺-ψα : ν₁ ≡ ν₂ → α <ᵇ β → bpsi ν₁ α <ᵇ⁺ bpsi ν₂ β` of
-- `Ordinal.Buchholz.OrderExtended._<ᵇ⁺_`.  Two of the three open
-- constructor cases in `docs/echo-types/buchholz-rank-obstruction.adoc`
-- (`<ᵇ⁺-ψα`, `<ᵇ-ψΩ≤`) are flagged there as needing a ψ-admissibility
-- rank refinement; `WellFormedAdmissible.agda` landed the carrier
-- (`WfAdm` + the rank-bound on the `bpsi` constructor); this module
-- lands the refined rank itself and discharges the `<ᵇ⁺-ψα` half of
-- the two-case unblock.
--
-- ## What this slice closes
--
-- 1. `rank-adm : BT → Ord`, an α-discriminating rank that diverges
--    from `rank-pow` only on the `bpsi` case:
--    `rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α`.
-- 2. `rank-pow≤rank-adm : ∀ t → rank-pow t ≤′ rank-adm t` — the new
--    rank dominates the provisional one, so the existing 10-case
--    `_<ᵇ⁰_` umbrella's rank-mono lifts to `rank-adm` consumers via
--    monotonicity (caller composes).
-- 3. `rank-mono-<ᵇ⁺-ψα-from-pow` — the headline primitive: from a
--    `rank-pow α <′ rank-pow β` hypothesis (which the existing
--    umbrella `rank-pow-mono-<ᵇ⁰` discharges for any
--    `<ᵇ⁰`-derivable `α <ᵇ⁰ β`), produces
--    `rank-adm (bpsi ν α) <′ rank-adm (bpsi ν β)`.
-- 4. `rank-adm-bpsi-bounded-under-adm` — the admissibility-source-
--    bound lemma referenced in CLAUDE.md.  Under `WfAdm (bpsi ν α)`,
--    `rank-adm (bpsi ν α) <′ ω-rank-pow (suc-Ω ν)` where
--    `suc-Ω ν` is the syntactic next-Ω-marker, via the
--    additive-principal closure of `ω-rank-pow ν`.  Documented;
--    full statement TBD pending a `suc-Ω` operation on the open
--    `OmegaIndex` set.
--
-- ## What this slice deliberately does NOT close
--
-- * `<ᵇ-ψΩ≤` at ν = μ.  The classical Buchholz semantics has
--   ψ_μ(α) < Ω_μ under admissibility (this is what admissibility
--   *means*).  Under the present syntactic-rank encoding
--   `ω-rank-pow ν` ↔ Ω_ν and `rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α`,
--   we would need `ω-rank-pow ν ⊕ rank-pow α <′ ω-rank-pow ν`,
--   which is impossible because `ω-rank-pow ν ≤′ ω-rank-pow ν ⊕ rank-pow α`
--   by `⊕-left-≤-sum`.  This is a classical-vs-syntactic encoding
--   mismatch surfaced by the slice: the next-Ω-marker gap that
--   classical admissibility lives inside is *not modelled* by the
--   present rank.  Closure requires either a two-component lex
--   rank (`(ω-rank-pow ν, rank-pow α)` with lex order) or a richer
--   target encoding `ω-rank-pow ν · ω + rank-pow α`.  Recorded as
--   a design follow-up in `docs/echo-types/buchholz-rank-obstruction.adoc`
--   and pinned in this module's `<ᵇ-ψΩ≤-still-open` comment block
--   below so the next session sees the constraint without re-deriving
--   it.
-- * `<ᵇ-+1` joint-bplus.  Unchanged from `RankPow.agda`'s deferral
--   — this slice is ψ-side only.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `rank-adm`                          -- the admissibility-aware rank
--   * `rank-adm-bzero`, `rank-adm-bOmega`,
--     `rank-adm-bplus`, `rank-adm-bpsi`   -- definitional sanity
--   * `rank-pow≤rank-adm`                 -- new dominates provisional
--   * `rank-mono-<ᵇ⁺-ψα-from-pow`         -- the slice's headline primitive
--   * `rank-adm-pos-bpsi`                 -- positivity at the bpsi case

module Ordinal.Buchholz.RankAdm where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers      using (OmegaIndex)
open import Ordinal.Brouwer           using (Ord; oz; osuc)
open import Ordinal.Brouwer.Arithmetic using (_⊕_)
open import Ordinal.Brouwer.Phase13    using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-trans
  ; ⊕-mono-<-right
  ; ⊕-mono-≤-left
  ; ⊕-mono-≤-right
  ; ⊕-left-≤-sum
  )
open import Ordinal.Buchholz.Syntax    using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.RankPow   using
  ( rank-pow
  ; ω-rank-pow
  ; ω-rank-pow-pos
  )

----------------------------------------------------------------------
-- The admissibility-aware rank
----------------------------------------------------------------------

-- Diverges from `rank-pow` only on `bpsi`: the α-tail contributes
-- to the rank, so the shared-Ω-index lex case `<ᵇ⁺-ψα` is no longer
-- collapsed to a same-rank pair.

rank-adm : BT → Ord
rank-adm bzero        = oz
rank-adm (bOmega ν)   = ω-rank-pow ν
rank-adm (bplus x y)  = rank-adm x ⊕ rank-adm y
rank-adm (bpsi ν α)   = ω-rank-pow ν ⊕ rank-pow α
  -- The α-tail uses `rank-pow`, not `rank-adm`, deliberately:
  -- the existing umbrella `rank-pow-mono-<ᵇ⁰` discharges rank-pow
  -- comparisons on the inner α; lifting the tail to `rank-adm`
  -- would require a recursive primitive we have not yet proved.
  -- See `<ᵇ-ψΩ≤-still-open` for the design constraint that fixes
  -- this choice.

----------------------------------------------------------------------
-- Definitional sanity
----------------------------------------------------------------------

rank-adm-bzero  : rank-adm bzero ≡ oz
rank-adm-bzero = refl

rank-adm-bOmega : ∀ ν → rank-adm (bOmega ν) ≡ ω-rank-pow ν
rank-adm-bOmega _ = refl

rank-adm-bplus  : ∀ x y → rank-adm (bplus x y) ≡ rank-adm x ⊕ rank-adm y
rank-adm-bplus _ _ = refl

rank-adm-bpsi   : ∀ ν α → rank-adm (bpsi ν α) ≡ ω-rank-pow ν ⊕ rank-pow α
rank-adm-bpsi _ _ = refl

----------------------------------------------------------------------
-- Positivity at the bpsi case
----------------------------------------------------------------------

-- `oz <′ rank-adm (bpsi ν α)`.  Useful for the `<ᵇ-0-ψ`
-- rank-mono case under `rank-adm` consumers (which the existing
-- `rank-mono-<ᵇ-0-ψ : oz <′ rank-pow (bpsi ν α) = ω-rank-pow ν`
-- discharges only for the rank-pow consumer).

rank-adm-pos-bpsi : ∀ {ν α} → oz <′ rank-adm (bpsi ν α)
rank-adm-pos-bpsi {ν} {α} =
  -- rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α; first summand
  -- is strictly positive by ω-rank-pow-pos, and ⊕-left-≤-sum makes
  -- the whole sum dominate.
  let
    pos-left : oz <′ ω-rank-pow ν
    pos-left = ω-rank-pow-pos ν
    left≤sum : ω-rank-pow ν ≤′ ω-rank-pow ν ⊕ rank-pow α
    left≤sum = ⊕-left-≤-sum {ω-rank-pow ν} (rank-pow α)
  in
    ≤′-trans
      {osuc oz} {ω-rank-pow ν} {ω-rank-pow ν ⊕ rank-pow α}
      pos-left
      left≤sum

----------------------------------------------------------------------
-- `rank-pow ≤′ rank-adm` (dominance)
----------------------------------------------------------------------

-- The admissibility-aware rank dominates the provisional one
-- pointwise.  Used by callers that have a `rank-pow` strict-mono
-- conclusion in hand and want to lift it to `rank-adm`.

rank-pow≤rank-adm : ∀ t → rank-pow t ≤′ rank-adm t
rank-pow≤rank-adm bzero        = ≤′-refl {oz}
rank-pow≤rank-adm (bOmega ν)   = ≤′-refl {ω-rank-pow ν}
rank-pow≤rank-adm (bpsi ν α)   =
  -- rank-pow (bpsi ν α) = ω-rank-pow ν;
  -- rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α.
  -- The left summand is ≤ the sum.
  ⊕-left-≤-sum {ω-rank-pow ν} (rank-pow α)
rank-pow≤rank-adm (bplus x y)  =
  -- rank-pow (bplus x y) = rank-pow x ⊕ rank-pow y;
  -- rank-adm (bplus x y) = rank-adm x ⊕ rank-adm y.
  -- Compose left-mono with right-mono via transitivity through the
  -- intermediate `rank-adm x ⊕ rank-pow y`:
  --   rank-pow x ⊕ rank-pow y
  --   ≤′ rank-adm x ⊕ rank-pow y        (⊕-mono-≤-left  on rank-pow≤rank-adm x)
  --   ≤′ rank-adm x ⊕ rank-adm y        (⊕-mono-≤-right on rank-pow≤rank-adm y)
  ≤′-trans
    {rank-pow x ⊕ rank-pow y}
    {rank-adm x ⊕ rank-pow y}
    {rank-adm x ⊕ rank-adm y}
    (⊕-mono-≤-left  {rank-pow x} {rank-adm x} {rank-pow y}
       (rank-pow≤rank-adm x))
    (⊕-mono-≤-right {rank-adm x} {rank-pow y} {rank-adm y}
       (rank-pow≤rank-adm y))

----------------------------------------------------------------------
-- Headline primitive: `<ᵇ⁺-ψα` rank-mono under `rank-adm`
----------------------------------------------------------------------

-- Given a `rank-pow α <′ rank-pow β` hypothesis (produced by the
-- existing umbrella for any `α <ᵇ⁰ β` per
-- `Ordinal.Buchholz.RankMonoUmbrella.rank-pow-mono-<ᵇ⁰`), conclude
-- `rank-adm (bpsi ν α) <′ rank-adm (bpsi ν β)`.
--
-- This is the slice's load-bearing addition: it discharges the
-- *first* of the two ψ-admissibility-blocked constructor cases
-- (`<ᵇ⁺-ψα`).  See `<ᵇ-ψΩ≤-still-open` comment block below for the
-- structural reason the *second* case (`<ᵇ-ψΩ≤`) does not close
-- under this rank shape.

rank-mono-<ᵇ⁺-ψα-from-pow : ∀ {ν α β}
  → rank-pow α <′ rank-pow β
  → rank-adm (bpsi ν α) <′ rank-adm (bpsi ν β)
rank-mono-<ᵇ⁺-ψα-from-pow {ν} {α} {β} p =
  -- rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α;
  -- rank-adm (bpsi ν β) = ω-rank-pow ν ⊕ rank-pow β.
  -- Pure right-strict-mono of `_⊕_` against the hypothesis.
  ⊕-mono-<-right {ω-rank-pow ν} {rank-pow α} {rank-pow β} p

----------------------------------------------------------------------
-- `<ᵇ-ψΩ≤-still-open` — the design constraint this slice surfaces
----------------------------------------------------------------------

-- `<ᵇ-ψΩ≤ : ν ≤Ω μ → bpsi ν α <ᵇ bOmega μ` ranges over ν ≤Ω μ,
-- INCLUDING the boundary case ν = μ.  Under admissibility,
-- `rank-pow α <′ ω-rank-pow ν` holds (`WfAdm` predicate's
-- `bpsi`-constructor rank bound).
--
-- Under `rank-adm`:
--   rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α
--   rank-adm (bOmega μ) = ω-rank-pow μ
--
-- Case `ν <Ω μ` (strict).  Both summands are strictly below
-- `ω-rank-pow μ` (rank-pow α via admissibility + transit through
-- `ω-rank-pow ν <′ ω-rank-pow μ`; `ω-rank-pow ν` directly via
-- `ω-rank-pow-mono`).  `additive-principal-ω-rank-pow {μ}` closes.
-- This case is straightforward and the follow-on slice will land it.
--
-- Case `ν = μ` (boundary).  Need
--   `ω-rank-pow μ ⊕ rank-pow α <′ ω-rank-pow μ`,
-- but `ω-rank-pow μ ≤′ ω-rank-pow μ ⊕ rank-pow α` always (left-≤-sum),
-- so a strict `<′ ω-rank-pow μ` conclusion forces the absurd
-- `ω-rank-pow μ <′ ω-rank-pow μ`.  Impossible under this rank shape.
--
-- The classical reading: ψ_μ(α) for admissible α lives in the gap
--   [ω-rank-pow μ, ω-rank-pow (μ+1))
-- (it is a countable ordinal below the next cardinal threshold).
-- The present rank `ω-rank-pow ν ⊕ rank-pow α` collapses that gap;
-- the constraint `α <′ ω-rank-pow ν` does not buy `<′ ω-rank-pow ν`
-- for the sum, only for the right summand.
--
-- Design follow-ups (not landed in this slice):
--
--   (A) Two-component lex rank.  `rank-lex : BT → Ord × Ord`
--       comparing first lex-by-`<′`-then-`≤′` on the second.  The
--       ψ-case is `(ω-rank-pow ν, rank-pow α)`, the Ω-case is
--       `(ω-rank-pow μ, oz)`.  Closes `<ᵇ-ψΩ≤` cleanly (when
--       `ν = μ`, first components are equal and admissibility's
--       `rank-pow α <′ ω-rank-pow ν` on the second component
--       carries the strict-less-than).  Cost: every existing
--       rank-mono primitive in `RankPow` needs a lex re-statement.
--
--   (B) Successor-multiplied rank.  Define a `_·ω_` operation on
--       `Ord` and set `rank-adm (bpsi ν α) = ω-rank-pow ν ·ω + rank-pow α`
--       so the ψ-rank lives strictly between two consecutive
--       Ω-ranks.  Cost: a multiplicative ordinal-arithmetic layer
--       beyond what `Ordinal.Brouwer.Arithmetic` currently ships;
--       `(·ω)`'s monotonicity lemmas would be a separate
--       sub-slice's worth of work.
--
--   (C) Stratify `_<ᵇ_` into a ν-respecting equivalence and use
--       a per-ν rank.  Heaviest re-architecture; mentioned for
--       completeness only.
--
-- Recommendation for the follow-on slice: option (A).  It reuses
-- the existing `RankPow` primitives verbatim on the first
-- component and the existing scalar `<′` / `≤′` infrastructure on
-- the second; the lex order propagates cleanly to a new umbrella.
-- Option (B) is ordinally cleaner but ships a new arithmetic
-- layer.
