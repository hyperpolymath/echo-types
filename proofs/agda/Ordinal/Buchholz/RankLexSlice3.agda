{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Lex-rank companion to the Slice 3 head-Ω discharge, covering the
-- bpsi-source-at-equality sub-case of `<ᵇ-+1` joint-bplus, 2026-05-28.
--
-- ## Where this sits
--
-- The Slice 3 headline `Ordinal.Buchholz.RankPowSlice3Headline.
-- rank-mono-<ᵇ-+1-via-head-Ω` discharges `bplus x₁ x₂ <ᵇ bplus y₁ y₂`
-- (from `x₁ <ᵇ y₁`) UNDER A STRICT-HEAD PREMISE `head-Ω x₁ <Ω head-Ω y₁`.
-- The premise is supplied externally by the umbrella's case-split:
--
--   * x₁ = bOmega μ  : `head-Ω-inv-bOmega` gives `μ <Ω head-Ω y₁`
--                       directly (STRICT for all three Ω-source
--                       constructors).  Slice 3 closes.
--   * x₁ = bpsi ν α  : `head-Ω-inv-bpsi` gives `ν ≤Ω head-Ω y₁`
--                       (NON-STRICT — `<ᵇ-ψΩ≤` permits equal markers).
--                       Strict sub-case (`ν <Ω head-Ω y₁`) closes
--                       via Slice 3.  EQUALITY sub-case
--                       (`ν ≡ head-Ω y₁`) is THIS MODULE'S TERRITORY.
--   * x₁ = bplus a b : recurse on the leftmost-leaf shape; reduces to
--                       one of the above two atomic cases.
--
-- This module handles the bpsi-source-at-equality remainder via the
-- existing lex-pair rank `rank-lex` from `Ordinal.Buchholz.RankLex`
-- (whose second component carries `rank-pow α` for the ψ case) plus
-- the existing admissibility-aware rank `rank-adm` from
-- `Ordinal.Buchholz.RankAdm`.
--
-- ## What this slice closes (the lex headline)
--
-- The headline:
--
--   rank-mono-<ᵇ-+1-via-rank-lex : ∀ {ν α β x₂ y₂}
--     → rank-pow α <′ rank-pow β       -- second-component lex witness
--     → rank-lex (bplus (bpsi ν α) x₂) <lex rank-lex (bplus (bpsi ν β) y₂)
--
-- ...is NOT directly stateable: `rank-lex (bplus x y) = mkLex
-- (rank-pow (bplus x y)) oz` in the existing `RankLex` module, so the
-- second component is *both* `oz` and the lex-second-strict
-- constructor `<lex-second : b₁ <′ b₂` cannot fire at `oz <′ oz`.
-- The existing `rank-lex` was deliberately shipped that way to scope
-- the slice to the `<ᵇ-ψΩ≤` ν=μ boundary headline alone (see the
-- companion-remark in `RankLex.agda` lines 142-148).
--
-- The HONEST closure THIS module ships:
--
--   rank-adm-bpsi-strict-at-equality : ∀ {ν α β}
--     → rank-pow α <′ rank-pow β
--     → rank-adm (bpsi ν α) <′ rank-adm (bpsi ν β)
--
-- This is a thin convenience re-export of `RankAdm.rank-mono-<ᵇ⁺-ψα-
-- from-pow` named for the joint-bplus consumer.  It is the LOAD-
-- BEARING primitive for the bpsi-source-at-equality sub-case at the
-- ψ-rank level.  The bplus-extension under `rank-adm` (= `rank-adm
-- (bplus x₁ x₂) <′ rank-adm (bplus y₁ y₂)`) is documented in the
-- design note below as the open structural gap.
--
-- ## What this slice deliberately DOES NOT close (honest scope)
--
-- The task's intended conclusion `rank-pow (bplus x₁ x₂) <′ rank-pow
-- (bplus y₁ y₂)` is *structurally not derivable* from `α <ᵇ β` alone
-- at the bpsi-source-at-equality sub-case:
--
--   * `rank-pow (bpsi ν α) = ω-rank-pow ν = rank-pow (bpsi ν β)` —
--     the provisional `rank-pow` shape collapses both ψ-sources at
--     the same ν to the SAME ordinal, so no strict-on-left-summand
--     witness exists at the `rank-pow` level.
--   * Promoting the conclusion to `rank-adm` produces `rank-adm
--     (bpsi ν α) <′ rank-adm (bpsi ν β)` cleanly (this module's
--     `rank-adm-bpsi-strict-at-equality`), but the bplus
--     extension `rank-adm (bplus x₁ x₂) <′ rank-adm (bplus y₁ y₂)`
--     requires either (a) additive-principal closure on `rank-adm
--     y₁` (NOT generally available — `rank-adm (bpsi ν β) =
--     ω-rank-pow ν ⊕ rank-pow β` is generically a sum, not an
--     ω-power), or (b) strict-left-monotonicity of `_⊕_` (a NON-
--     theorem; the `α ⊕ ω ≡ β ⊕ ω` counterexample documented in
--     `Phase13.agda`).
--   * Promoting to a redesigned lex rank `rank-lex-jb` whose bplus
--     case carries the leftmost-ψ-α info in the second component
--     would close the headline at the LEX-rank level (lex-first
--     comparing rank-pow's then lex-second comparing α-ranks);
--     however, this requires reshaping the existing `rank-lex` (or
--     introducing a parallel rank), breaking the existing `<ᵇ-ψΩ≤`
--     boundary discharge.  Deferred as a follow-on design slice.
--
-- The bpsi-source-at-equality sub-case is therefore CLOSED AT THE
-- PSI-RANK LEVEL (via `rank-adm-bpsi-strict-at-equality`) and OPEN
-- AT THE BPLUS-CHAIN LEVEL pending one of (a)/(b)/(c) above.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `rank-adm-bpsi-strict-at-equality` — ψ-rank strict step from
--     the α<β witness, joint-bplus-consumer-facing wrapper.
--   * `rank-lex-bpsi-strict-at-equality` — same content lifted to
--     `rank-lex`'s second component via `<lex-second`.
--   * `rank-adm-bplus-decompose-left`   — `rank-adm` decomposes
--     definitionally on bplus into the left and right summands (used
--     by the joint-bplus consumer to chain `rank-adm-bpsi-strict-
--     at-equality` against the source's left summand).

module Ordinal.Buchholz.RankLexSlice3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer            using (Ord)
open import Ordinal.Brouwer.Arithmetic using (_⊕_)
open import Ordinal.Brouwer.Phase13    using (_<′_)
open import Ordinal.Buchholz.Syntax    using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.RankPow   using (rank-pow; ω-rank-pow)
open import Ordinal.Buchholz.RankAdm   using
  ( rank-adm
  ; rank-mono-<ᵇ⁺-ψα-from-pow
  )
open import Ordinal.Buchholz.RankLex   using
  ( RankLex
  ; mkLex
  ; _<lex_
  ; <lex-second
  ; rank-lex
  )

----------------------------------------------------------------------
-- ψ-rank strict step at the equality sub-case (rank-adm side)
----------------------------------------------------------------------

-- Re-export of `RankAdm.rank-mono-<ᵇ⁺-ψα-from-pow` named for the
-- joint-bplus consumer.  Given a `rank-pow α <′ rank-pow β` witness
-- (produced by `Ordinal.Buchholz.RankMonoUmbrella.rank-pow-mono-<ᵇ⁰`
-- for any `α <ᵇ⁰ β`), conclude `rank-adm (bpsi ν α) <′ rank-adm
-- (bpsi ν β)`.
--
-- This is the LOAD-BEARING primitive of the bpsi-source-at-equality
-- sub-case at the ψ-rank level.  The joint-bplus headline at the
-- bplus-chain level is structurally blocked as documented in this
-- module's preamble; this primitive closes the part that DOES close.

rank-adm-bpsi-strict-at-equality : ∀ {ν α β}
  → rank-pow α <′ rank-pow β
  → rank-adm (bpsi ν α) <′ rank-adm (bpsi ν β)
rank-adm-bpsi-strict-at-equality {ν} {α} {β} p =
  rank-mono-<ᵇ⁺-ψα-from-pow {ν} {α} {β} p

----------------------------------------------------------------------
-- ψ-rank strict step at the equality sub-case (rank-lex side)
----------------------------------------------------------------------

-- Lift the strict α-rank step into the `rank-lex` lex order.  Since
-- `rank-lex (bpsi ν α) = mkLex (ω-rank-pow ν) (rank-pow α)` and
-- `rank-lex (bpsi ν β) = mkLex (ω-rank-pow ν) (rank-pow β)`, the
-- first components are syntactically equal (no funext, no `with`
-- elimination needed) and the `<lex-second` constructor fires
-- against the second-component witness.
--
-- This is the LEX-rank-level mirror of `rank-adm-bpsi-strict-at-
-- equality`; consumers that work at the lex-rank level use this one
-- rather than the rank-adm form.  Both convey the same structural
-- content (the α-rank discriminates), differing only in which rank
-- the consumer is composing against.

rank-lex-bpsi-strict-at-equality : ∀ {ν α β}
  → rank-pow α <′ rank-pow β
  → rank-lex (bpsi ν α) <lex rank-lex (bpsi ν β)
rank-lex-bpsi-strict-at-equality {ν} {α} {β} p =
  <lex-second {ω-rank-pow ν} {rank-pow α} {rank-pow β} p

----------------------------------------------------------------------
-- Definitional decomposition of `rank-adm` on `bplus`
----------------------------------------------------------------------

-- Pinned as `refl` for the joint-bplus consumer that needs to chain
-- a strict step on the left summand against a tail bound on the
-- right summand.  Documents the additive structure of `rank-adm` on
-- `bplus` for callers that want to reason about it without re-opening
-- `RankAdm`.

rank-adm-bplus-decompose-left : ∀ x y →
                                rank-adm (bplus x y) ≡ rank-adm x ⊕ rank-adm y
rank-adm-bplus-decompose-left _ _ = refl

----------------------------------------------------------------------
-- Design note: why the headline `rank-pow (bplus x₁ x₂) <′
-- rank-pow (bplus y₁ y₂)` does NOT close from this slice's primitives
----------------------------------------------------------------------

-- The task's stated headline conclusion
--   rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
-- at the bpsi-source-at-equality sub-case
--   (x₁ = bpsi ν α, y₁ = bpsi ν β, x₁ <ᵇ y₁ via the α<β witness)
-- requires a strict step on the bplus left summand at the rank-pow
-- level.  But
--   rank-pow (bpsi ν α) = ω-rank-pow ν = rank-pow (bpsi ν β)
-- by definition; the strict step exists ONLY at the rank-adm level
-- (`rank-adm (bpsi ν α) <′ rank-adm (bpsi ν β)`, which this module
-- closes via `rank-adm-bpsi-strict-at-equality`).
--
-- Lifting the strict rank-adm step to a strict rank-adm sum
--   rank-adm x₁ ⊕ rank-adm x₂ <′ rank-adm y₁ ⊕ rank-adm y₂
-- requires either
--   (a) additive-principal closure on `rank-adm y₁`, which holds
--       only when `rank-adm y₁ = ω-rank-pow _` exactly — i.e., when
--       y₁ is bOmega μ or bzero, NOT when y₁ = bpsi ν β where
--       `rank-adm y₁ = ω-rank-pow ν ⊕ rank-pow β` is a generic sum.
--   (b) strict left-monotonicity of `_⊕_`, which is a NON-theorem
--       under Brouwer arithmetic — the `α ⊕ ω ≡ β ⊕ ω`
--       counterexample documented in `Ordinal.Brouwer.Phase13` (see
--       the block comment near `⊕-mono-≤-left`'s declaration).
--
-- The clean resolution is a parallel rank with a richer bplus second
-- component (`rank-lex-jb : BT → RankLex` whose `bplus`-case carries
-- the leftmost-ψ-α info), but introducing it parallel to `rank-lex`
-- requires a follow-on design slice — the existing `rank-lex`'s
-- `<ᵇ-ψΩ≤`-boundary discharge depends on `rank-lex`'s bplus-case
-- being `oz`-second, so the redesign is non-local.
--
-- Therefore the joint-bplus bpsi-source-at-equality sub-case is
-- CLOSED at the ψ-rank level (one source-level discriminator
-- between source ψ-α and target ψ-β is now formal) and OPEN at the
-- bplus-chain level (transporting that discriminator through bplus
-- requires additional ordinal-arithmetic infrastructure that this
-- session does not land).
--
-- The honest contribution of this slice: pin the ψ-rank discharge as
-- a NAMED THEOREM accessible from the joint-bplus consumer, plus an
-- explicit declaration of the bplus-chain obstacle so the next
-- session can see exactly which lemmas would unblock it without
-- re-deriving the analysis.
