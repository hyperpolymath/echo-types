{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Path-3 PROTOTYPE — same-left joint-bplus extension (2026-05-30).
--
-- ## Context
--
-- Slice 3+4 Route A's rank-lex-jb pivot (PRs #147 / #165 / #166)
-- attacks the joint-bplus `<ᵇ-+1`-at-equal-head case by enriching
-- the RANK FUNCTION (carrying `leftmost-α` as a second component)
-- to discriminate where rank-pow alone collapses.  The (a)+(b)+(c)
-- assembly identified a key insight in PR #166's note: the
-- consumer-side first-eq derivation reduces to TAIL-RANK-EQUALITY
-- under WfCNF (`first-eq-from-bpsi-source-at-equal-head`), and the
-- same residual obligation also gates the ψ-rank-level closure
-- (`RankLexSlice3.rank-adm-bpsi-strict-at-equality`).
--
-- ## Path-3 ALTERNATIVE — enrich the SOURCE rule, not the rank
--
-- The K-free `_<ᵇ_`'s `<ᵇ-+1` constructor carries only `x₁ <ᵇ y₁`
-- as premise; nothing on `x₂ vs y₂`.  For the same-LITERAL-left
-- sub-case (`bplus x y₂ <ᵇ bplus x z₂` when `y₂ <ᵇ z₂`),
-- `<ᵇ-irrefl` makes the only viable `<ᵇ-+1` instantiation
-- (`x <ᵇ x`) impossible — so this case is UNREACHABLE in K-free
-- `_<ᵇ_`.  The extended `_<ᵇ⁺_` of `Ordinal.Buchholz.OrderExtended`
-- adds `<ᵇ⁺-+2 : x₁ ≡ y₁ → x₂ <ᵇ y₂ → bplus x₁ x₂ <ᵇ⁺ bplus y₁ y₂`
-- to fill this gap (mod a K-elimination on the shared `x₁ ≡ y₁`).
--
-- This PROTOTYPE narrows the extended `<ᵇ⁺-+2` to `<ᵇ⁰` on the
-- tail premise (the closed 10-constructor umbrella), then shows
-- rank-pow closure FOR THE SAME-LEFT JOINT-BPLUS CASE WITHOUT
-- routing through rank-lex-jb at all.  Path-3's claim: enriching
-- the source-rule with same-left + tail-`<ᵇ⁰` discharges this
-- case at the rank-pow level via `rank-pow-bplus-right-mono`,
-- bypassing the rank-lex-jb pivot's first-eq derivation
-- obligation entirely.
--
-- ## Scope of this prototype
--
-- * Extends only `_<ᵇ⁰_` (10-constructor closure), not `_<ᵇ¹_`
--   (which adds strict-head joint-bplus) — keeps the prototype
--   minimal and the closure inductively grounded.
-- * Does NOT prove well-foundedness of the extended relation —
--   that would need a separate proof; orthogonal to the
--   rank-mono question.
-- * Does NOT subsume rank-lex-jb for the cross-head case
--   (`bpsi ν α` vs `bOmega ν` etc.) — that case has different
--   left-summand SYNTAX, only equal rank-pow.  Rank-lex-jb
--   handles those; this prototype handles same-left-syntax.
--
-- ## What this prototype demonstrates
--
-- The Path-3 implication from PR #166's closing note:
-- "the source rule may need enrichment, not the rank function".
-- A `<ᵇ⁰`-grounded same-left source rule closes its rank-pow
-- obligation in ONE LINE via `rank-pow-bplus-right-mono`,
-- contrasted with the multi-PR rank-lex-jb assembly's chain
-- through first-eq + leftmost-α-strict + `<lex-second`.  When
-- the same-left literal-equality holds, Path-3 is structurally
-- simpler than the rank-lex-jb route.
--
-- Honest caveat: this does NOT close the RANK-EQUAL-HEAD-
-- SYNTAX-DIFFERENT case (e.g., `bpsi ν α` vs `bOmega ν`); the
-- rank-lex-jb pivot is still load-bearing for that scenario.
-- Path-3 covers a strictly different sub-case.

module Ordinal.Buchholz.RankMonoSameLeft where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer.Phase13 using (_<′_)
open import Ordinal.Buchholz.Syntax using (BT; bplus)
open import Ordinal.Buchholz.RankPow using
  ( rank-pow
  ; rank-pow-bplus-right-mono
  )
open import Ordinal.Buchholz.RankMonoUmbrella using
  ( _<ᵇ⁰_
  ; rank-pow-mono-<ᵇ⁰
  )

----------------------------------------------------------------------
-- The extended relation `_<ᵇ⁺²_`
----------------------------------------------------------------------

-- Two constructors:
--
--   1. `<ᵇ⁺²-from-<ᵇ⁰` — embed every `<ᵇ⁰` derivation into the
--      extension.  Keeps the prototype additive over the closed
--      umbrella's 10 cases.
--   2. `<ᵇ⁺²-same-left` — the SOURCE-RULE ENRICHMENT: when the
--      left summand is LITERALLY equal on both sides and the
--      right summand satisfies `<ᵇ⁰`, the bplus chain is in the
--      relation.  Crucially, the SAME `x` appears on both sides
--      under one binder — this is the K-eliminated case that
--      `_<ᵇ_` deliberately omits.  In `--safe --without-K` the
--      shared binder is supplied syntactically (Agda accepts
--      this in `data` constructors; the K-restriction bites only
--      at pattern-match elimination, not at constructor
--      formation).

data _<ᵇ⁺²_ : BT → BT → Set where
  <ᵇ⁺²-from-<ᵇ⁰ : ∀ {x y}
    → x <ᵇ⁰ y
    → x <ᵇ⁺² y

  <ᵇ⁺²-same-left : ∀ {x y₂ z₂}
    → y₂ <ᵇ⁰ z₂
    → bplus x y₂ <ᵇ⁺² bplus x z₂

infix 4 _<ᵇ⁺²_

----------------------------------------------------------------------
-- Rank-pow monotonicity for `_<ᵇ⁺²_`
----------------------------------------------------------------------

-- Direct structural recursion.  The inherited case forwards to the
-- closed umbrella's `rank-pow-mono-<ᵇ⁰`.  The same-left case fires
-- `rank-pow-bplus-right-mono` (which IS `⊕-mono-<-right`
-- specialised to rank-pow) on the tail's rank-pow strict witness.

rank-pow-mono-<ᵇ⁺² : ∀ {x y} → x <ᵇ⁺² y → rank-pow x <′ rank-pow y
rank-pow-mono-<ᵇ⁺² (<ᵇ⁺²-from-<ᵇ⁰ p) = rank-pow-mono-<ᵇ⁰ p
rank-pow-mono-<ᵇ⁺² (<ᵇ⁺²-same-left {x = x} {y₂ = y₂} {z₂ = z₂} p) =
  rank-pow-bplus-right-mono {x = x} {y = y₂} {z = z₂}
    (rank-pow-mono-<ᵇ⁰ p)

----------------------------------------------------------------------
-- Convenience constructor — direct same-left rank-mono
----------------------------------------------------------------------

-- The same-left case stated as a direct rank-mono lemma, without
-- routing through the extended-relation embedding.  Demonstrates
-- the one-line closure that motivated this Path-3 prototype.

rank-pow-mono-same-left :
  ∀ {x y₂ z₂}
  → y₂ <ᵇ⁰ z₂
  → rank-pow (bplus x y₂) <′ rank-pow (bplus x z₂)
rank-pow-mono-same-left {x = x} {y₂ = y₂} {z₂ = z₂} p =
  rank-pow-bplus-right-mono {x = x} {y = y₂} {z = z₂}
    (rank-pow-mono-<ᵇ⁰ p)

----------------------------------------------------------------------
-- What this prototype shows
----------------------------------------------------------------------

-- Path-3 verdict (witnessed mechanically): the SAME-LITERAL-LEFT
-- joint-bplus case at the rank-pow level discharges in ONE LINE
-- via existing `rank-pow-bplus-right-mono` once the source rule
-- carries a `<ᵇ⁰`-grounded tail premise.  The rank-lex-jb pivot's
-- machinery (first-eq derivation, leftmost-α discriminator,
-- `<lex-second` discharge, tail-rank-equality consumer
-- obligation) is NOT NEEDED for this sub-case.
--
-- The implication identified in PR #166's note holds: enriching
-- the source rule is structurally simpler than the rank-function
-- enrichment for this scenario.  For the cross-head case
-- (`bpsi ν α` vs `bOmega ν` etc.), rank-lex-jb's leftmost-α
-- discriminator remains load-bearing; Path-3 is complementary,
-- not subsuming.
--
-- Future work that this prototype unblocks:
--   * Lifting the tail premise from `_<ᵇ⁰_` to `_<ᵇ¹_` (allowing
--     strict-head joint-bplus tails) — composes mechanically via
--     `rank-pow-mono-<ᵇ¹`.
--   * Wrapping the extension in WfCNF endpoints (mirroring
--     `_<ᵇ⁻ⁿ_` from RankMonoUmbrellaSlice4) for downstream
--     consumers that need the canonical-form invariant.
--   * Well-foundedness of `_<ᵇ⁺²_` — separate from rank-mono;
--     would need a Brouwer-rank embedding (the rank function
--     here provides the seed).
