{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Checked refutation of strict left-monotonicity of `_⊕_`.
--
-- The Phase13 block comment near `⊕-mono-≤-left` notes that the
-- strict-left-mono claim
--
--   ∀ {α β γ} → α <′ β → α ⊕ γ <′ β ⊕ γ
--
-- is NOT a theorem under Brouwer arithmetic, citing the
-- counterexample at α = oz, β = osuc oz, γ = olim nat-to-ord (= ω):
-- both `α ⊕ γ` and `β ⊕ γ` denote the same ordinal (the limit ω),
-- so a strict inequality cannot hold.
--
-- This module promotes that prose claim into a CHECKED REFUTATION:
-- it states `StrictLeftMonoSum` as a named hypothesis, exhibits the
-- counterexample as a finite chain that derives `⊥`, and packages
-- the result as `strict-left-mono-refuted : ¬ StrictLeftMonoSum`.
--
-- Cited by `Ordinal.Buchholz.RankLexSlice3` as the structural
-- blocker for the bplus-chain-level extension of the joint-bplus
-- rank-mono primitive (route (b) of its design-note's open
-- follow-on plan).  Promoting prose to a named theorem makes the
-- closure-decision auditable.
--
-- ## What lands
--
--   * `StrictLeftMonoSum` — the hypothesised property (as a `Set`).
--   * `<′-irrefl` — Brouwer well-foundedness-derived irreflexivity
--     of `_<′_` (small standalone helper; standard derivation from
--     `wf-<′`).
--   * `osuc-oz-⊕-nat≤osuc-oz-⊕-nat` — the structural-recursion
--     helper `osuc oz ⊕ nat-to-ord k ≤′ osuc (oz ⊕ nat-to-ord k)`.
--   * `osuc-oz-⊕-ω≤oz-⊕-ω` — the limit-level companion: both olims
--     denote the same ordinal (ω) so the larger side `≤′` the smaller.
--   * `strict-left-mono-refuted` — the headline `¬ StrictLeftMonoSum`.
--
-- ## Headlines (pin in `Smoke.agda`)
--
--   * `StrictLeftMonoSum`
--   * `strict-left-mono-refuted`

module Ordinal.Brouwer.StrictLeftMonoRefuted where

open import Data.Nat.Base                        using (ℕ; zero; suc)
open import Data.Empty                           using (⊥)
open import Data.Product.Base                    using (_,_)
open import Relation.Nullary                     using (¬_)
open import Induction.WellFounded                using (Acc; acc)

open import Ordinal.Brouwer                      using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Arithmetic           using (_⊕_; nat-to-ord)
open import Ordinal.Brouwer.Phase13              using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-trans
  ; wf-<′
  )

----------------------------------------------------------------------
-- The hypothesised property
----------------------------------------------------------------------

-- Strict left-monotonicity of `_⊕_`: if `α <′ β` then for every
-- right addend `γ`, `α ⊕ γ <′ β ⊕ γ`.  Refuted below.

StrictLeftMonoSum : Set
StrictLeftMonoSum = ∀ {α β γ} → α <′ β → α ⊕ γ <′ β ⊕ γ

----------------------------------------------------------------------
-- Irreflexivity of `_<′_` from well-foundedness
----------------------------------------------------------------------

-- Standard derivation: structural recursion on `Acc _<′_ α`.

acc-no-self : ∀ {α} → Acc _<′_ α → α <′ α → ⊥
acc-no-self (acc rec) α<α = acc-no-self (rec α<α) α<α

<′-irrefl : ∀ {α} → ¬ (α <′ α)
<′-irrefl {α} = acc-no-self (wf-<′ α)

----------------------------------------------------------------------
-- The counterexample: γ = ω (= olim nat-to-ord)
----------------------------------------------------------------------

-- Step a) Per-index dominance: `osuc oz ⊕ nat-to-ord k ≤′ osuc (oz
-- ⊕ nat-to-ord k)`.  Each side is a finite stack of osucs over oz;
-- both reduce to `nat-to-ord (suc k)` semantically.  Proved by
-- structural recursion on k:
--
--   * k = 0:  `osuc oz ⊕ oz = osuc oz` and `osuc (oz ⊕ oz) = osuc oz`
--             (both definitional), so `osuc oz ≤′ osuc oz` is `≤′-refl`.
--   * k = suc k':  Both sides reduce one `osuc` step; the `osuc / osuc`
--             clause of `_≤′_` collapses to the inductive hypothesis.

osuc-oz-⊕-nat≤osuc-of-oz-⊕-nat : ∀ k →
    (osuc oz) ⊕ nat-to-ord k ≤′ osuc (oz ⊕ nat-to-ord k)
osuc-oz-⊕-nat≤osuc-of-oz-⊕-nat zero    = ≤′-refl {osuc oz}
osuc-oz-⊕-nat≤osuc-of-oz-⊕-nat (suc k) =
  osuc-oz-⊕-nat≤osuc-of-oz-⊕-nat k

-- Step b) Branch-selection lemma in the olim: the k-th branch of the
-- "osuc oz" side is bounded by the (suc k)-th branch of the "oz" side,
-- which in turn lives in the limit `oz ⊕ ω`.
--
-- Concretely: `osuc oz ⊕ nat-to-ord k ≤′ oz ⊕ nat-to-ord (suc k)`.
-- Both sides reduce: LHS as `osuc-oz-⊕-nat≤osuc-of-oz-⊕-nat`'s upper
-- bound; RHS by the `_⊕_` definitional clause `α ⊕ osuc β = osuc
-- (α ⊕ β)`, giving exactly `osuc (oz ⊕ nat-to-ord k)`.

osuc-oz-⊕-nat≤oz-⊕-nat-suc : ∀ k →
    (osuc oz) ⊕ nat-to-ord k ≤′ oz ⊕ nat-to-ord (suc k)
osuc-oz-⊕-nat≤oz-⊕-nat-suc k = osuc-oz-⊕-nat≤osuc-of-oz-⊕-nat k

-- Step c) The limit-level companion lemma: `osuc oz ⊕ ω ≤′ oz ⊕ ω`.
-- The "larger" side actually `≤′` the smaller because both olims
-- enumerate the same ordinal ω.
--
-- Per the `olim f ≤′ β` clause of `_≤′_`, we need each branch of
-- the LHS olim to be `≤′` the RHS olim.  For branch k, pick branch
-- `suc k` in the RHS olim and apply `osuc-oz-⊕-nat≤oz-⊕-nat-suc`.

osuc-oz-⊕-ω≤oz-⊕-ω :
    (osuc oz) ⊕ (olim nat-to-ord) ≤′ oz ⊕ (olim nat-to-ord)
osuc-oz-⊕-ω≤oz-⊕-ω zero    = suc zero    , osuc-oz-⊕-nat≤oz-⊕-nat-suc zero
osuc-oz-⊕-ω≤oz-⊕-ω (suc k) = suc (suc k) , osuc-oz-⊕-nat≤oz-⊕-nat-suc (suc k)

----------------------------------------------------------------------
-- The headline refutation
----------------------------------------------------------------------

-- If strict-left-mono held, applying it at α = oz, β = osuc oz,
-- γ = ω would produce `oz ⊕ ω <′ osuc oz ⊕ ω`.  Combined with
-- `osuc-oz-⊕-ω≤oz-⊕-ω` (the other direction) via `≤′-trans`, we get
-- `oz ⊕ ω <′ oz ⊕ ω`, which `<′-irrefl` refutes.
--
-- The premise `oz <′ osuc oz` is `osuc oz ≤′ osuc oz` (= `oz ≤′ oz`
-- = `⊤`).

strict-left-mono-refuted : ¬ StrictLeftMonoSum
strict-left-mono-refuted slm =
  <′-irrefl {oz ⊕ olim nat-to-ord}
    (≤′-trans
      {osuc (oz ⊕ olim nat-to-ord)}
      {osuc oz ⊕ olim nat-to-ord}
      {oz ⊕ olim nat-to-ord}
      (slm {oz} {osuc oz} {olim nat-to-ord} (≤′-refl {osuc oz}))
      osuc-oz-⊕-ω≤oz-⊕-ω)
