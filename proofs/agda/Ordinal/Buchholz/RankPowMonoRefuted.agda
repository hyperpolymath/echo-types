{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Checked refutation: the provisional `rank-pow` is NOT a monotone
-- order-embedding of `_<ᵇ_` — not even restricted to WfCNF terms.  It
-- STRICTLY REVERSES a concrete `<ᵇ` step at the `<ᵇ-+1` joint-bplus
-- ψ/Ω equal-marker boundary.
--
-- ## Why this matters (sharpening the Slice 3 "open" verdict)
--
-- `Ordinal.Buchholz.RankPowSlice3Headline.rank-mono-<ᵇ-+1-via-head-Ω`
-- closes the joint-bplus rank-mono case only UNDER A STRICT-HEAD
-- PREMISE `head-Ω x₁ <Ω head-Ω y₁`, and
-- `Ordinal.Buchholz.RankMonoUmbrellaSlice3._<ᵇ¹_` bakes that premise
-- into its joint-bplus constructor `<ᵇ¹-+1-+`.  The equal-head
-- remainder (`head-Ω x₁ ≡ head-Ω y₁`) is documented in
-- `Ordinal.Buchholz.RankLexSlice3`'s design note as "CLOSED at the
-- ψ-rank level, OPEN at the bplus-chain level pending one of
-- (a)/(b)/(c)".
--
-- This module sharpens that verdict from "open / unproven" to
-- "FALSE".  The equal-head joint-bplus rank-mono statement does not
-- merely lack a proof for the current `rank-pow`: it has a
-- counterexample.  No strengthening of the proof effort closes it.
-- The defect is structural — `rank-pow (bpsi ν _) = ω-rank-pow ν =
-- rank-pow (bOmega ν)` (`RankPow.agda:163,165`) gives ψ_ν(α) and Ω_ν
-- the SAME rank, so `rank-pow` cannot see the strict gap ψ_ν(α) < Ω_ν
-- that the intended ordinal semantics has.  Closing the equal-head
-- case REQUIRES a different rank: one that places ψ_ν(α) strictly
-- below Ω_ν at a shared marker (option (c) of the RankLexSlice3
-- design note — the non-local rank redesign).
--
-- This is the `rank-pow`-level companion to the two Brouwer-arithmetic
-- refutations the closure routes lean on:
--   * `Ordinal.Brouwer.StrictLeftMonoRefuted`            (route (b)),
--   * `Ordinal.Brouwer.AdditivePrincipalGenericRefuted`  (route (a)).
-- Those refute the arithmetic lemmas a `rank-pow`-level closure would
-- have to consume.  This module is more direct: it refutes the
-- rank-monotonicity GOAL itself, so a future session sees immediately
-- that the equal-head case is unreachable with this rank and does not
-- re-attempt it.  Concretely it UPGRADES the placeholder matched-
-- negative `Ordinal.Buchholz.RankMonoUmbrellaSlice4.
-- <ᵇ⁻ⁿ-shortfall-equal-head` (a bare `⊤`-alias) to a checked
-- counterexample, in the same "promote a placeholder to a theorem"
-- spirit as `StrictLeftMonoRefuted`.
--
-- The witness sits at the CROSS-HEAD flavour of the boundary —
-- `bpsi ν _` vs `bOmega ν` (syntactically distinct, `rank-pow`-equal)
-- — which `Ordinal.Buchholz.RankLexJointBplus` flags as the case its
-- `rank-lex-jb` pivot remains load-bearing for.  This refutation is
-- exactly why that pivot to a DIFFERENT rank (one whose `bplus`
-- second component carries `leftmost-α`, placing ψ_ν(α) below Ω_ν) is
-- the only viable forward path: the present `rank-pow` cannot be
-- repaired into monotonicity here, it must be replaced.
--
-- ## The witness (BOTH terms WfCNF)
--
--   s = bplus (bpsi (fin 0) bzero) (bpsi (fin 0) bzero)   -- ψ₀(0) + ψ₀(0)
--   t = bplus (bOmega (fin 0))     bzero                   -- Ω₀ + 0
--
--   * `s <ᵇ t` via `<ᵇ-+1 (<ᵇ-ψΩ≤ (fin 0 ≤Ω fin 0))`: the source's
--     leading summand ψ₀(0) is `<ᵇ` the target's leading summand Ω₀
--     at the EQUAL marker fin 0 — exactly the `<ᵇ-ψΩ≤` boundary that
--     `head-Ω-inv-bpsi` can only bound non-strictly.
--   * Yet `rank-pow t = ω¹ ⊕ oz <′ ω¹ ⊕ ω¹ = rank-pow s`: `rank-pow`
--     ranks the SOURCE strictly ABOVE the TARGET, because both leading
--     summands collapse to ω¹ = `ω-rank-pow (fin 0)` and the source
--     carries a second ψ₀(0) summand while the target's tail is 0.
--
-- Ordinally `s` really is below `t` (ψ₀(0)·2 < Ω₀, since Ω₀ is
-- additively principal); the reversal is purely an artefact of
-- `rank-pow`'s α-blind, ψ/Ω-collapsing shape.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `s`, `t`, `wf-s`, `wf-t`, `s<ᵇt`  -- the witness data
--   * `rank-pow-strictly-reverses`       -- rank-pow t <′ rank-pow s
--   * `RankPowMono`, `rank-pow-mono-refuted`
--                                        -- ¬ (WfCNF rank-monotonicity)
--   * `RankPowMonoPlus1`, `rank-pow-mono-plus1-refuted`
--                                        -- ¬ (joint-bplus, no strict-head)

module Ordinal.Buchholz.RankPowMonoRefuted where

open import Data.Nat.Base                         using (zero; suc; z≤n)
open import Data.Empty                            using (⊥)
open import Data.Sum.Base                         using (inj₁; inj₂)
open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Induction.WellFounded                 using (Acc; acc)

open import Ordinal.Brouwer                       using (oz; osuc)
open import Ordinal.Brouwer.Phase13               using
  ( _≤′_
  ; _<′_
  ; ≤′-zero
  ; ≤′-trans
  ; ⊕-mono-<-right
  ; ⊕-mono-≤-right
  ; wf-<′
  )
open import Ordinal.Brouwer.OmegaPow              using (ω^_; ω^_-pos)
open import Ordinal.OmegaMarkers                  using (fin; _≤Ω_; fin≤fin)
open import Ordinal.Buchholz.Syntax               using
  ( BT; bzero; bOmega; bplus; bpsi )
open import Ordinal.Buchholz.Order                using
  ( _<ᵇ_; <ᵇ-0-Ω; <ᵇ-ψΩ≤; <ᵇ-+1 )
open import Ordinal.Buchholz.WellFormed           using (wf-fin)
open import Ordinal.Buchholz.WellFormedCNF        using
  ( WfCNF
  ; wf-cnf-bzero
  ; wf-cnf-bomega
  ; wf-cnf-bpsi
  ; wf-cnf-bplus
  ; atomic-bzero
  ; atomic-bpsi
  )
open import Ordinal.Buchholz.RankPow              using (rank-pow)

----------------------------------------------------------------------
-- The witness terms
----------------------------------------------------------------------

-- s = ψ₀(0) + ψ₀(0);  t = Ω₀ + 0.  Both in Cantor normal form.
s : BT
s = bplus (bpsi (fin 0) bzero) (bpsi (fin 0) bzero)

t : BT
t = bplus (bOmega (fin 0)) bzero

----------------------------------------------------------------------
-- Both witnesses are WfCNF
----------------------------------------------------------------------

-- s: left = ψ₀(0) (WfCNF), right = ψ₀(0) (atomic), tail bound by
-- equality (ψ₀(0) ≤ᵇ ψ₀(0) via `inj₂ refl`).
wf-s : WfCNF s
wf-s =
  wf-cnf-bplus
    (wf-cnf-bpsi wf-fin wf-cnf-bzero)
    (wf-cnf-bpsi wf-fin wf-cnf-bzero)
    atomic-bpsi
    (inj₂ refl)

-- t: left = Ω₀ (WfCNF), right = 0 (atomic), tail bound 0 ≤ᵇ Ω₀ via
-- `<ᵇ-0-Ω`.
wf-t : WfCNF t
wf-t =
  wf-cnf-bplus
    (wf-cnf-bomega wf-fin)
    wf-cnf-bzero
    atomic-bzero
    (inj₁ <ᵇ-0-Ω)

----------------------------------------------------------------------
-- s <ᵇ t at the ψ/Ω equal-marker boundary
----------------------------------------------------------------------

-- fin 0 ≤Ω fin 0 (reflexive) — the `<ᵇ-ψΩ≤` constructor only needs
-- the NON-strict marker bound, so the equal marker fin 0 suffices.
fin0≤Ωfin0 : fin 0 ≤Ω fin 0
fin0≤Ωfin0 = fin≤fin z≤n

-- ψ₀(0) <ᵇ Ω₀ lifts to (ψ₀(0) + ψ₀(0)) <ᵇ (Ω₀ + 0) via `<ᵇ-+1`
-- (source-strict-on-the-leading-summand).
s<ᵇt : s <ᵇ t
s<ᵇt = <ᵇ-+1 (<ᵇ-ψΩ≤ fin0≤Ωfin0)

----------------------------------------------------------------------
-- rank-pow strictly REVERSES the step
----------------------------------------------------------------------

-- rank-pow t  =  ω-rank-pow (fin 0) ⊕ rank-pow bzero  =  ω¹ ⊕ oz
-- rank-pow s  =  ω-rank-pow (fin 0) ⊕ ω-rank-pow (fin 0)  =  ω¹ ⊕ ω¹
-- and  ω¹ ⊕ oz <′ ω¹ ⊕ ω¹  by strict right-monotonicity of `_⊕_`
-- (right summand oz <′ ω¹ via `ω^_-pos 1`).  Both rank reductions are
-- definitional, so the inequality typechecks against the goal.
rank-pow-strictly-reverses : rank-pow t <′ rank-pow s
rank-pow-strictly-reverses =
  ⊕-mono-<-right {ω^ 1} {oz} {ω^ 1} (ω^_-pos 1)

-- The same reversal as a NON-strict bound, for the `≤′-trans` step in
-- the refutations below (rank-pow t ≤′ rank-pow s).
rank-pow-t≤s : rank-pow t ≤′ rank-pow s
rank-pow-t≤s =
  ⊕-mono-≤-right {ω^ 1} {oz} {ω^ 1} (≤′-zero {ω^ 1})

----------------------------------------------------------------------
-- Irreflexivity of `_<′_` from well-foundedness
----------------------------------------------------------------------

-- Standard derivation by structural recursion on `Acc _<′_ α`
-- (mirrors `Ordinal.Brouwer.StrictLeftMonoRefuted.<′-irrefl`).
acc-no-self : ∀ {α} → Acc _<′_ α → α <′ α → ⊥
acc-no-self (acc rec) α<α = acc-no-self (rec α<α) α<α

<′-irrefl : ∀ {α} → ¬ (α <′ α)
<′-irrefl {α} = acc-no-self (wf-<′ α)

----------------------------------------------------------------------
-- Refutation 1: general WfCNF rank-monotonicity over `_<ᵇ_`
----------------------------------------------------------------------

-- The property a single clean rank-mono theorem would assert: every
-- `<ᵇ` step between WfCNF terms is reflected by a strict rank
-- increase.  This is precisely what fails — which is why the landed
-- programme proceeds constructor-by-constructor with the head-Ω /
-- strict-head machinery rather than as one inductive theorem.
RankPowMono : Set
RankPowMono =
  ∀ {a b} → WfCNF a → WfCNF b → a <ᵇ b → rank-pow a <′ rank-pow b

-- Feeding the witness `s <ᵇ t` to the hypothetical monotonicity gives
-- `rank-pow s <′ rank-pow t`; chaining with `rank-pow t ≤′ rank-pow s`
-- yields `rank-pow s <′ rank-pow s`, refuted by `<′-irrefl`.
rank-pow-mono-refuted : ¬ RankPowMono
rank-pow-mono-refuted mono =
  <′-irrefl {rank-pow s}
    (≤′-trans {osuc (rank-pow s)} {rank-pow t} {rank-pow s}
      (mono wf-s wf-t s<ᵇt) rank-pow-t≤s)

----------------------------------------------------------------------
-- Refutation 2: joint-bplus shape WITHOUT the strict-head premise
----------------------------------------------------------------------

-- The exact statement `RankMonoUmbrellaSlice3.<ᵇ¹-+1-+` works around
-- by adding `head-Ω x₁ <Ω head-Ω y₁`.  Without that premise (only the
-- source-strict witness `x₁ <ᵇ y₁` plus WfCNF), the joint-bplus
-- rank-mono conclusion is false: the witness instantiates it at
-- x₁ = ψ₀(0), x₂ = ψ₀(0), y₁ = Ω₀, y₂ = 0 (where head-Ω x₁ ≡ head-Ω y₁
-- ≡ fin 0, so no strict-head premise is available).
RankPowMonoPlus1 : Set
RankPowMonoPlus1 =
  ∀ {x₁ x₂ y₁ y₂}
  → WfCNF (bplus x₁ x₂) → WfCNF (bplus y₁ y₂)
  → x₁ <ᵇ y₁
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)

rank-pow-mono-plus1-refuted : ¬ RankPowMonoPlus1
rank-pow-mono-plus1-refuted mono =
  <′-irrefl {rank-pow s}
    (≤′-trans {osuc (rank-pow s)} {rank-pow t} {rank-pow s}
      (mono wf-s wf-t (<ᵇ-ψΩ≤ fin0≤Ωfin0)) rank-pow-t≤s)
