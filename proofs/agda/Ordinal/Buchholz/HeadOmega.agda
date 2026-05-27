{-# OPTIONS --safe --without-K #-}

-- Leading-Ω-index head function for Buchholz terms.  First slice of the
-- planned closure of the last open per-constructor case `<ᵇ-+1`
-- joint-bplus in the Buchholz rank-monotonicity matrix
-- (`docs/echo-types/buchholz-rank-obstruction.adoc` §"What remains
-- open").
--
-- ## The closure plan (option A from RankPow.agda's preamble)
--
-- The `<ᵇ-+1` joint-bplus case fails to discharge under `rank-pow`
-- alone because `rank-pow (bplus z₁ z₂)` is not additive principal in
-- general — `rank-pow y₁` (the left summand of the *target*) need not
-- close ⊕-sums of subterm ranks.  The recommended unblock per the
-- obstruction doc is to dominate `rank-pow t` by an additive-principal
-- ω-power indexed by the leading Ω-marker of `t`, and then discharge
-- `<ᵇ-+1` via head-Ω inversion + additive-principal at head-Ω's
-- successor.
--
-- This module lands the *head-Ω function itself* and its definitional
-- sanity lemmas.  The downstream rank-mono / domination work is
-- deferred to follow-on slices, so that the head-Ω abstraction stands
-- on its own merits before any rank consumer pulls on it.
--
-- ## What lands in this slice
--
--   * `head-Ω : BT → OmegaIndex` — the leading-Ω-index head function.
--     Returns the leftmost-deepest Ω marker carried by the term, with
--     `fin 0` as the default for `bzero` (which has none — the future
--     rank-mono lemma will guard this case explicitly via a non-bzero
--     premise).
--   * `head-Ω-bzero`, `head-Ω-bOmega`, `head-Ω-bplus`, `head-Ω-bpsi` —
--     definitional sanity lemmas, one per `BT` constructor.  These
--     lemmas are `refl` (the equations are the definition); they exist
--     so downstream code can rewrite by them without unfolding
--     `head-Ω` directly.
--
-- ## What is deferred to follow-on slices
--
--   * `head-Ω-mono` family (head-Ω respecting WfCNF / WfAdm structural
--     bounds).  Needs the rank-domination lemma to be stated first.
--   * `rank-pow-dominated-by-head-Ω : (t : BT) → NonBzero t → WfCNF t →
--     rank-pow t <′ ω-rank-pow-succ (head-Ω t)` (the load-bearing
--     domination lemma).  Needs an `ω-rank-pow-succ : OmegaIndex →
--     Ord` (one option: `ω-rank-pow-succ (fin n) = ω^(suc (suc n))`,
--     `ω-rank-pow-succ ω = olim (λ n → ω^(suc (suc n)))`) plus a
--     structural recursion on `WfCNF t` using
--     `rank-pow-bplus-into-ω-rank-pow` at each `bplus` step.
--   * `rank-mono-<ᵇ-+1-via-head-Ω` (the headline discharge).  Builds
--     on the domination lemma + `rank-mono-<ᵇ-+1-via-target` from
--     `RankPow.agda`.

module Ordinal.Buchholz.HeadOmega where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers   using (OmegaIndex; fin; ω)
open import Ordinal.Buchholz.Syntax using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )

----------------------------------------------------------------------
-- `head-Ω : BT → OmegaIndex` — leading-Ω-index head function
----------------------------------------------------------------------

-- The leftmost-deepest Ω marker carried by the term.
--
--   * `bzero`        ↦ `fin 0` (default; bzero has no Ω marker — the
--                      future rank-mono lemma will require a
--                      non-bzero premise so this default is never
--                      consumed in proofs).
--   * `bOmega ν`     ↦ `ν`     (the Ω marker IS ν).
--   * `bplus x y`    ↦ `head-Ω x` (leftmost — the WfCNF tail bound
--                      `y ≤ᵇ x` means y's leading Ω is dominated by
--                      x's, so the leftmost is also the deepest).
--   * `bpsi ν α`     ↦ `ν`     (the ψ-binder's Ω-index dominates the
--                      argument α, mirroring the provisional
--                      `rank-pow (bpsi ν α) = ω-rank-pow ν` shape in
--                      `RankPow.agda`).
--
-- Termination is structural (size-decreasing on the first argument
-- of `bplus`), no decreasing measure needed.

head-Ω : BT → OmegaIndex
head-Ω bzero        = fin 0
head-Ω (bOmega ν)   = ν
head-Ω (bplus x _)  = head-Ω x
head-Ω (bpsi ν _)   = ν

----------------------------------------------------------------------
-- Definitional sanity, one lemma per `BT` constructor
----------------------------------------------------------------------

-- These are all `refl` — they record the defining equations so that
-- downstream slices can rewrite by them at consumer sites without
-- unfolding `head-Ω` (or, equivalently, naming the equations
-- explicitly when the unfolding is inconvenient in tactic position).

head-Ω-bzero : head-Ω bzero ≡ fin 0
head-Ω-bzero = refl

head-Ω-bOmega : ∀ ν → head-Ω (bOmega ν) ≡ ν
head-Ω-bOmega _ = refl

head-Ω-bplus : ∀ x y → head-Ω (bplus x y) ≡ head-Ω x
head-Ω-bplus _ _ = refl

head-Ω-bpsi : ∀ ν α → head-Ω (bpsi ν α) ≡ ν
head-Ω-bpsi _ _ = refl

----------------------------------------------------------------------
-- Compositional convenience
----------------------------------------------------------------------

-- `head-Ω` of a left-leaning `bplus` chain bottoms out at the
-- leftmost atom's leading Ω.  Direct consequence of `head-Ω-bplus`
-- applied twice; provided as a named lemma because the two-level
-- pattern recurs in any rank-mono discharge that walks the WfCNF
-- left spine of a `bplus`.

head-Ω-bplus-left : ∀ x y z → head-Ω (bplus (bplus x y) z) ≡ head-Ω x
head-Ω-bplus-left _ _ _ = refl
