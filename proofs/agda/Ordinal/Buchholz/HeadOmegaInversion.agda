{-# OPTIONS --safe --without-K #-}

-- Head-Ω inversion for the original Buchholz `_<ᵇ_` order.  Companion
-- module to `Ordinal.Buchholz.HeadOmega` (Slice 1) and `RankPow.agda`
-- Slice 2; option (b) of the Slice 2-bplus follow-on plan from
-- `RankPow.agda`'s preamble.
--
-- ## What this gives
--
-- Two inversion lemmas: from an `<ᵇ` derivation whose source is
-- atomic (`bOmega ν` or `bpsi ν α`), extract a bound on the target
-- term's leading Ω-marker `head-Ω y`.
--
--   * `head-Ω-inv-bOmega : bOmega ν <ᵇ y → ν <Ω head-Ω y`
--   * `head-Ω-inv-bpsi   : bpsi ν α <ᵇ y → ν ≤Ω head-Ω y`
--
-- The strict-vs-non-strict asymmetry tracks the `<ᵇ-ψΩ≤` constructor:
-- `bpsi ν α <ᵇ bOmega μ` only requires `ν ≤Ω μ`, not strict, so the
-- ψ-source lemma can only conclude `≤Ω` against the target head.  The
-- Ω-source lemma is strict because the three constructors with
-- `bOmega ν` on the left (`<ᵇ-ΩΩ`, `<ᵇ-Ωψ`, `<ᵇ-Ω+`) all carry a
-- strict `<Ω` witness on the target's leading Ω-marker.
--
-- ## Why this lemma family
--
-- Option (b) from `RankPow.agda`'s Slice 2-bplus follow-on plan: a
-- head-Ω inversion path that does NOT transitively depend on
-- rank-mono.  The bplus-target case of `<ᵇ-+1` joint-bplus needs to
-- bound `rank-pow source <′ rank-pow target` where `target = bplus y₁
-- y₂` and `rank-pow y₁` is not additive principal in general.  The
-- recovery: use additive-principal-`ω-rank-pow {head-Ω y₁}` (always
-- additive principal) as the closure, and bound the source's rank
-- by `ω-rank-pow-succ (head-Ω y₁)` via Slice 2's domination + this
-- inversion family pulling `head-Ω` information from the `<ᵇ` premise.
--
-- Keeping this inversion family in its own module — rather than
-- threading it through `RankMonoUmbrella`'s `_<ᵇ⁰_` carrier or any
-- rank-mono primitive — preserves the dependency-graph invariant
-- the inline comment in `RankPow.agda`'s Slice 2-bplus note flags:
-- a future signature change to `rank-pow-mono-≤ᵇ` cannot silently
-- break `rank-pow-dominated-by-head-Ω` (or vice versa), because the
-- inversion family talks only about `<Ω` / `≤Ω` on Ω-markers, not
-- about ranks at all.
--
-- ## Out of scope
--
-- The bplus-source inversion (`bplus x y <ᵇ z → head-Ω x ?? head-Ω
-- z`) is structurally different: the three `<ᵇ-+_` constructors all
-- recurse on `x <ᵇ (target)` where x can be anything, so the natural
-- inversion would have to traverse arbitrary BT subterms.  Deferred
-- to a follow-on slice; for the Slice 2-bplus consumer, the bplus
-- source is handled by inducting on the WfCNF carrier and applying
-- the atomic inversions at the leading subterm.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `head-Ω-inv-bOmega`
--   * `head-Ω-inv-bpsi`

module Ordinal.Buchholz.HeadOmegaInversion where

open import Ordinal.OmegaMarkers   using
  ( OmegaIndex
  ; _<Ω_
  ; _≤Ω_
  ; <Ω→≤Ω
  )
open import Ordinal.Buchholz.Syntax using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.Order  using
  ( _<ᵇ_
  ; <ᵇ-ΩΩ
  ; <ᵇ-Ωψ
  ; <ᵇ-ψΩ
  ; <ᵇ-ψΩ≤
  ; <ᵇ-Ω+
  ; <ᵇ-ψ+
  )
open import Ordinal.Buchholz.HeadOmega using (head-Ω)

----------------------------------------------------------------------
-- bOmega-source inversion: strict bound on the target's leading Ω
----------------------------------------------------------------------

-- For each constructor of `_<ᵇ_` that can produce a `bOmega ν <ᵇ y`
-- derivation, the target's leading Ω-marker strictly dominates ν:
--
--   * `<ᵇ-ΩΩ p`:  y = bOmega ν', head-Ω y = ν', p : ν <Ω ν'.
--   * `<ᵇ-Ωψ p`:  y = bpsi ν' α', head-Ω y = ν', p : ν <Ω ν'.
--   * `<ᵇ-Ω+ p`:  y = bplus x' y', head-Ω y = head-Ω x',
--                 recurse on p : bOmega ν <ᵇ x'.
--
-- Termination: the `<ᵇ-Ω+` recursion goes through `p`, a structurally
-- smaller `<ᵇ` derivation.

head-Ω-inv-bOmega : ∀ {ν y} → bOmega ν <ᵇ y → ν <Ω head-Ω y
head-Ω-inv-bOmega (<ᵇ-ΩΩ p) = p
head-Ω-inv-bOmega (<ᵇ-Ωψ p) = p
head-Ω-inv-bOmega (<ᵇ-Ω+ p) = head-Ω-inv-bOmega p

----------------------------------------------------------------------
-- bpsi-source inversion: non-strict bound on the target's leading Ω
----------------------------------------------------------------------

-- For each constructor of `_<ᵇ_` that can produce a `bpsi ν α <ᵇ y`
-- derivation, the target's leading Ω-marker dominates ν (non-strict —
-- the `<ᵇ-ψΩ≤` constructor only carries `ν ≤Ω μ`):
--
--   * `<ᵇ-ψΩ p`:   y = bpsi ν' β', head-Ω y = ν', p : ν <Ω ν'.
--                  Lift to `≤Ω` via `<Ω→≤Ω`.
--   * `<ᵇ-ψΩ≤ p`: y = bOmega μ,    head-Ω y = μ,  p : ν ≤Ω μ.
--                  Pass through directly.
--   * `<ᵇ-ψ+ p`:  y = bplus x' y', head-Ω y = head-Ω x',
--                  recurse on p : bpsi ν α <ᵇ x'.

head-Ω-inv-bpsi : ∀ {ν α y} → bpsi ν α <ᵇ y → ν ≤Ω head-Ω y
head-Ω-inv-bpsi (<ᵇ-ψΩ p)  = <Ω→≤Ω p
head-Ω-inv-bpsi (<ᵇ-ψΩ≤ p) = p
head-Ω-inv-bpsi (<ᵇ-ψ+ p)  = head-Ω-inv-bpsi p
