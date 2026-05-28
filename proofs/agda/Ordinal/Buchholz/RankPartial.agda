{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Partial `rank-mono-<ᵇ`: the constructors of `Ordinal.Buchholz.Order._<ᵇ_`
-- that DO admit additive Brouwer-rank monotonicity.
--
-- Per `docs/echo-types/buchholz-rank-obstruction.adoc`, the full
-- `rank-mono-<ᵇ` is impossible for the current `_<ᵇ_` because nine
-- of its thirteen constructors are ordinally unsound under any
-- additive rank `BT → Ord` of the form `rank (bplus x y) = rank x
-- ⊕ rank y`.  This module lands the *four* constructors that do
-- admit the additive rank — a stepping stone toward either path
-- 1 (WF-restriction of `_<ᵇ_` with a CNF tail-constraint) or path
-- 2 (a non-additive denotational measure).
--
-- The four passing constructors:
--
--   * `<ᵇ-0-Ω` : `bzero <ᵇ bOmega μ`        — rank `oz <′ ω-rank μ`
--   * `<ᵇ-0-ψ` : `bzero <ᵇ bpsi ν α`         — rank `oz <′ psi-rank ν (rank α)`
--   * `<ᵇ-ΩΩ`  : `bOmega μ <ᵇ bOmega ν` (μ <Ω ν) — rank `ω-rank μ <′ ω-rank ν`
--   * `<ᵇ-Ωψ`  : `bOmega μ <ᵇ bpsi ν α`  (μ <Ω ν) — rank `ω-rank μ <′ psi-rank ν (rank α)`
--
-- The nine failing constructors (`<ᵇ-0-+`, `<ᵇ-ψΩ`, `<ᵇ-ψΩ≤`,
-- `<ᵇ-Ω+`, `<ᵇ-ψ+`, `<ᵇ-+Ω`, `<ᵇ-+ψ`, `<ᵇ-+1`, and the special
-- `bplus bzero bzero` sub-case of `<ᵇ-0-+`) are documented in
-- `buchholz-rank-obstruction.adoc` with per-constructor counter-
-- examples.
--
-- The supporting lemma `ω-rank-mono-<Ω` lands here as well — it
-- is the missing piece from `Ordinal.Brouwer.Arithmetic` that the
-- partial rank-mono needs and that earlier sessions did not
-- isolate.

module Ordinal.Buchholz.RankPartial where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Arithmetic using
  (_⊕_; nat-to-ord; ω-rank; psi-rank)
open import Ordinal.Brouwer.Phase13 using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-zero
  ; ≤′-lim
  ; ≤′-trans
  ; ≤′-self-osuc
  ; ⊕-left-≤-sum
  )

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; fin; ω
  ; _<Ω_
  ; fin<fin
  ; fin<ω
  )
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<ᵇ_
  ; <ᵇ-0-Ω
  ; <ᵇ-0-ψ
  ; <ᵇ-ΩΩ
  ; <ᵇ-Ωψ
  )
open import Ordinal.Buchholz.RankBrouwer using (rank)

----------------------------------------------------------------------
-- Auxiliary: `oz <′ osuc α` for any α
--
-- The strict-below-its-successor witness collapses to `≤′-zero`
-- under the recursive shape of `_<′_`: `osuc oz ≤′ osuc α` reduces
-- to `oz ≤′ α`, which is `tt`.
----------------------------------------------------------------------

oz<′osuc′ : ∀ {α} → oz <′ osuc α
oz<′osuc′ = tt

----------------------------------------------------------------------
-- Auxiliary: `oz <′ nat-to-ord (suc n)` for any n
--
-- The standard successor-stack encoding of `suc n` starts at `osuc
-- (nat-to-ord n)`.  Apply `oz<′osuc′`.
----------------------------------------------------------------------

oz<′nat-to-ord-suc : ∀ n → oz <′ nat-to-ord (suc n)
oz<′nat-to-ord-suc n = oz<′osuc′ {nat-to-ord n}

----------------------------------------------------------------------
-- Auxiliary: monotonicity of `nat-to-ord` under ℕ's strict order
--
-- Structural induction on `m <ℕ n`.  Recursive `_<′_` on a
-- successor stack reduces the goal at each step.
----------------------------------------------------------------------

nat-mono-< : ∀ {m n} → m < n → nat-to-ord m <′ nat-to-ord n
nat-mono-< {zero}  {suc n}  (s≤s z≤n) = oz<′nat-to-ord-suc n
nat-mono-< {suc m} {suc n}  (s≤s m<n) = nat-mono-< {m} {n} m<n

----------------------------------------------------------------------
-- Auxiliary: every `nat-to-ord m` sits strictly below `olim nat-to-ord`
--
-- Pick the index `suc m` in the limit; then `osuc (nat-to-ord m)
-- ≤′ nat-to-ord (suc m)` is reflexivity on the recursive encoding.
----------------------------------------------------------------------

nat-to-lim : ∀ m → nat-to-ord m <′ olim nat-to-ord
nat-to-lim m = ≤′-lim {α = osuc (nat-to-ord m)} nat-to-ord (suc m) (≤′-refl {nat-to-ord m})

----------------------------------------------------------------------
-- Lemma — `ω-rank-mono-<Ω`
--
-- The Ω-marker rank is strictly monotone under `_<Ω_`.  Case
-- analysis on the strict order's two constructors:
--
--   * `fin<fin m<n` reduces to ℕ-monotonicity via `nat-mono-<`.
--   * `fin<ω`        reduces to the limit-domination via `nat-to-lim`.
--
-- This is the missing piece that the four-constructor partial
-- rank-mono below relies on; it was implicit in earlier session
-- discussions but never isolated as a lemma.
----------------------------------------------------------------------

ω-rank-mono-<Ω : ∀ {μ ν} → μ <Ω ν → ω-rank μ <′ ω-rank ν
ω-rank-mono-<Ω (fin<fin {m} {n} m<n) = nat-mono-< {suc m} {suc n} (s≤s m<n)
ω-rank-mono-<Ω (fin<ω {m})           = nat-to-lim (suc m)

----------------------------------------------------------------------
-- Partial rank-mono: the four constructors of `_<ᵇ_` that admit
-- additive Brouwer-rank monotonicity.
----------------------------------------------------------------------

-- `<ᵇ-0-Ω`: rank `bzero = oz`; rank `bOmega μ = ω-rank μ`.  For
-- finite μ = `fin n`, `ω-rank (fin n) = nat-to-ord (suc n) =
-- osuc (nat-to-ord n)`, so `oz <′ osuc _`.  For μ = ω, `ω-rank ω
-- = olim nat-to-ord`, so we use `nat-to-lim` at index 0.

rank-mono-<ᵇ-0-Ω : ∀ {μ} → rank (bzero) <′ rank (bOmega μ)
rank-mono-<ᵇ-0-Ω {fin n} = oz<′nat-to-ord-suc n
rank-mono-<ᵇ-0-Ω {ω}     = nat-to-lim 0

-- `<ᵇ-0-ψ`: rank `bpsi ν α = psi-rank ν (rank α) = osuc (ω-rank ν
-- ⊕ rank α)`.  Outer osuc → `oz <′ osuc _`.

rank-mono-<ᵇ-0-ψ : ∀ {ν α} → rank (bzero) <′ rank (bpsi ν α)
rank-mono-<ᵇ-0-ψ {ν} {α} = oz<′osuc′ {ω-rank ν ⊕ rank α}

-- `<ᵇ-ΩΩ`: rank both sides are `ω-rank`.  Apply `ω-rank-mono-<Ω`.

rank-mono-<ᵇ-ΩΩ : ∀ {μ ν} → μ <Ω ν → rank (bOmega μ) <′ rank (bOmega ν)
rank-mono-<ᵇ-ΩΩ μ<ν = ω-rank-mono-<Ω μ<ν

-- `<ᵇ-Ωψ`: rank `bpsi ν α = osuc (ω-rank ν ⊕ rank α)`.  The
-- target dominates `ω-rank ν` by `⊕-left-≤-sum` and then by
-- `≤′-self-osuc`.  Chain: ω-rank μ <′ ω-rank ν ≤′ ω-rank ν ⊕
-- rank α ≤′ osuc (ω-rank ν ⊕ rank α).

rank-mono-<ᵇ-Ωψ :
  ∀ {μ ν α} → μ <Ω ν → rank (bOmega μ) <′ rank (bpsi ν α)
rank-mono-<ᵇ-Ωψ {μ} {ν} {α} μ<ν =
  -- Goal `rank (bOmega μ) <′ rank (bpsi ν α)` unfolds to
  -- `osuc (ω-rank μ) ≤′ osuc (ω-rank ν ⊕ rank α)`.  Three-step
  -- chain via `≤′-trans`:
  --   1. `osuc (ω-rank μ) ≤′ ω-rank ν`         from ω-rank-mono-<Ω
  --   2. `ω-rank ν ≤′ ω-rank ν ⊕ rank α`        from ⊕-left-≤-sum
  --   3. `ω-rank ν ⊕ rank α ≤′ osuc (ω-rank ν ⊕ rank α)` from ≤′-self-osuc
  let
    step1 : osuc (ω-rank μ) ≤′ ω-rank ν
    step1 = ω-rank-mono-<Ω μ<ν

    step2 : ω-rank ν ≤′ ω-rank ν ⊕ rank α
    step2 = ⊕-left-≤-sum {α = ω-rank ν} (rank α)

    step3 : ω-rank ν ⊕ rank α ≤′ osuc (ω-rank ν ⊕ rank α)
    step3 = ≤′-self-osuc (ω-rank ν ⊕ rank α)

    step12 : osuc (ω-rank μ) ≤′ ω-rank ν ⊕ rank α
    step12 = ≤′-trans {osuc (ω-rank μ)} {ω-rank ν} {ω-rank ν ⊕ rank α} step1 step2

    step123 : osuc (ω-rank μ) ≤′ osuc (ω-rank ν ⊕ rank α)
    step123 = ≤′-trans {osuc (ω-rank μ)} {ω-rank ν ⊕ rank α} {osuc (ω-rank ν ⊕ rank α)} step12 step3
  in step123

----------------------------------------------------------------------
-- A composed partial rank-mono: the four-constructor case dispatch
--
-- Given a derivation `p : x <ᵇ y` whose head is one of the four
-- additively-rankable constructors, produce `rank x <′ rank y`.
-- The cases below are exhaustive *for those four shapes only*;
-- the other nine constructors are intentionally absent and would
-- be rejected by the coverage checker if listed.  Callers that need
-- the full thirteen-constructor coverage must either restrict
-- `_<ᵇ_` (path 1, `WfCNF`-style) or use a non-additive measure
-- (path 2).
--
-- This signature is therefore a *partial function* over `_<ᵇ_`'s
-- constructor space, not a total function: a caller passing one
-- of the nine unsupported constructors will fail to typecheck at
-- the call site.  The four-clause function below mechanises
-- exactly the rank-mono fragment that the obstruction note marks
-- as provable.
----------------------------------------------------------------------

rank-mono-partial-0-Ω : ∀ {μ} → bzero <ᵇ bOmega μ → rank bzero <′ rank (bOmega μ)
rank-mono-partial-0-Ω {μ} <ᵇ-0-Ω = rank-mono-<ᵇ-0-Ω {μ}

rank-mono-partial-0-ψ : ∀ {ν α} → bzero <ᵇ bpsi ν α → rank bzero <′ rank (bpsi ν α)
rank-mono-partial-0-ψ {ν} {α} <ᵇ-0-ψ = rank-mono-<ᵇ-0-ψ {ν} {α}

rank-mono-partial-ΩΩ : ∀ {μ ν} → bOmega μ <ᵇ bOmega ν → rank (bOmega μ) <′ rank (bOmega ν)
rank-mono-partial-ΩΩ {μ} {ν} (<ᵇ-ΩΩ μ<ν) = rank-mono-<ᵇ-ΩΩ {μ} {ν} μ<ν

rank-mono-partial-Ωψ : ∀ {μ ν α} → bOmega μ <ᵇ bpsi ν α → rank (bOmega μ) <′ rank (bpsi ν α)
rank-mono-partial-Ωψ {μ} {ν} {α} (<ᵇ-Ωψ μ<ν) = rank-mono-<ᵇ-Ωψ {μ} {ν} {α} μ<ν
