{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Doubled-ladder rank monotonicity — atomic-boundary slice (2026-06-14).
--
-- ## Why this exists
--
-- `RankDoubledLadder` landed the doubled-ladder rank `rank2 : BT → Ord`
-- together with the arithmetic spine that the single ω-power ladder
-- could not provide:
--
--   * `rank2-bpsi-below-bOmega` — the equal-Ω room fact;
--   * `double-cross-gap`        — the STRICT cross-index gap
--                                 `Ω_ν < ψ_{ν'}(…)` for `ν <Ω ν'`;
--   * `ω-rank-pow-reflects-<Ω`  — the bOmega-case inversion;
--   * `rank2-bounded`           — the WfAdm→rank2 admissibility transfer.
--
-- This slice consumes that spine to discharge the per-constructor
-- `rank2`-monotonicity primitives for the four ATOMIC-vs-ATOMIC
-- comparisons of the core `_<ᵇ_` (`Ordinal.Buchholz.Order`):
--
--   * `<ᵇ-ΩΩ  : μ <Ω ν → bOmega μ <ᵇ bOmega ν`
--   * `<ᵇ-Ωψ  : μ <Ω ν → bOmega μ <ᵇ bpsi ν α`
--   * `<ᵇ-ψΩ  : μ <Ω ν → bpsi μ α <ᵇ bpsi ν β`
--   * `<ᵇ-ψΩ≤ : ν ≤Ω μ → bpsi ν α <ᵇ bOmega μ`
--
-- These are exactly the constructors the doubled ladder was BUILT to
-- enable: the single-ladder `rank-pow` collapses ψ_ν/Ω_ν to the same
-- block (so it cannot order `<ᵇ-ψΩ≤`), and `rank-adm` ranks ψ ABOVE Ω
-- (so it inverts `<ᵇ-Ωψ`).  The doubled ladder orders all four with
-- strict room.
--
-- Each primitive is stated relation-agnostically (premise = the
-- constructor's index data + the LHS `WfAdm` witness where an
-- admissibility bound is needed), so a `_<ᵇ_` consumer pattern-matches
-- on its own constructor and applies the matching primitive — the same
-- discipline as RankPow's `rank-mono-<ᵇ-*` family.
--
-- ## Honest scope
--
-- This slice covers the four atomic-boundary constructors only.  NOT
-- yet landed (documented follow-on):
--   * the bzero-source positivity cases (`<ᵇ-0-Ω/0-ψ/0-+`);
--   * the five bplus-recursive cases (`<ᵇ-Ω+/ψ+/+Ω/+ψ/+1`), which
--     recurse on the `<ᵇ` sub-derivation and combine via `⊕`-mono;
--   * the full `rank2-mono : WfAdm x → WfAdm y → x <ᵇ y → rank2 x <′
--     rank2 y` umbrella + the `wf-<′`-transport headline `wf-<ᵇ`.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `rank2-mono-ΩΩ`
--   * `rank2-mono-Ωψ`
--   * `rank2-mono-ψΩ`
--   * `rank2-mono-ψΩ≤`

module Ordinal.Buchholz.RankDoubledLadderMono where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer               using (Ord; osuc)
open import Ordinal.Brouwer.Phase13       using (_≤′_; _<′_; ≤′-trans; ≤′-self-osuc; ⊕-left-≤-sum)
open import Ordinal.Brouwer.Arithmetic    using (_⊕_)
open import Ordinal.OmegaMarkers          using (OmegaIndex; _<Ω_; _≤Ω_; ≤Ω-split)
open import Ordinal.Buchholz.Syntax       using (BT; bOmega; bpsi)
open import Ordinal.Buchholz.RankPow       using
  ( ω-rank-pow
  ; ω-rank-pow-succ
  ; ω-rank-pow-<-succ
  )
open import Ordinal.Buchholz.RankDoubledLadder using
  ( rank2
  ; double
  ; double-cross-gap
  ; rank2-bpsi-below-bOmega
  ; rank2-bounded
  )
open import Ordinal.Buchholz.WellFormedAdmissible using (WfAdm; wf-adm-bpsi)

----------------------------------------------------------------------
-- Local strict / mixed transitivity (Phase13 exports only ≤′-trans)
----------------------------------------------------------------------

-- `α <′ β` is `osuc α ≤′ β`; chain through `β ≤′ osuc β`.
<′-trans : ∀ {α β γ} → α <′ β → β <′ γ → α <′ γ
<′-trans {α} {β} {γ} p q =
  ≤′-trans {osuc α} {β} {γ} p
    (≤′-trans {β} {osuc β} {γ} (≤′-self-osuc β) q)

-- Mixed `<′ ⨾ ≤′`.  `α <′ β` is `osuc α ≤′ β`, so this is `≤′-trans`.
<′-≤′-trans : ∀ {α β γ} → α <′ β → β ≤′ γ → α <′ γ
<′-≤′-trans {α} {β} {γ} p q = ≤′-trans {osuc α} {β} {γ} p q

----------------------------------------------------------------------
-- Admissibility extraction
----------------------------------------------------------------------

-- From a `WfAdm (bpsi ν α)` witness, recover the rank2-level
-- admissibility bound `rank2 α <′ ω-rank-pow (double ν)` via the
-- scale-transfer bridge.  This is the single point where the slice
-- depends on well-formedness — the bound is what keeps a ψ-rank
-- strictly inside its own doubled exponent block.
ψ-adm-rank2 : ∀ {ν α}
  → WfAdm (bpsi ν α)
  → rank2 α <′ ω-rank-pow (double ν)
ψ-adm-rank2 {ν} {α} (wf-adm-bpsi _ wfα admα) = rank2-bounded {α} {ν} wfα admα

----------------------------------------------------------------------
-- The four atomic-boundary rank2-mono primitives
----------------------------------------------------------------------

-- `<ᵇ-ΩΩ` — Ω_μ < Ω_ν.  Ω-block μ is strictly below ψ-block ν
-- (`double-cross-gap`), which is strictly below Ω-block ν
-- (`ω-rank-pow-<-succ`).
rank2-mono-ΩΩ : ∀ {μ ν}
  → μ <Ω ν
  → rank2 (bOmega μ) <′ rank2 (bOmega ν)
rank2-mono-ΩΩ {μ} {ν} μ<ν =
  <′-trans {ω-rank-pow-succ (double μ)} {ω-rank-pow (double ν)} {ω-rank-pow-succ (double ν)}
    (double-cross-gap μ<ν)
    (ω-rank-pow-<-succ (double ν))

-- `<ᵇ-Ωψ` — Ω_μ < ψ_ν(α) for μ <Ω ν.  Ω-block μ is strictly below
-- ψ-block ν (`double-cross-gap`), which is `≤′` the ψ-rank
-- `ω-rank-pow (double ν) ⊕ rank2 α` (`⊕-left-≤-sum`).  No
-- admissibility needed — the ψ-argument only adds.
rank2-mono-Ωψ : ∀ {μ ν α}
  → μ <Ω ν
  → rank2 (bOmega μ) <′ rank2 (bpsi ν α)
rank2-mono-Ωψ {μ} {ν} {α} μ<ν =
  <′-≤′-trans {ω-rank-pow-succ (double μ)} {ω-rank-pow (double ν)}
              {ω-rank-pow (double ν) ⊕ rank2 α}
    (double-cross-gap μ<ν)
    (⊕-left-≤-sum {ω-rank-pow (double ν)} (rank2 α))

-- `<ᵇ-ψΩ` — ψ_μ(α) < ψ_ν(β) for μ <Ω ν.  Under admissibility the
-- whole ψ_μ(α) rank sits below Ω-block μ (`rank2-bpsi-below-bOmega`),
-- which is below ψ-block ν (`double-cross-gap`), which is `≤′` the
-- target ψ-rank (`⊕-left-≤-sum`).
rank2-mono-ψΩ : ∀ {μ ν α β}
  → WfAdm (bpsi μ α)
  → μ <Ω ν
  → rank2 (bpsi μ α) <′ rank2 (bpsi ν β)
rank2-mono-ψΩ {μ} {ν} {α} {β} wfμα μ<ν =
  <′-≤′-trans {rank2 (bpsi μ α)} {ω-rank-pow (double ν)}
              {ω-rank-pow (double ν) ⊕ rank2 β}
    (<′-trans {rank2 (bpsi μ α)} {ω-rank-pow-succ (double μ)} {ω-rank-pow (double ν)}
      (rank2-bpsi-below-bOmega {μ} {α} (ψ-adm-rank2 {μ} {α} wfμα))
      (double-cross-gap μ<ν))
    (⊕-left-≤-sum {ω-rank-pow (double ν)} (rank2 β))

-- `<ᵇ-ψΩ≤` — ψ_ν(α) < Ω_μ for ν ≤Ω μ.  THE equal-Ω boundary the
-- single ladder could not order.  Split `ν ≤Ω μ`:
--   * ν ≡ μ — the room fact `rank2-bpsi-below-bOmega` lands the goal
--             directly (`ω-rank-pow-succ (double ν) = rank2 (bOmega μ)`);
--   * ν <Ω μ — ψ_ν(α) below Ω-block ν, below ψ-block μ
--             (`double-cross-gap`), below Ω-block μ (`ω-rank-pow-<-succ`).
rank2-mono-ψΩ≤ : ∀ {ν μ α}
  → WfAdm (bpsi ν α)
  → ν ≤Ω μ
  → rank2 (bpsi ν α) <′ rank2 (bOmega μ)
rank2-mono-ψΩ≤ {ν} {μ} {α} wfνα ν≤μ with ≤Ω-split ν≤μ
... | inj₂ refl =
  rank2-bpsi-below-bOmega {ν} {α} (ψ-adm-rank2 {ν} {α} wfνα)
... | inj₁ ν<μ =
  <′-trans {rank2 (bpsi ν α)} {ω-rank-pow-succ (double ν)} {rank2 (bOmega μ)}
    (rank2-bpsi-below-bOmega {ν} {α} (ψ-adm-rank2 {ν} {α} wfνα))
    (<′-trans {ω-rank-pow-succ (double ν)} {ω-rank-pow (double μ)} {ω-rank-pow-succ (double μ)}
      (double-cross-gap ν<μ)
      (ω-rank-pow-<-succ (double μ)))
