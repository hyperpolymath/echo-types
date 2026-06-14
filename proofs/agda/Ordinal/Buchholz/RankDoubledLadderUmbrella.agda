{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- The doubled-ladder umbrella `rank2-mono` + well-foundedness `wf-<ᵇ²`
-- (2026-06-14) — the Gate 1 capstone.
--
-- ## What this lands
--
-- A *rank2-soundness-ready* relation `_<ᵇ²_` mirroring ALL 12
-- constructors of the core `Ordinal.Buchholz.Order._<ᵇ_`, with the
-- rank2-soundness side conditions baked into the constructors (the
-- WfAdm witnesses for the ψ-source atomic cases, the leading-power
-- admissibility bound for `<ᵇ-+ψ`, and the WfCNF tail bounds `y ≤ᵇ² x`
-- for the source-bplus cases).  On this self-contained relation:
--
--   * `rank2-mono-<ᵇ² : s <ᵇ² t → rank2 s <′ rank2 t`  — THE UMBRELLA
--   * `wf-<ᵇ² : WellFounded _<ᵇ²_`                     — well-foundedness
--
-- Unlike the single-ladder `RankMonoUmbrella._<ᵇ⁰_` (which closes only
-- 10 of 13 constructors — `<ᵇ-0-+`, `<ᵇ-ψΩ≤`, and the bplus-target
-- `<ᵇ-+1` were structurally blocked), the doubled ladder closes ALL
-- 12 core constructors, because each has a landed `rank2`-mono
-- primitive:
--
--   * atomic boundary   — RankDoubledLadderMono       (ΩΩ Ωψ ψΩ ψΩ≤)
--   * bzero + via-left   — RankDoubledLadderMonoPlus    (0-Ω 0-ψ 0-+ Ω+ ψ+)
--   * bplus-on-left      — RankDoubledLadderAddPrincipal (+Ω)
--                          + RankDoubledLadderMonoPlus2  (+ψ +1)
--
-- ## The `<ᵇ-+ψ` leading-power bridge
--
-- `rank2-mono-+ψ` needs the source pieces below the ψ-block's LEADING
-- power `ω-rank-pow (double ν)` — strictly stronger than "below the
-- whole ψ-rank".  Plain recursion only gives the weaker bound, so the
-- `<ᵇ²-+ψ` constructor carries `WfAdm x` + `rank-pow x <′ ω-rank-pow ν`
-- and the umbrella derives the leading-power bound through the
-- scale-transfer bridge `rank2-bounded`.  The tail bound on `y` rides
-- the WfCNF order `y ≤ᵇ² x` through `rank2-mono-≤ᵇ²` + `≤′-<′-trans`.
--
-- ## Well-foundedness recipe (mechanical, zero new obligations)
--
--   wf-<ᵇ² = Subrelation.wellFounded rank2-mono-<ᵇ²
--              (On.wellFounded rank2 wf-<′)
--
-- — the same rank-embedding transport as `RankMonoUnionWF.wf-<ᵇᵘ`,
-- routed through `rank2` instead of `rank-pow`.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `_<ᵇ²_`            -- the rank2-ready relation
--   * `rank2-mono-<ᵇ²`   -- THE UMBRELLA (strict)
--   * `rank2-mono-≤ᵇ²`   -- non-strict companion
--   * `wf-<ᵇ²`           -- well-foundedness via rank2 embedding

module Ordinal.Buchholz.RankDoubledLadderUmbrella where

open import Data.Sum.Base                         using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Induction.WellFounded                 using (WellFounded; module Subrelation)
open import Relation.Binary.Construct.On as On    using (wellFounded)

open import Ordinal.OmegaMarkers                  using (_<Ω_; _≤Ω_)
open import Ordinal.Buchholz.Syntax               using (BT; bzero; bOmega; bpsi; bplus)
open import Ordinal.Brouwer                       using (Ord; osuc)
open import Ordinal.Brouwer.Phase13               using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-trans
  ; ≤′-self-osuc
  ; wf-<′
  )
open import Ordinal.Buchholz.RankPow              using (rank-pow; ω-rank-pow)
open import Ordinal.Buchholz.WellFormedAdmissible using (WfAdm)
open import Ordinal.Buchholz.RankDoubledLadder    using
  ( rank2
  ; double
  ; rank2-bounded
  ; ≤′-<′-trans
  )
open import Ordinal.Buchholz.RankDoubledLadderMono using
  ( <′-≤′-trans
  ; rank2-mono-ΩΩ
  ; rank2-mono-Ωψ
  ; rank2-mono-ψΩ
  ; rank2-mono-ψΩ≤
  )
open import Ordinal.Buchholz.RankDoubledLadderMonoPlus using
  ( rank2-pos-bOmega
  ; rank2-pos-bpsi
  ; rank2-mono-0-+
  ; rank2-mono-Ω+
  ; rank2-mono-ψ+
  )
open import Ordinal.Buchholz.RankDoubledLadderAddPrincipal using (rank2-mono-+Ω)
open import Ordinal.Buchholz.RankDoubledLadderMonoPlus2     using (rank2-mono-+ψ; rank2-mono-+1)

----------------------------------------------------------------------
-- The rank2-soundness-ready relation `_<ᵇ²_`
----------------------------------------------------------------------

mutual

  data _<ᵇ²_ : BT → BT → Set where
    -- bzero-source (positivity; 0-+ carries a positivity sub-derivation)
    <ᵇ²-0-Ω : ∀ {μ}   → bzero <ᵇ² bOmega μ
    <ᵇ²-0-ψ : ∀ {ν α} → bzero <ᵇ² bpsi ν α
    <ᵇ²-0-+ : ∀ {x y} → bzero <ᵇ² x → bzero <ᵇ² bplus x y

    -- atomic vs atomic (ψ-source cases carry their WfAdm witness)
    <ᵇ²-ΩΩ  : ∀ {μ ν}     → μ <Ω ν → bOmega μ <ᵇ² bOmega ν
    <ᵇ²-Ωψ  : ∀ {μ ν α}   → μ <Ω ν → bOmega μ <ᵇ² bpsi ν α
    <ᵇ²-ψΩ  : ∀ {μ ν α β}  → WfAdm (bpsi μ α) → μ <Ω ν → bpsi μ α <ᵇ² bpsi ν β
    <ᵇ²-ψΩ≤ : ∀ {ν μ α}    → WfAdm (bpsi ν α) → ν ≤Ω μ → bpsi ν α <ᵇ² bOmega μ

    -- via-left (recurse on the sub-derivation)
    <ᵇ²-Ω+  : ∀ {μ x y}   → bOmega μ <ᵇ² x → bOmega μ <ᵇ² bplus x y
    <ᵇ²-ψ+  : ∀ {ν α x y} → bpsi ν α <ᵇ² x → bpsi ν α <ᵇ² bplus x y

    -- source-bplus (premise on left summand + tail bound on source)
    <ᵇ²-+Ω  : ∀ {x y μ}
      → x <ᵇ² bOmega μ
      → y ≤ᵇ² x
      → bplus x y <ᵇ² bOmega μ
    -- +ψ carries the leading-power admissibility bridge for x
    <ᵇ²-+ψ  : ∀ {x y ν α}
      → WfAdm x
      → rank-pow x <′ ω-rank-pow ν
      → y ≤ᵇ² x
      → bplus x y <ᵇ² bpsi ν α

    -- joint-bplus (whole source below target head)
    <ᵇ²-+1  : ∀ {x₁ x₂ y₁ y₂}
      → bplus x₁ x₂ <ᵇ² y₁
      → bplus x₁ x₂ <ᵇ² bplus y₁ y₂

  _≤ᵇ²_ : BT → BT → Set
  x ≤ᵇ² y = (x <ᵇ² y) ⊎ (x ≡ y)

infix 4 _<ᵇ²_ _≤ᵇ²_

≤ᵇ²-refl : ∀ {x} → x ≤ᵇ² x
≤ᵇ²-refl = inj₂ refl

----------------------------------------------------------------------
-- The umbrella theorem
----------------------------------------------------------------------

mutual

  rank2-mono-<ᵇ² : ∀ {s t} → s <ᵇ² t → rank2 s <′ rank2 t
  rank2-mono-<ᵇ² (<ᵇ²-0-Ω {μ})          = rank2-pos-bOmega μ
  rank2-mono-<ᵇ² (<ᵇ²-0-ψ {ν} {α})      = rank2-pos-bpsi ν α
  rank2-mono-<ᵇ² (<ᵇ²-0-+ {x} {y} p)    =
    rank2-mono-0-+ {x} {y} (rank2-mono-<ᵇ² p)
  rank2-mono-<ᵇ² (<ᵇ²-ΩΩ {μ} {ν} p)     = rank2-mono-ΩΩ {μ} {ν} p
  rank2-mono-<ᵇ² (<ᵇ²-Ωψ {μ} {ν} {α} p) = rank2-mono-Ωψ {μ} {ν} {α} p
  rank2-mono-<ᵇ² (<ᵇ²-ψΩ {μ} {ν} {α} {β} wf p) =
    rank2-mono-ψΩ {μ} {ν} {α} {β} wf p
  rank2-mono-<ᵇ² (<ᵇ²-ψΩ≤ {ν} {μ} {α} wf p) =
    rank2-mono-ψΩ≤ {ν} {μ} {α} wf p
  rank2-mono-<ᵇ² (<ᵇ²-Ω+ {μ} {x} {y} p) =
    rank2-mono-Ω+ {μ} {x} {y} (rank2-mono-<ᵇ² p)
  rank2-mono-<ᵇ² (<ᵇ²-ψ+ {ν} {α} {x} {y} p) =
    rank2-mono-ψ+ {ν} {α} {x} {y} (rank2-mono-<ᵇ² p)
  rank2-mono-<ᵇ² (<ᵇ²-+Ω {x} {y} {μ} p y≤x) =
    rank2-mono-+Ω {x} {y} {μ}
      (rank2-mono-<ᵇ² p)
      (≤′-<′-trans {rank2 y} {rank2 x} {rank2 (bOmega μ)}
        (rank2-mono-≤ᵇ² y≤x)
        (rank2-mono-<ᵇ² p))
  rank2-mono-<ᵇ² (<ᵇ²-+ψ {x} {y} {ν} {α} wfx rpx y≤x) =
    rank2-mono-+ψ {x} {y} {ν} {α}
      (rank2-bounded {x} {ν} wfx rpx)
      (≤′-<′-trans {rank2 y} {rank2 x} {ω-rank-pow (double ν)}
        (rank2-mono-≤ᵇ² y≤x)
        (rank2-bounded {x} {ν} wfx rpx))
  rank2-mono-<ᵇ² (<ᵇ²-+1 {x₁} {x₂} {y₁} {y₂} p) =
    rank2-mono-+1 {x₁} {x₂} {y₁} {y₂} (rank2-mono-<ᵇ² p)

  rank2-mono-≤ᵇ² : ∀ {x y} → x ≤ᵇ² y → rank2 x ≤′ rank2 y
  rank2-mono-≤ᵇ² {x} {y} (inj₁ p) =
    ≤′-trans {rank2 x} {osuc (rank2 x)} {rank2 y}
      (≤′-self-osuc (rank2 x))
      (rank2-mono-<ᵇ² p)
  rank2-mono-≤ᵇ² {x} {.x} (inj₂ refl) = ≤′-refl {rank2 x}

----------------------------------------------------------------------
-- Well-foundedness of `_<ᵇ²_` via the rank2 embedding
----------------------------------------------------------------------

-- Step 1 — InverseImage transport: `_<′_` well-founded on `Ord`
-- lifts to the pullback `_<′_ on rank2` on `BT`.
wf-rank2-pullback : WellFounded (λ x y → rank2 x <′ rank2 y)
wf-rank2-pullback = On.wellFounded rank2 wf-<′

-- Step 2 — Subrelation transport: `rank2-mono-<ᵇ²` witnesses that
-- `_<ᵇ²_` is a sub-relation of the pullback, so it inherits
-- well-foundedness.
wf-<ᵇ² : WellFounded _<ᵇ²_
wf-<ᵇ² = Subrelation.wellFounded rank2-mono-<ᵇ² wf-rank2-pullback
