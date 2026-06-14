{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Doubled-ladder rank monotonicity — additive-principality of the
-- Ω-block target + the `<ᵇ-+Ω` primitive (2026-06-14).
--
-- ## Why this exists
--
-- The bplus-ON-LEFT constructors (`<ᵇ-+Ω`, `<ᵇ-+ψ`, `<ᵇ-+1`) compare
-- a SUM `rank2 x ⊕ rank2 y` against the target rank.  Closing them
-- needs the target to ABSORB the sum — i.e. additive principality of
-- the target rank.  This slice supplies that for the Ω-block target
-- `ω-rank-pow-succ (double μ) = rank2 (bOmega μ)`, and uses it to
-- discharge the first of the three, `<ᵇ-+Ω`.
--
-- `RankPow.additive-principal-ω-rank-pow` already gives additive
-- principality for the ψ-block target `ω-rank-pow μ`.  The Ω-block
-- target `ω-rank-pow-succ μ` needs its own proof:
--
--   * fin branch — `ω-rank-pow-succ (fin n) = ω^(suc (suc n))` is a
--     clean ω-power, so the existing `OmegaPow.additive-principal`
--     (additive principality of `ω^(suc k)`) applies at `k = suc n`.
--   * ω branch — `ω-rank-pow-succ ω = olim (λ n → ω-rank-pow ω ·ℕ n)`
--     (= ω^(ω+1)) has the SAME limit shape `olim (λ k → B ·ℕ k)` that
--     `OmegaPow.additive-principal` exploits, only with base
--     `B = ω-rank-pow ω` instead of `ω^ n`.  The proof there is
--     generic in the base (it uses only `·ℕ-add-≤ {B}` and the `⊕`
--     monotonicities), so this module re-states it once as
--     `additive-principal-base` over an arbitrary base and instantiates
--     at `B = ω-rank-pow ω`.
--
-- ## Honest scope
--
-- Lands `additive-principal-base`, `additive-principal-ω-rank-pow-succ`,
-- and the `<ᵇ-+Ω` rank2-mono primitive `rank2-mono-+Ω`.  The two
-- remaining bplus-on-left cases (`<ᵇ-+ψ`, `<ᵇ-+1`) have NON-ω-power
-- targets (a ψ-block sum / a bplus sum) and need the tail-ordering
-- machinery (`y ≤ᵇ x` → rank bound) — deferred to the umbrella slice.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `additive-principal-ω-rank-pow-succ`
--   * `rank2-mono-+Ω`

module Ordinal.Buchholz.RankDoubledLadderAddPrincipal where

open import Data.Nat                       using (ℕ; suc; _+_)
open import Data.Product.Base              using (_,_)

open import Ordinal.Brouwer               using (Ord; osuc; olim)
open import Ordinal.Brouwer.Phase13       using
  ( _<′_
  ; _≤′_
  ; ≤′-trans
  ; ≤′-self-osuc
  ; ⊕-mono-≤-left
  ; ⊕-mono-<-right
  )
open import Ordinal.Brouwer.Arithmetic    using (_⊕_)
open import Ordinal.Brouwer.OmegaPow       using (_·ℕ_; ·ℕ-add-≤; additive-principal)
open import Ordinal.OmegaMarkers          using (OmegaIndex; fin; ω)
open import Ordinal.Buchholz.Syntax       using (BT; bOmega; bplus)
open import Ordinal.Buchholz.RankPow       using (ω-rank-pow; ω-rank-pow-succ)
open import Ordinal.Buchholz.RankDoubledLadder using (rank2; double)

----------------------------------------------------------------------
-- Base-generic additive principality of `olim (λ k → B ·ℕ k)`
----------------------------------------------------------------------

-- A re-statement of `OmegaPow.additive-principal` over an ARBITRARY
-- base `B`.  The original proof at `OmegaPow.agda:361` uses only
-- `·ℕ-add-≤ {B}` and the `⊕`-monotonicities — nothing specific to
-- `B = ω^ n` — so it transfers verbatim with `ω^ n ↦ B`.  Needed for
-- the ω-marker Ω-block target `ω-rank-pow-succ ω =
-- olim (λ n → ω-rank-pow ω ·ℕ n)`.
additive-principal-base : ∀ {B α β}
  → α <′ olim (λ k → B ·ℕ k)
  → β <′ olim (λ k → B ·ℕ k)
  → α ⊕ β <′ olim (λ k → B ·ℕ k)
additive-principal-base {B} {α} {β} (kα , sα) (kβ , sβ) = kβ + kα , proof
  where
  α≤′kα : α ≤′ B ·ℕ kα
  α≤′kα = ≤′-trans {α} {osuc α} {B ·ℕ kα} (≤′-self-osuc α) sα

  step1 : α ⊕ β ≤′ (B ·ℕ kα) ⊕ β
  step1 = ⊕-mono-≤-left {α} {B ·ℕ kα} {β} α≤′kα

  step2 : osuc ((B ·ℕ kα) ⊕ β) ≤′ (B ·ℕ kα) ⊕ (B ·ℕ kβ)
  step2 = ⊕-mono-<-right {B ·ℕ kα} {β} {B ·ℕ kβ} sβ

  step3 : (B ·ℕ kα) ⊕ (B ·ℕ kβ) ≤′ B ·ℕ (kβ + kα)
  step3 = ·ℕ-add-≤ {B} kα kβ

  proof : osuc (α ⊕ β) ≤′ B ·ℕ (kβ + kα)
  proof =
    ≤′-trans
      {osuc (α ⊕ β)} {(B ·ℕ kα) ⊕ (B ·ℕ kβ)} {B ·ℕ (kβ + kα)}
      (≤′-trans
        {osuc (α ⊕ β)} {osuc ((B ·ℕ kα) ⊕ β)} {(B ·ℕ kα) ⊕ (B ·ℕ kβ)}
        step1 step2)
      step3

----------------------------------------------------------------------
-- Additive principality of the Ω-block target `ω-rank-pow-succ μ`
----------------------------------------------------------------------

-- The Ω-block analogue of `RankPow.additive-principal-ω-rank-pow`.
-- fin: reuse `OmegaPow.additive-principal` at the doubled successor
-- exponent; ω: instantiate `additive-principal-base` at the base
-- `ω-rank-pow ω`.
additive-principal-ω-rank-pow-succ : ∀ {μ α β}
  → α <′ ω-rank-pow-succ μ
  → β <′ ω-rank-pow-succ μ
  → α ⊕ β <′ ω-rank-pow-succ μ
additive-principal-ω-rank-pow-succ {fin n} pα pβ =
  additive-principal {suc n} pα pβ
additive-principal-ω-rank-pow-succ {ω}     pα pβ =
  additive-principal-base {ω-rank-pow ω} pα pβ

----------------------------------------------------------------------
-- The `<ᵇ-+Ω` rank2-mono primitive
----------------------------------------------------------------------

-- `<ᵇ-+Ω : x <ᵇ bOmega μ → bplus x y <ᵇ bOmega μ`.  The whole sum
-- `rank2 x ⊕ rank2 y` lands below the Ω-block target when BOTH
-- summands do — the left bound is the IH on the sub-derivation
-- `x <ᵇ bOmega μ`, the right bound is the tail bound (from `y ≤ᵇ x`,
-- supplied by the umbrella consumer).  Stated relation-agnostically:
-- both bounds are premises.
rank2-mono-+Ω : ∀ {x y μ}
  → rank2 x <′ rank2 (bOmega μ)
  → rank2 y <′ rank2 (bOmega μ)
  → rank2 (bplus x y) <′ rank2 (bOmega μ)
rank2-mono-+Ω {x} {y} {μ} px py =
  additive-principal-ω-rank-pow-succ {double μ} px py
