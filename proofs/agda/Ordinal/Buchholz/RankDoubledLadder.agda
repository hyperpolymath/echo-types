{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Doubled-ladder rank foundation — Slice 1 (2026-06-13).
--
-- ## Why this exists
--
-- Gate 1's residual is the EQUAL-Ω boundary `bpsi ν α <ᵇ bOmega ν`
-- (ψ_ν(α) < Ω_ν at the SAME leading marker ν).  The session that
-- isolated it (`RankPowSlice3Headline` + `head-Ω-strict-or-eq`)
-- and proved the local "room" fact (`RankPowDomination.
-- ω-rank-pow-⊕-below-succ`) also recorded the obstruction to a
-- GLOBAL rank: naively placing `Ω_ν` at `ω-rank-pow-succ ν`
-- (= ω^(ν+2)) breaks the cross-index constructor
-- `<ᵇ-Ωψ` (`bOmega μ <ᵇ bpsi (suc μ) bzero`), because at ν = suc μ
-- the source bound ω^(μ+2) MEETS the target ω^((suc μ)+1) = ω^(μ+2)
-- and the strict gap collapses.
--
-- ## The fix: double the index
--
-- Give ψ and Ω their OWN interleaved exponent blocks by mapping
-- level ν to TWO ω-power blocks instead of one:
--
--     ψexp ν = 2ν+1     (ψ_ν(α) ranks in the ω^(2ν+1) block)
--     Ωexp ν = 2ν+2     (Ω_ν ranks at ω^(2ν+2), one block above)
--
-- The intended atomic order
--
--     … < ψ_ν(α) < Ω_ν < ψ_{ν+1}(β) < Ω_{ν+1} < …
--
-- then embeds with STRICT room everywhere, because consecutive
-- levels are now two exponent-blocks apart:
--
--   * `Ωexp ν = suc (ψexp ν)`           — Ω_ν is exactly one block
--                                          above the ψ_ν block;
--   * `Ωexp μ < ψexp (suc μ)`           — and Ω_μ is strictly below
--                                          the NEXT level's ψ block
--                                          (2μ+2 < 2(μ+1)+1 = 2μ+3),
--                                          which is exactly the
--                                          cross-index gap the single
--                                          ladder could not provide.
--
-- ## What this slice lands (the two interleaving facts)
--
--   * `ψ-block-below-Ω-block` — the doubled-ladder room fact:
--     an admissibility-bounded ψ-rank `ω^(2ν+1) ⊕ β` (with
--     `β <′ ω^(2ν+1)`) is strictly below `ω^(2ν+2)`.  (Same shape
--     as `ω-rank-pow-⊕-below-succ`, re-expressed on the doubled
--     exponents so it composes with the cross-index fact below.)
--   * `Ω-block-below-next-ψ` — the cross-index gap: `ω^(2μ+2) <′
--     ω^(2ν+1)` whenever `μ < n`.  This is the fact the single
--     ladder lacked; the doubling buys it as plain `ω^`-strict-mono
--     on `Ωexp μ < ψexp ν`.
--
-- Together these are the arithmetic spine of the doubled-ladder
-- rank `rank2 : BT → Ord` (ψ_ν → ω^(2ν+1) ⊕ …, Ω_ν → ω^(2ν+2),
-- bplus → ⊕), whose per-constructor monotonicity + WF transport are
-- the follow-on slices.
--
-- ## Honest scope
--
-- Slice 1 is the fin-index arithmetic foundation only.  NOT yet
-- landed: the `rank2` function itself; the OmegaIndex ω (limit)
-- cases; the per-constructor rank-mono re-proof against `rank2`;
-- the `wf-<′`-transport.  This module proves the doubled ladder
-- RESOLVES the documented cross-index obstruction at the fin level —
-- the design is sound; the build-out is mechanical follow-on.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `ψ-block-below-Ω-block`
--   * `Ω-block-below-next-ψ`

module Ordinal.Buchholz.RankDoubledLadder where

open import Data.Nat using (ℕ; suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (+-suc; +-mono-≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

open import Ordinal.Brouwer               using (Ord; osuc; oz; olim)
open import Ordinal.Brouwer.Phase13       using
  ( _≤′_
  ; _<′_
  ; ≤′-trans
  ; ≤′-self-osuc
  ; f-in-lim′
  )
open import Ordinal.Brouwer.Arithmetic    using (_⊕_)
open import Ordinal.Brouwer.OmegaPow       using
  ( ω^_
  ; ω^-strict-mono
  ; ω^-strict-mono-suc
  ; additive-principal
  )
open import Ordinal.OmegaMarkers          using (OmegaIndex; fin; ω; _<Ω_; fin<fin; fin<ω)
open import Ordinal.Buchholz.Syntax       using (BT; bzero; bOmega; bpsi; bplus)
open import Ordinal.Buchholz.RankPow      using (ω-rank-pow; ω-rank-pow-succ)
open import Ordinal.Buchholz.RankPowDomination using (ω-rank-pow-⊕-below-succ)

----------------------------------------------------------------------
-- Local strict transitivity (Phase13 exports only ≤′-trans)
----------------------------------------------------------------------

-- `α <′ β` is `osuc α ≤′ β`; chain through `β ≤′ osuc β`.
<′-trans : ∀ {α β γ} → α <′ β → β <′ γ → α <′ γ
<′-trans {α} {β} {γ} p q =
  ≤′-trans {osuc α} {β} {γ} p
    (≤′-trans {β} {osuc β} {γ} (≤′-self-osuc β) q)

----------------------------------------------------------------------
-- The doubled-index exponent blocks
----------------------------------------------------------------------

-- ψ-block exponent for level n: 2n+1.
ψexp : ℕ → ℕ
ψexp n = suc (n + n)

-- Ω-block exponent for level n: 2n+2 = suc (ψexp n).
Ωexp : ℕ → ℕ
Ωexp n = suc (suc (n + n))

----------------------------------------------------------------------
-- Fact 1 — ψ-block sits below Ω-block at the SAME level
----------------------------------------------------------------------

-- The doubled-ladder room fact.  Under admissibility (`β <′ ω^(2ν+1)`),
-- the ψ-rank `ω^(2ν+1) ⊕ β` is strictly below `ω^(2ν+2)`.  Both
-- summands are `< ω^(suc (ψexp n)) = ω^(Ωexp n)` (left by one-step
-- strict-mono, right by admissibility + that step), and the target is
-- additive principal, so the sum stays below.
ψ-block-below-Ω-block : ∀ {n β}
  → β <′ ω^ (ψexp n)
  → (ω^ (ψexp n) ⊕ β) <′ ω^ (Ωexp n)
ψ-block-below-Ω-block {n} {β} β<ψ =
  additive-principal {ψexp n} {ω^ (ψexp n)} {β}
    (ω^-strict-mono-suc (ψexp n))
    (<′-trans {β} {ω^ (ψexp n)} {ω^ (suc (ψexp n))}
      β<ψ
      (ω^-strict-mono-suc (ψexp n)))

----------------------------------------------------------------------
-- Fact 2 — Ω-block sits below the NEXT level's ψ-block (cross-index)
----------------------------------------------------------------------

-- The fact the single ω-power ladder lacked.  For `m < n`,
-- `Ωexp m = 2m+2 < 2n+1 = ψexp n` (because `m < n` gives
-- `m+1 ≤ n`, hence `(m+1)+(m+1) ≤ n+n`, i.e. `2m+2 ≤ 2n < 2n+1`).
-- So `ω^(2m+2) <′ ω^(2n+1)` by plain `ω^`-strict-mono — the strict
-- gap survives even at the boundary `n = suc m` that defeated the
-- single ladder.
Ω-block-below-next-ψ : ∀ {m n}
  → m < n
  → ω^ (Ωexp m) <′ ω^ (ψexp n)
Ω-block-below-next-ψ {m} {n} m<n = ω^-strict-mono Ωexp-m<ψexp-n
  where
    -- suc m + suc m ≡ suc (suc (m + m))   (def on the left + +-suc)
    +-shift : suc m + suc m ≡ suc (suc (m + m))
    +-shift = cong suc (+-suc m m)

    -- 2m+2 ≤ n+n  from  (m+1)+(m+1) ≤ n+n
    Ωexp-m≤n+n : suc (suc (m + m)) ≤ n + n
    Ωexp-m≤n+n = subst (_≤ n + n) +-shift (+-mono-≤ m<n m<n)

    -- 2m+2 < 2n+1
    Ωexp-m<ψexp-n : Ωexp m < ψexp n
    Ωexp-m<ψexp-n = s≤s Ωexp-m≤n+n

----------------------------------------------------------------------
-- Slice 2 — the doubled-ladder rank `rank2 : BT → Ord`
----------------------------------------------------------------------

-- The doubled ladder is just the EXISTING `ω-rank-pow` /
-- `ω-rank-pow-succ` on a DOUBLED OmegaIndex.  Doubling the fin index
-- by `n ↦ n + n` lands the ψ-block on `ω-rank-pow (fin (n+n)) =
-- ω^(suc (n+n)) = ω^(2n+1) = ω^(ψexp n)` and the Ω-block on
-- `ω-rank-pow-succ (fin (n+n)) = ω^(2n+2) = ω^(Ωexp n)`, both
-- DEFINITIONALLY (no transport).  So the whole `Ordinal.Brouwer`
-- machinery — additive-principal closure, the room fact
-- `RankPowDomination.ω-rank-pow-⊕-below-succ` (which is ∀ OmegaIndex,
-- so it covers the limit `ω` marker too), strict-mono — transfers to
-- the doubled ladder for free, by instantiating its index at
-- `double ν`.

double : OmegaIndex → OmegaIndex
double (fin n) = fin (n + n)
double ω       = ω

-- `rank2 : BT → Ord` — ψ_ν(α) into the 2ν+1 block (offset by the
-- α-rank), Ω_ν at the 2ν+2 block, bplus by ordinal sum, bzero at oz.
rank2 : BT → Ord
rank2 bzero       = oz
rank2 (bOmega ν)  = ω-rank-pow-succ (double ν)
rank2 (bpsi ν α)  = ω-rank-pow (double ν) ⊕ rank2 α
rank2 (bplus x y) = rank2 x ⊕ rank2 y

----------------------------------------------------------------------
-- Definitional sanity
----------------------------------------------------------------------

rank2-bzero : rank2 bzero ≡ oz
rank2-bzero = refl

rank2-bOmega : ∀ ν → rank2 (bOmega ν) ≡ ω-rank-pow-succ (double ν)
rank2-bOmega _ = refl

rank2-bpsi : ∀ ν α → rank2 (bpsi ν α) ≡ ω-rank-pow (double ν) ⊕ rank2 α
rank2-bpsi _ _ = refl

rank2-bplus : ∀ x y → rank2 (bplus x y) ≡ rank2 x ⊕ rank2 y
rank2-bplus _ _ = refl

----------------------------------------------------------------------
-- Headline: the equal-Ω boundary discharge at `rank2`
----------------------------------------------------------------------

-- The payoff of the doubled ladder.  At the SAME leading marker ν, an
-- admissibility-bounded ψ_ν(α) ranks strictly below Ω_ν:
--
--   rank2 (bpsi ν α) = ω-rank-pow (double ν) ⊕ rank2 α
--                    <′ ω-rank-pow-succ (double ν) = rank2 (bOmega ν)
--
-- given `rank2 α <′ ω-rank-pow (double ν)` (the rank2-level
-- admissibility bound — the WfAdm bridge that supplies it from
-- `WfAdm`'s `rank-pow α <′ ω-rank-pow ν` field is the follow-on).
--
-- This is EXACTLY `RankPowDomination.ω-rank-pow-⊕-below-succ`
-- instantiated at the doubled index `double ν` — covering both the
-- fin AND the limit (`ω`) marker, since that lemma is total over
-- OmegaIndex.  This is the case the single-ladder rank-pow/rank-adm
-- could not discharge (rank-pow collapses ψ_ν/Ω_ν; rank-adm ranks
-- ψ ABOVE Ω); the doubled ladder closes it directly.
rank2-bpsi-below-bOmega : ∀ {ν α}
  → rank2 α <′ ω-rank-pow (double ν)
  → rank2 (bpsi ν α) <′ rank2 (bOmega ν)
rank2-bpsi-below-bOmega {ν} {α} adm =
  ω-rank-pow-⊕-below-succ {double ν} {rank2 α} adm

----------------------------------------------------------------------
-- Cross-index gap at the doubled scale (the `<ᵇ-Ωψ` arithmetic)
----------------------------------------------------------------------

-- The doubled ladder's STRICT cross-index gap, lifted to the
-- `double`-of-OmegaIndex form and total over the marker (fin AND ω):
--
--   ν <Ω μ  →  rank2 (bOmega ν)  <′  ω-rank-pow (double μ)
--           =  ω-rank-pow-succ (double ν) <′ ω-rank-pow (double μ)
--
-- i.e. Ω_ν's rank-block (2·idx ν + 2) lands strictly below μ's
-- ψ-block (2·idx μ + 1) whenever ν <Ω μ.  This is the fact that the
-- single ω-power ladder could NOT provide (there, `ω-rank-pow-succ
-- μ ≤′ ω-rank-pow ν` was only NON-strict at the boundary
-- ν = suc μ); the doubling buys the strict inequality, here for
-- both the fin markers (via the Slice-1 fact `Ω-block-below-next-ψ`,
-- definitionally aligned through `double (fin n) = fin (n+n)`) and
-- the limit marker `ω` (via one-step strict-mono into the limit's
-- (2a+3)-th approximant).
--
-- This is the arithmetic the cross-index `<ᵇ-Ωψ` constructor's
-- `rank2`-mono will consume (with `⊕`-left-weakening to absorb the
-- target's ψ-argument), and the bOmega case of the WfAdm→rank2
-- scale-transfer bridge.
double-cross-gap : ∀ {ν μ}
  → ν <Ω μ
  → ω-rank-pow-succ (double ν) <′ ω-rank-pow (double μ)
double-cross-gap {fin a} {fin b} (fin<fin a<b) = Ω-block-below-next-ψ a<b
double-cross-gap {fin a} {ω}     fin<ω         =
  ≤′-trans
    {osuc (ω^ (suc (suc (a + a))))}
    {ω^ (suc (suc (suc (a + a))))}
    {olim (λ n → ω^ (suc n))}
    (ω^-strict-mono-suc (suc (suc (a + a))))
    (f-in-lim′ (λ n → ω^ (suc n)) (suc (suc (a + a))))
