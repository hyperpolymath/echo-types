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
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong)

open import Ordinal.Brouwer               using (Ord; osuc)
open import Ordinal.Brouwer.Phase13       using
  ( _≤′_
  ; _<′_
  ; ≤′-trans
  ; ≤′-self-osuc
  )
open import Ordinal.Brouwer.Arithmetic    using (_⊕_)
open import Ordinal.Brouwer.OmegaPow       using
  ( ω^_
  ; ω^-strict-mono
  ; ω^-strict-mono-suc
  ; additive-principal
  )

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
