{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Veblen φ-hierarchy over Brouwer ordinals — RUNG 3 (slice 2) of the
-- target-side climb toward ψ₀(Ω_ω) (BH order-type fidelity, open problem
-- D-2026-06-14). 2026-06-18.
--
-- ## This slice: φ₁ — the enumeration of ε-numbers
--
-- The ε-numbers are the fixed points of ω-exponentiation (`ω^^ ε ≃ ε`).
-- φ₁ enumerates them in increasing order:
--
--   * `next-ε β`   — the least ε-number STRICTLY above β: the supremum of
--                    the ω^^-tower started at `osuc β`.  It is a fixed
--                    point by the same shifted-tower argument as ε₀, but
--                    its base index `osuc β` now uses the rung-3.1
--                    inflationary law `ω^^-infl (osuc β)` (ε₀'s `oz` base
--                    only needed `ω^^-pos`).
--   * `φ₁`         — `φ₁ 0 = ε₀`, `φ₁ (α+1) = next-ε (φ₁ α)`,
--                    `φ₁ (lim f) = sup`.
--   * `φ₁-ε-number`— EVERY value of φ₁ is an ε-number (bi-`≤′`).
--
-- ## Honest scope (rung 3 of a long climb)
--
-- φ₁ is the FIRST transfinite Veblen level (φ₀ = ω^^ itself).  The
-- Feferman–Schütte ordinal Γ₀ needs the full binary φ_α hierarchy + its
-- diagonal fixed point; ψ₀(Ω_ω) sits far above even Γ₀ and additionally
-- needs the ordinal-collapsing layer.  Order-type fidelity (ψ₀(Ω_ω))
-- therefore REMAINS OPEN (D-2026-06-14); this slice neither reaches Γ₀
-- nor plugs `Fidelity.AtHeight`.  bi-`≤′` (not `≡`) throughout, because
-- Brouwer `olim`s of different ℕ-indexings of one supremum are not
-- definitionally equal.

module Ordinal.Brouwer.VeblenPhi where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13 using (_≤′_; f-in-lim′; ≤′-refl; ≤′-trans)
open import Ordinal.Brouwer.OrdinalExp using (ω^^_; ε₀; ε₀-ε-number; ω^^-infl)

----------------------------------------------------------------------
-- next-ε : the least ε-number strictly above β
----------------------------------------------------------------------

-- The ω^^-tower started at an arbitrary base.
tower-from : Ord → ℕ → Ord
tower-from x zero    = x
tower-from x (suc n) = ω^^ (tower-from x n)

-- The supremum of the tower from `osuc β` (so it lies above β).
next-ε : Ord → Ord
next-ε β = olim (tower-from (osuc β))

-- `next-ε β` is a fixed point of ω^^ (bi-`≤′`).  Mirrors the ε₀ proof:
-- `ω^^ (next-ε β)` is definitionally the supremum of the tower shifted
-- by one, so each direction is a one-step `f-in-lim′` — except the base
-- index of the ≥ direction, which uses `ω^^-infl (osuc β)`.
ω^^-next-ε-≤ : ∀ β → ω^^ (next-ε β) ≤′ next-ε β
ω^^-next-ε-≤ β n = f-in-lim′ (tower-from (osuc β)) (suc n)

next-ε-≤-ω^^ : ∀ β → next-ε β ≤′ ω^^ (next-ε β)
next-ε-≤-ω^^ β zero =
  ≤′-trans {osuc β} {ω^^ (osuc β)} {olim (λ k → ω^^ (tower-from (osuc β) k))}
    (ω^^-infl (osuc β)) (f-in-lim′ (λ k → ω^^ (tower-from (osuc β) k)) 0)
next-ε-≤-ω^^ β (suc m) =
  f-in-lim′ (λ k → ω^^ (tower-from (osuc β) k)) m

-- `next-ε β` lies strictly above β (witness: tower index 0 = `osuc β`).
β<next-ε : ∀ β → osuc β ≤′ next-ε β
β<next-ε β = 0 , ≤′-refl {β}

----------------------------------------------------------------------
-- φ₁ : the ε-number enumeration
----------------------------------------------------------------------

φ₁ : Ord → Ord
φ₁ oz       = ε₀
φ₁ (osuc α) = next-ε (φ₁ α)
φ₁ (olim f) = olim (λ n → φ₁ (f n))

-- Headline: every value of φ₁ is an ε-number (fixed point of ω^^), bi-`≤′`.
-- oz reuses `ε₀-ε-number`; osuc is `next-ε`'s fixed-point pair for ANY
-- base (no IH); the limit case lifts the per-branch IH through `olim`
-- via `f-in-lim′` (pointwise `≤′` ⇒ `olim`-bounded).
φ₁-ε-number : ∀ α → (ω^^ (φ₁ α) ≤′ φ₁ α) × (φ₁ α ≤′ ω^^ (φ₁ α))
φ₁-ε-number oz       = ε₀-ε-number
φ₁-ε-number (osuc α) = ω^^-next-ε-≤ (φ₁ α) , next-ε-≤-ω^^ (φ₁ α)
φ₁-ε-number (olim f) =
  (λ n → ≤′-trans {ω^^ (φ₁ (f n))} {φ₁ (f n)} {olim (λ k → φ₁ (f k))}
           (proj₁ (φ₁-ε-number (f n))) (f-in-lim′ (λ k → φ₁ (f k)) n))
  , (λ n → ≤′-trans {φ₁ (f n)} {ω^^ (φ₁ (f n))} {olim (λ k → ω^^ (φ₁ (f k)))}
             (proj₂ (φ₁-ε-number (f n))) (f-in-lim′ (λ k → ω^^ (φ₁ (f k))) n))
