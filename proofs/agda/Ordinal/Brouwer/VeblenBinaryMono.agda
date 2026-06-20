{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Binary Veblen — RUNG 6: first-argument monotonicity (toward Γ₀ as a
-- diagonal fixed point).  Target-side climb toward ψ₀(Ω_ω) (BH order-type
-- fidelity, open problem D-2026-06-14).  Builds on `VeblenBinary` and
-- `VeblenBinaryNormal` (every level a normal function; the Veblen
-- recurrence; the generic fixed-point engine).  2026-06-20.
--
-- ## What this slice adds
--
-- The diagonal Γ₀ = φ_0(0), φ_{φ_0(0)}(0), … was DEFINED in `VeblenBinary`
-- with only `≤′`-upper-bound sanity.  Showing it is a FIXED POINT of the
-- diagonal map D(α) = φ_α(0) needs monotonicity of φ in its FIRST
-- argument.  This slice proves the two forms of first-argument
-- monotonicity that the diagonal needs, and uses them to close ONE
-- direction of the Γ₀ fixed point:
--
--   * `φ-mono₁-step`     — adjacent levels are ordered: φ_α x ≤′ φ_{α+1} x.
--   * `φ-mono₁-into-lim` — a level below a limit is dominated by the limit
--                          level: φ_{h m} x ≤′ φ_{olim h} x.
--   * `Γ₀-prefixed`      — Γ₀ ≤′ φ_Γ₀(0): Γ₀ is a pre-fixed point of the
--                          diagonal (φ_Γ₀(0) is at least Γ₀).
--
-- Both monotonicity results rest on the SAME idea, now mechanised: the
-- value φ_β(x) is a fixed point of every lower level φ_α (α below β), so
--     φ_α x ≤′ φ_α (φ_β x)            [φ_α monotone, x ≤′ φ_β x]
--          = φ_β x                    [φ_β x is a fixed point of φ_α].
-- For the successor case the absorbing fixed point is `φ-level-fixed`
-- (rung 5); for the limit case it is supplied by `commonStep`
-- correctness: a fixed point of `commonStep F` is a common fixed point of
-- every family member (`commonStep-absorb`), and `deriv` lands on such a
-- fixed point (`deriv-fixed-≤` + `commonStep-cont`).
--
-- ## Honest scope (still a LONG climb)
--
-- This closes the `≤′` direction `Γ₀ ≤′ φ_Γ₀(0)` only.  The reverse
-- `φ_Γ₀(0) ≤′ Γ₀` (closure from above) and full "Γ₀ is the LEAST diagonal
-- fixed point" need general first-argument monotonicity / common-fixed-
-- point-from-above and remain OPEN — the next slice.  ψ₀(Ω_ω) sits far
-- above Γ₀ behind the ordinal-collapsing layer; order-type fidelity
-- REMAINS OPEN (D-2026-06-14).  No postulate is closed.

module Ordinal.Brouwer.VeblenBinaryMono where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13
  using (_≤′_; ≤′-trans; ≤′-zero; f-in-lim′)
open import Ordinal.Brouwer.VeblenBinary
  using (φ; deriv; commonStep; Γ₀; Γ-tower; φ-cont)
open import Ordinal.Brouwer.VeblenBinaryNormal
  using (≡→≤′; φ-mono₂; φ-infl; deriv-fixed-≤; φ-level-fixed-≤)

----------------------------------------------------------------------
-- commonStep correctness.
----------------------------------------------------------------------

-- A pre-fixed point of `commonStep F` is a pre-fixed point of every
-- family member: F m y ≤′ commonStep F y ≤′ y.  One step, via the
-- supremum embedding.
commonStep-absorb :
  (F : ℕ → Ord → Ord) (m : ℕ) {y : Ord} →
  commonStep F y ≤′ y → F m y ≤′ y
commonStep-absorb F m {y} p =
  ≤′-trans {F m y} {commonStep F y} {y} (f-in-lim′ (λ n → F n y) m) p

-- `commonStep F` is continuous (in the `≤′` form `deriv-fixed-≤` wants)
-- when every family member is.
commonStep-cont :
  (F : ℕ → Ord → Ord)
  (Fc : ∀ n k → F n (olim k) ≤′ olim (λ m → F n (k m))) →
  ∀ k → commonStep F (olim k) ≤′ olim (λ m → commonStep F (k m))
commonStep-cont F Fc k = λ n →
  ≤′-trans {F n (olim k)} {olim (λ m → F n (k m))} {olim (λ m → commonStep F (k m))}
    (Fc n k)
    (λ m → ≤′-trans {F n (k m)} {commonStep F (k m)} {olim (λ m′ → commonStep F (k m′))}
             (f-in-lim′ (λ n′ → F n′ (k m)) n)
             (f-in-lim′ (λ m′ → commonStep F (k m′)) m))

----------------------------------------------------------------------
-- First-argument monotonicity.
----------------------------------------------------------------------

-- Adjacent levels are ordered.  φ_{α+1} x is a fixed point of φ_α
-- (`φ-level-fixed-≤`), so φ_α x ≤′ φ_α (φ_{α+1} x) = φ_{α+1} x.
φ-mono₁-step : ∀ α x → φ α x ≤′ φ (osuc α) x
φ-mono₁-step α x =
  ≤′-trans {φ α x} {φ α (φ (osuc α) x)} {φ (osuc α) x}
    (φ-mono₂ α {x} {φ (osuc α) x} (φ-infl (osuc α) x))
    (φ-level-fixed-≤ α x)

-- A level below a limit is dominated by the limit level.  φ_{olim h} x is
-- a fixed point of `commonStep (n ↦ φ_{h n})`, hence (by
-- `commonStep-absorb`) a fixed point of each φ_{h m}; so
-- φ_{h m} x ≤′ φ_{h m} (φ_{olim h} x) = φ_{olim h} x.
φ-mono₁-into-lim : ∀ h m x → φ (h m) x ≤′ φ (olim h) x
φ-mono₁-into-lim h m x =
  ≤′-trans {φ (h m) x} {φ (h m) (φ (olim h) x)} {φ (olim h) x}
    (φ-mono₂ (h m) {x} {φ (olim h) x} (φ-infl (olim h) x))
    (commonStep-absorb F m {φ (olim h) x} prefixed)
  where
  F = λ n → φ (h n)
  -- φ (olim h) x = deriv (commonStep F) x, and `deriv` lands on a fixed
  -- point of `commonStep F` (the ≤′ direction).
  prefixed : commonStep F (φ (olim h) x) ≤′ φ (olim h) x
  prefixed =
    deriv-fixed-≤ (commonStep F)
      (commonStep-cont F (λ n k → ≡→≤′ (φ-cont (h n) k))) x

----------------------------------------------------------------------
-- Γ₀ is a pre-fixed point of the diagonal D(α) = φ_α(0).
--
-- Γ₀ = olim Γ-tower, and each successor approximant
-- Γ-tower (suc m) = φ_{Γ-tower m}(0) is ≤′ φ_{olim Γ-tower}(0) = φ_Γ₀(0)
-- by `φ-mono₁-into-lim`.  So the supremum Γ₀ is ≤′ φ_Γ₀(0).
----------------------------------------------------------------------

Γ₀-prefixed : Γ₀ ≤′ φ Γ₀ oz
Γ₀-prefixed = go
  where
  go : ∀ n → Γ-tower n ≤′ φ Γ₀ oz
  go zero    = ≤′-zero {φ Γ₀ oz}
  go (suc m) = φ-mono₁-into-lim Γ-tower m oz
