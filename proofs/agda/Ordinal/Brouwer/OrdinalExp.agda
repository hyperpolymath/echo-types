{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Ordinal exponentiation base ω + the first ε-number ε₀ — RUNG 1 of the
-- target-side Brouwer-ordinal climb toward ψ₀(Ω_ω) (the BH order-type
-- fidelity milestone, open problem D-2026-06-14). 2026-06-15.
--
-- ## What this module IS
--
-- * `ω^^_ : Ord → Ord` — ω raised to an ORDINAL power, generalising
--   `OmegaPow.ω^_ : ℕ → Ord` (finite exponent) to limit exponents.
-- * `ε₀ : Ord` — the first ε-number, sup{1, ω, ω^ω, ω^(ω^ω), …},
--   built as the `olim` of the ω-exponentiation tower.
-- * Positivity (`ω^^-pos`, `ε₀-pos`) + the approximant bound
--   (`ε-tower-below-ε₀`), all postulate-free under `--safe --without-K`.
--
-- ## Honest scope (rung 1 of a LONG climb — do not overclaim)
--
-- ε₀ is the first named milestone above the existing `ω^_` /
-- `ω-rank-pow` arithmetic, and it is ENORMOUSLY below ψ₀(Ω_ω): the
-- fidelity height `bh-height = ψ₀(Ω_ω)` (the `Fidelity.AtHeight`
-- parameter) sits far above ε₀ ≪ Γ₀ ≪ … ≪ ψ₀(Ω_ω). This module does
-- NOT plug that parameter. It builds the ordinal-exponentiation
-- primitive every higher rung needs and pins ε₀ as the first checkable
-- value. (ε₀ is itself the collapse ψ₀(Ω₁) — the first nontrivial data
-- point the eventual `denotation` ⟦·⟧ must reproduce.)
--
-- RUNG 2 (2026-06-18): ε₀ IS an ε-number — `ω^^ ε₀ ≃ ε₀` as `_≤′_` in
-- BOTH directions (`ω^^-ε₀-≤`, `ε₀-≤-ω^^-ε₀`, packaged `ε₀-ε-number`).
-- bi-`≤′`, not `≡`, because two `olim`s of different ℕ-indexings of the
-- same supremum are not definitionally equal. No general inflationary
-- lemma is needed: `ω^^ ε₀` is definitionally the `olim` of the shifted
-- tower `n ↦ ε-tower (suc n)`, so each direction reduces to one-step
-- `f-in-lim′` (+ `ω^^-pos` for the base index).
--
-- The *strict* inflationary `α <′ ω^^ α` is deliberately NOT pursued: it
-- is FALSE exactly at the ε-numbers (ε₀ = ω^^ ε₀ is the counterexample);
-- the non-strict `α ≤′ ω^^ α` holds but is not needed for the fixed point.

module Ordinal.Brouwer.OrdinalExp where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13 using (_≤′_; _<′_; f-in-lim′)
open import Ordinal.Brouwer.OmegaPow using (_·ℕ_; oz<′oz⊕)

----------------------------------------------------------------------
-- Ordinal exponentiation base ω
----------------------------------------------------------------------

-- ω^^ α = ω to the ordinal power α.  oz ↦ 1; successor ↦ a limit of
-- finite products (ω^(α+1) = sup_n (ω^α ·ℕ n)); limit ↦ pointwise sup.
-- Structural recursion on the Ord exponent.
ω^^_ : Ord → Ord
ω^^ oz       = osuc oz
ω^^ (osuc α) = olim (λ n → (ω^^ α) ·ℕ n)
ω^^ (olim f) = olim (λ n → ω^^ (f n))

ω^^-zero : ω^^ oz ≡ osuc oz
ω^^-zero = refl

-- ω^^ is strictly positive everywhere (mirrors OmegaPow.ω^_-pos).
ω^^-pos : ∀ α → oz <′ ω^^ α
ω^^-pos oz       = tt
ω^^-pos (osuc α) = 1 , oz<′oz⊕ {ω^^ α} (ω^^-pos α)
ω^^-pos (olim f) = 0 , ω^^-pos (f 0)

----------------------------------------------------------------------
-- ε₀ — the first ε-number
----------------------------------------------------------------------

-- The ω-exponentiation tower 1, ω, ω^ω, ω^(ω^ω), … and its supremum.
ε-tower : ℕ → Ord
ε-tower zero    = osuc oz
ε-tower (suc n) = ω^^ (ε-tower n)

ε-tower-suc : ∀ n → ε-tower (suc n) ≡ ω^^ (ε-tower n)
ε-tower-suc _ = refl

ε₀ : Ord
ε₀ = olim ε-tower

-- ε₀ is positive, and every tower approximant sits at-or-below it.
ε₀-pos : oz <′ ε₀
ε₀-pos = 0 , tt

ε-tower-below-ε₀ : ∀ n → ε-tower n ≤′ ε₀
ε-tower-below-ε₀ n = f-in-lim′ ε-tower n

----------------------------------------------------------------------
-- ε₀ is an ε-number: a fixed point of ω-exponentiation (RUNG 2)
----------------------------------------------------------------------

-- `ω^^ ε₀ ≃ ε₀`, as `_≤′_` in both directions.  `ω^^ ε₀ = ω^^ (olim
-- ε-tower)` reduces to `olim (n ↦ ω^^ (ε-tower n))`, and each
-- `ω^^ (ε-tower n)` is definitionally `ε-tower (suc n)` — i.e. `ω^^ ε₀`
-- is the supremum of the tower SHIFTED by one.  A shifted supremum has
-- the same value, so both inequalities are one-step `f-in-lim′`s.

-- Upper: every element of the shifted tower is below ε₀.
ω^^-ε₀-≤ : ω^^ ε₀ ≤′ ε₀
ω^^-ε₀-≤ n = f-in-lim′ ε-tower (suc n)

-- Lower: every tower element is below the shifted tower's supremum.
-- The base index ε-tower 0 = 1 sits below ε-tower 1 = ω^^ 1 by `ω^^-pos`;
-- every successor element ε-tower (suc m) = ω^^ (ε-tower m) IS the m-th
-- element of the shifted tower, so it is below by `f-in-lim′`.
ε₀-≤-ω^^-ε₀ : ε₀ ≤′ ω^^ ε₀
ε₀-≤-ω^^-ε₀ zero    = 0 , ω^^-pos (osuc oz)
ε₀-≤-ω^^-ε₀ (suc m) = f-in-lim′ (λ k → ω^^ (ε-tower k)) m

-- ε₀ is a fixed point of ω-exponentiation (the defining property of an
-- ε-number), packaged as bi-`≤′`.
ε₀-ε-number : (ω^^ ε₀ ≤′ ε₀) × (ε₀ ≤′ ω^^ ε₀)
ε₀-ε-number = ω^^-ε₀-≤ , ε₀-≤-ω^^-ε₀
