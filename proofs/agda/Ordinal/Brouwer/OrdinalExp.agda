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
-- This module does NOT prove ε₀ is an ε-number (`ω^^ ε₀ ≡ ε₀`); that
-- fixpoint property and the inflationary `α <′ ω^^ α` are follow-on
-- rungs.

module Ordinal.Brouwer.OrdinalExp where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
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
