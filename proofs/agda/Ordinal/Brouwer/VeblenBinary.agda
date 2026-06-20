{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Binary Veblen φ_α(β) + the diagonal Γ₀ over Brouwer ordinals — RUNG 4
-- of the target-side climb toward ψ₀(Ω_ω) (BH order-type fidelity, open
-- problem D-2026-06-14).  Builds on `OrdinalExp` (ω^^ = φ₀),
-- `VeblenPhi` / `VeblenPhiNormal` (φ₁ = the ε-number enumeration, now a
-- normal function).  2026-06-20.
--
-- ## The construction (the load-bearing tractability move)
--
-- The two-argument Veblen function is defined by STRUCTURAL RECURSION ON
-- THE FIRST ARGUMENT, returning a function `Ord → Ord`:
--
--   φ oz       = ω^^_                                   (φ₀ = ω-exponentiation)
--   φ (osuc α) = deriv (φ α)                            (enumerate fixed points of φ_α)
--   φ (olim f) = deriv (commonStep (n ↦ φ (f n)))       (common fixed points)
--
-- The SECOND-argument recursion lives entirely inside the generic
-- fixed-point enumerator `deriv` (independent of φ), so φ's own recursion
-- is purely first-argument-structural and Agda accepts its termination
-- WITHOUT a `TERMINATING` pragma.  This is the move that makes binary
-- Veblen tractable here:
--
--   * `deriv g` enumerates the fixed points of a (continuous) `g`, by
--     recursion on its own argument — `deriv g (osuc β) = nextFix g
--     (deriv g β)`, `deriv g (olim h) = olim (deriv g ∘ h)`;
--   * `nextFix g x = olim (g-tower g (osuc x))` is the least fixed point
--     of `g` strictly above `x` (sup of the `g`-iteration tower from
--     `osuc x`) — the exact generalisation of `next-ε` from `VeblenPhi`;
--   * `commonStep F x = olim (n ↦ F n x)` packages a countable family of
--     normal functions into one whose fixed points are the COMMON fixed
--     points of the family — the limit case.
--
-- Γ₀ (the Feferman–Schütte ordinal) is the diagonal:
--   Γ₀ = sup { 0, φ_0(0), φ_{φ_0(0)}(0), … } = olim Γ-tower.
--
-- ## What is proved here
--
--   * the recurrences (`φ-oz`, `φ-osuc`, `φ-olim`) — definitional;
--   * φ is CONTINUOUS in its second argument (`φ-cont`) — a normal-
--     function property, definitional from `deriv`'s `olim` clause;
--   * the generic fixed-point engine is CORRECT: for continuous monotone
--     inflationary `g`, `nextFix g x` is a fixed point of `g` (bi-`≤′`,
--     `nextFix-fixed-≤` / `nextFix-fixed-≥`) and lies strictly above `x`
--     (`nextFix-above`);
--   * the engine SUBSUMES the ε-number story: instantiated at ω^^ it
--     reproves `ω^^ (nextFix ω^^ x) ≃ nextFix ω^^ x` (`ω^^-nextFix-fixed-{≤,≥}`);
--   * Γ₀ is defined, positive (`Γ₀-pos`), an upper bound of its diagonal
--     approximants (`Γ-tower-below-Γ₀`, `φ-diagonal-step`).
--
-- ## Honest scope (rung 4 of a LONG climb — do not overclaim)
--
-- Γ₀ is DEFINED and given basic properties; the full theorem that Γ₀ is
-- the LEAST fixed point of the diagonal α ↦ φ_α(0) (the proper
-- characterisation of the Feferman–Schütte ordinal) is NOT proved here —
-- it needs the common-fixed-point correctness of `commonStep` plus
-- monotonicity/inflationarity of every φ level, and is the next slice.
-- ψ₀(Ω_ω) sits FAR above Γ₀ and additionally needs the ordinal-collapsing
-- layer; order-type fidelity (ψ₀(Ω_ω)) therefore REMAINS OPEN
-- (D-2026-06-14).  This slice neither characterises Γ₀ as least nor plugs
-- `Fidelity.AtHeight`, and closes NO postulate.  bi-`≤′` (not `≡`) is used
-- for fixed-point facts (Brouwer `olim`s of different ℕ-indexings of one
-- supremum are not definitionally equal).

module Ordinal.Brouwer.VeblenBinary where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13
  using (_≤′_; _<′_; ≤′-refl; ≤′-trans; f-in-lim′)
open import Ordinal.Brouwer.OrdinalExp using (ω^^_; ω^^-infl)
open import Ordinal.Brouwer.VeblenPhiNormal using (ω^^-mono-≤′)

----------------------------------------------------------------------
-- The generic fixed-point engine (independent of φ).
----------------------------------------------------------------------

-- Iterate g from a base, ℕ-many times.
g-tower : (Ord → Ord) → Ord → ℕ → Ord
g-tower g x zero    = x
g-tower g x (suc n) = g (g-tower g x n)

-- The least fixed point of g strictly above x: the supremum of the
-- g-iteration tower started at `osuc x`.  Generalises `VeblenPhi.next-ε`.
nextFix : (Ord → Ord) → Ord → Ord
nextFix g x = olim (g-tower g (osuc x))

-- Enumerate the fixed points of g.  Recursion on the SECOND argument,
-- with g fixed; generalises `VeblenPhi.φ₁`.
deriv : (Ord → Ord) → Ord → Ord
deriv g oz       = nextFix g oz
deriv g (osuc β) = nextFix g (deriv g β)
deriv g (olim h) = olim (λ n → deriv g (h n))

-- Package a countable family of normal functions into one whose fixed
-- points are the COMMON fixed points of the family.
commonStep : (ℕ → (Ord → Ord)) → Ord → Ord
commonStep F x = olim (λ n → F n x)

----------------------------------------------------------------------
-- Binary Veblen function.  Structural recursion on the FIRST argument.
----------------------------------------------------------------------

φ : Ord → Ord → Ord
φ oz       = ω^^_
φ (osuc α) = deriv (φ α)
φ (olim f) = deriv (commonStep (λ n → φ (f n)))

-- The recurrences (definitional).
φ-oz : φ oz ≡ ω^^_
φ-oz = refl

φ-osuc : ∀ α → φ (osuc α) ≡ deriv (φ α)
φ-osuc _ = refl

φ-olim : ∀ f → φ (olim f) ≡ deriv (commonStep (λ n → φ (f n)))
φ-olim _ = refl

-- φ is CONTINUOUS in its second argument: it commutes with `olim`.  A
-- defining property of a normal function, here definitional because every
-- branch (ω^^ / deriv) commutes with `olim` by its own `olim` clause.
φ-cont : ∀ α h → φ α (olim h) ≡ olim (λ n → φ α (h n))
φ-cont oz       h = refl
φ-cont (osuc α) h = refl
φ-cont (olim f) h = refl

----------------------------------------------------------------------
-- Correctness of the fixed-point engine (generic, then at ω^^).
----------------------------------------------------------------------

-- `nextFix g x` lies strictly above x (tower index 0 = osuc x).
nextFix-above : ∀ g x → osuc x ≤′ nextFix g x
nextFix-above g x = 0 , ≤′-refl {x}

-- One step of the tower is `g` of the previous (definitional); recorded
-- for readability.
g-tower-suc : ∀ g x n → g (g-tower g x n) ≡ g-tower g x (suc n)
g-tower-suc g x n = refl

-- `g (nextFix g x) ≤′ nextFix g x` for continuous g.  The supremum of the
-- tower SHIFTED by one (= g applied through the limit) is below the
-- supremum of the tower.
nextFix-fixed-≤ :
  (g : Ord → Ord)
  (g-cont : ∀ h → g (olim h) ≤′ olim (λ n → g (h n)))
  (x : Ord) →
  g (nextFix g x) ≤′ nextFix g x
nextFix-fixed-≤ g g-cont x =
  ≤′-trans {g (olim T)} {olim (λ n → g (T n))} {olim T}
    (g-cont T) (λ n → f-in-lim′ T (suc n))
  where T = g-tower g (osuc x)

-- `nextFix g x ≤′ g (nextFix g x)` for monotone inflationary g.  Each
-- tower approximant is below `g (olim T)`: index 0 via inflationarity,
-- successors via monotonicity.
nextFix-fixed-≥ :
  (g : Ord → Ord)
  (g-mono : ∀ {a b} → a ≤′ b → g a ≤′ g b)
  (g-infl : ∀ y → y ≤′ g y)
  (x : Ord) →
  nextFix g x ≤′ g (nextFix g x)
nextFix-fixed-≥ g g-mono g-infl x = go
  where
  T = g-tower g (osuc x)
  go : ∀ n → T n ≤′ g (olim T)
  go zero    =
    ≤′-trans {osuc x} {olim T} {g (olim T)} (f-in-lim′ T 0) (g-infl (olim T))
  go (suc m) = g-mono {T m} {olim T} (f-in-lim′ T m)

----------------------------------------------------------------------
-- The engine subsumes the ε-number story: instantiate at g = ω^^.
-- ω^^ is continuous by definition (its `olim` clause), monotone
-- (`ω^^-mono-≤′`), and inflationary (`ω^^-infl`).  So `nextFix ω^^ x` is
-- a genuine ε-number (fixed point of ω-exponentiation), recovered from the
-- generic engine — exactly the role `next-ε` plays in `VeblenPhi`.
----------------------------------------------------------------------

ω^^-nextFix-fixed-≤ : ∀ x → ω^^ (nextFix ω^^_ x) ≤′ nextFix ω^^_ x
ω^^-nextFix-fixed-≤ =
  nextFix-fixed-≤ ω^^_ (λ h → ≤′-refl {olim (λ n → ω^^ (h n))})

ω^^-nextFix-fixed-≥ : ∀ x → nextFix ω^^_ x ≤′ ω^^ (nextFix ω^^_ x)
ω^^-nextFix-fixed-≥ =
  nextFix-fixed-≥ ω^^_ (λ {a} {b} → ω^^-mono-≤′ {a} {b}) ω^^-infl

----------------------------------------------------------------------
-- Γ₀ — the diagonal (Feferman–Schütte ordinal).
----------------------------------------------------------------------

-- The diagonal tower:  0, φ_0(0), φ_{φ_0(0)}(0), φ_{φ_{φ_0(0)}(0)}(0), …
Γ-tower : ℕ → Ord
Γ-tower zero    = oz
Γ-tower (suc n) = φ (Γ-tower n) oz

Γ₀ : Ord
Γ₀ = olim Γ-tower

-- Γ₀ is positive: the first diagonal step is φ_0(0) = ω^^ 0 = 1.
Γ₀-pos : oz <′ Γ₀
Γ₀-pos = 1 , ≤′-refl {oz}

-- Every diagonal approximant is below Γ₀ (it is their supremum).
Γ-tower-below-Γ₀ : ∀ n → Γ-tower n ≤′ Γ₀
Γ-tower-below-Γ₀ n = f-in-lim′ Γ-tower n

-- The diagonal map applied to an approximant stays below Γ₀:
-- φ_{Γ-tower n}(0) = Γ-tower (suc n) ≤′ Γ₀.  Γ₀ is closed under the
-- diagonal on its own approximants (the constructive seed of "Γ₀ is a
-- fixed point of α ↦ φ_α(0)"; the full bi-`≤′` fixed point is the next
-- slice — see the honest-scope note in the module header).
φ-diagonal-step : ∀ n → φ (Γ-tower n) oz ≤′ Γ₀
φ-diagonal-step n = f-in-lim′ Γ-tower (suc n)
