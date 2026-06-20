{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Binary Veblen — RUNG 5: EVERY level φ_α is a NORMAL FUNCTION, and
-- φ_{α+1} ENUMERATES the fixed points of φ_α.  Target-side climb toward
-- ψ₀(Ω_ω) (BH order-type fidelity, open problem D-2026-06-14).  Builds on
-- `VeblenBinary` (the binary φ + the generic fixed-point engine) and
-- `VeblenPhiNormal` (ω^^-monotonicity).  2026-06-20.
--
-- ## What this slice adds
--
-- `VeblenBinary` defined φ and proved continuity (`φ-cont`) + the generic
-- engine correctness (`nextFix-fixed-{≤,≥}`).  This slice closes the two
-- remaining normal-function properties FOR EVERY LEVEL, by induction on
-- the level α through the generic engine:
--
--   * `φ-mono₂`  — every φ_α is monotone in its argument
--                  (α fixed; a ≤′ b → φ_α a ≤′ φ_α b);
--   * `φ-infl`   — every φ_α is inflationary (β ≤′ φ_α β).
--
-- Together with `VeblenBinary.φ-cont` this gives: EVERY Veblen level is a
-- normal function (strictly-monotone-or-equal + continuous + inflationary
-- — the three properties a fixed-point enumeration needs).
--
-- And the defining property of the hierarchy:
--
--   * `φ-level-fixed-{≤,≥}` — φ_{α+1}(β) IS a fixed point of φ_α
--                  (φ_α (φ_{α+1} β) ≃ φ_{α+1} β, bi-`≤′`).
--
-- The generic engine lemmas (`deriv-mono`, `deriv-infl`, `deriv-fixed-*`,
-- `nextFix-mono`, `commonStep-mono`) are proved once for an arbitrary
-- (monotone / continuous) `g` and then instantiated at each level — the
-- same reuse pattern `VeblenPhiNormal` used for φ₁, now generic.
--
-- ## Honest scope (still a LONG climb)
--
-- This is the normal-function backbone needed for "Γ₀ is the LEAST
-- diagonal fixed point" (the next slice) and for the eventual
-- ordinal-collapsing layer.  It does NOT prove Γ₀ least, does NOT reach
-- the collapsing layer, and closes NO postulate.  Order-type fidelity
-- (ψ₀(Ω_ω)) REMAINS OPEN (D-2026-06-14).  bi-`≤′` (not `≡`) for the
-- fixed-point facts, as throughout the Brouwer climb.

module Ordinal.Brouwer.VeblenBinaryNormal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)
open import Ordinal.Brouwer.Phase13
  using (_≤′_; _<′_; ≤′-refl; ≤′-trans; ≤′-lim; ≤′-zero; ≤′-self-osuc
        ; osuc-mono-≤′; f-in-lim′)
open import Ordinal.Brouwer.OrdinalExp using (ω^^_; ω^^-infl)
open import Ordinal.Brouwer.VeblenPhiNormal using (ω^^-mono-≤′)
open import Ordinal.Brouwer.VeblenBinary
  using (φ; deriv; nextFix; commonStep; g-tower; nextFix-above
        ; nextFix-fixed-≤; nextFix-fixed-≥; φ-cont)

----------------------------------------------------------------------
-- Propositional equality into `≤′` (continuity is stated as `≡`; the
-- generic fixed-point lemmas want the `≤′` form).
----------------------------------------------------------------------

≡→≤′ : ∀ {a b} → a ≡ b → a ≤′ b
≡→≤′ {a} refl = ≤′-refl {a}

----------------------------------------------------------------------
-- Generic monotonicity of the engine (for a monotone g).
----------------------------------------------------------------------

-- The g-tower is monotone in its base.
g-tower-mono :
  (g : Ord → Ord) (gm : ∀ {a b} → a ≤′ b → g a ≤′ g b)
  (a b : Ord) → a ≤′ b → ∀ n → g-tower g a n ≤′ g-tower g b n
g-tower-mono g gm a b p zero    = p
g-tower-mono g gm a b p (suc n) =
  gm {g-tower g a n} {g-tower g b n} (g-tower-mono g gm a b p n)

-- nextFix is monotone in its base (for monotone g).
nextFix-mono :
  (g : Ord → Ord) (gm : ∀ {a b} → a ≤′ b → g a ≤′ g b)
  {x y : Ord} → x ≤′ y → nextFix g x ≤′ nextFix g y
nextFix-mono g gm {x} {y} p =
  λ n → ≤′-lim {g-tower g (osuc x) n} (g-tower g (osuc y)) n
          (g-tower-mono g gm (osuc x) (osuc y) p n)

-- One enumeration step is non-decreasing: deriv g b ≤′ deriv g (osuc b).
-- (No monotonicity hypothesis needed — nextFix lands strictly above.)
deriv-step-≤ : (g : Ord → Ord) (b : Ord) → deriv g b ≤′ deriv g (osuc b)
deriv-step-≤ g b =
  ≤′-trans {deriv g b} {osuc (deriv g b)} {nextFix g (deriv g b)}
    (≤′-self-osuc (deriv g b)) (nextFix-above g (deriv g b))

-- deriv g oz is the least enumerated value.
deriv-oz-least : (g : Ord → Ord) (b : Ord) → deriv g oz ≤′ deriv g b
deriv-oz-least g oz       = ≤′-refl {deriv g oz}
deriv-oz-least g (osuc b) =
  ≤′-trans {deriv g oz} {deriv g b} {deriv g (osuc b)}
    (deriv-oz-least g b) (deriv-step-≤ g b)
deriv-oz-least g (olim h) = ≤′-lim {deriv g oz} (λ k → deriv g (h k)) 0 (deriv-oz-least g (h 0))

-- deriv is monotone in its argument (for monotone g).  Structural
-- recursion on the `_≤′_` shape — the φ₁-mono pattern, now generic.
deriv-mono :
  (g : Ord → Ord) (gm : ∀ {a b} → a ≤′ b → g a ≤′ g b)
  {a b : Ord} → a ≤′ b → deriv g a ≤′ deriv g b
deriv-mono g gm {oz}     {b}      _       = deriv-oz-least g b
deriv-mono g gm {osuc a} {oz}     p       = ⊥-elim p
deriv-mono g gm {osuc a} {osuc b} p       =
  nextFix-mono g gm {deriv g a} {deriv g b} (deriv-mono g gm {a} {b} p)
deriv-mono g gm {osuc a} {olim h} (n , q) =
  ≤′-lim {deriv g (osuc a)} (λ k → deriv g (h k)) n (deriv-mono g gm {osuc a} {h n} q)
deriv-mono g gm {olim a₁} {b}     p       =
  λ n → deriv-mono g gm {a₁ n} {b} (p n)

-- commonStep is monotone when every family member is.
commonStep-mono :
  (F : ℕ → Ord → Ord) (Fm : ∀ n {x y} → x ≤′ y → F n x ≤′ F n y)
  {x y : Ord} → x ≤′ y → commonStep F x ≤′ commonStep F y
commonStep-mono F Fm {x} {y} p =
  λ n → ≤′-lim {F n x} (λ k → F k y) n (Fm n p)

----------------------------------------------------------------------
-- Every Veblen level is monotone in its argument.
----------------------------------------------------------------------

φ-mono₂ : ∀ α {a b} → a ≤′ b → φ α a ≤′ φ α b
φ-mono₂ oz       {a} {b} p = ω^^-mono-≤′ {a} {b} p
φ-mono₂ (osuc α) {a} {b} p =
  deriv-mono (φ α) (λ {c} {d} → φ-mono₂ α {c} {d}) {a} {b} p
φ-mono₂ (olim f) {a} {b} p =
  deriv-mono (commonStep (λ n → φ (f n)))
    (commonStep-mono (λ n → φ (f n)) (λ n {x} {y} → φ-mono₂ (f n) {x} {y})) {a} {b} p

----------------------------------------------------------------------
-- Every Veblen level is inflationary.
----------------------------------------------------------------------

-- deriv is inflationary (no hypothesis on g — nextFix lands above).
deriv-infl : (g : Ord → Ord) → ∀ β → β ≤′ deriv g β
deriv-infl g oz       = ≤′-zero {deriv g oz}
deriv-infl g (osuc β) =
  ≤′-trans {osuc β} {osuc (deriv g β)} {nextFix g (deriv g β)}
    (osuc-mono-≤′ {β} {deriv g β} (deriv-infl g β)) (nextFix-above g (deriv g β))
deriv-infl g (olim h) =
  λ n → ≤′-lim {h n} (λ k → deriv g (h k)) n (deriv-infl g (h n))

φ-infl : ∀ α β → β ≤′ φ α β
φ-infl oz       β = ω^^-infl β
φ-infl (osuc α) β = deriv-infl (φ α) β
φ-infl (olim f) β = deriv-infl (commonStep (λ n → φ (f n))) β

----------------------------------------------------------------------
-- φ_{α+1} enumerates the fixed points of φ_α.
--
-- Every value `deriv g β` is a fixed point of `g` (for continuous /
-- monotone-inflationary g), generalising `nextFix-fixed-*` from the base
-- of the tower to the whole enumeration; instantiated at g = φ_α this is
-- the defining Veblen recurrence φ_α(φ_{α+1}(β)) ≃ φ_{α+1}(β).
----------------------------------------------------------------------

deriv-fixed-≤ :
  (g : Ord → Ord) (gc : ∀ h → g (olim h) ≤′ olim (λ n → g (h n)))
  (β : Ord) → g (deriv g β) ≤′ deriv g β
deriv-fixed-≤ g gc oz       = nextFix-fixed-≤ g gc oz
deriv-fixed-≤ g gc (osuc β) = nextFix-fixed-≤ g gc (deriv g β)
deriv-fixed-≤ g gc (olim h) =
  ≤′-trans {g (olim D)} {olim (λ n → g (D n))} {olim D}
    (gc D)
    (λ n → ≤′-trans {g (D n)} {D n} {olim D}
             (deriv-fixed-≤ g gc (h n)) (f-in-lim′ D n))
  where D = λ k → deriv g (h k)

deriv-fixed-≥ :
  (g : Ord → Ord) (gm : ∀ {a b} → a ≤′ b → g a ≤′ g b) (gi : ∀ y → y ≤′ g y)
  (β : Ord) → deriv g β ≤′ g (deriv g β)
deriv-fixed-≥ g gm gi oz       = nextFix-fixed-≥ g gm gi oz
deriv-fixed-≥ g gm gi (osuc β) = nextFix-fixed-≥ g gm gi (deriv g β)
deriv-fixed-≥ g gm gi (olim h) =
  λ n → ≤′-trans {D n} {g (D n)} {g (olim D)}
          (deriv-fixed-≥ g gm gi (h n)) (gm {D n} {olim D} (f-in-lim′ D n))
  where D = λ k → deriv g (h k)

-- The Veblen recurrence: φ_{α+1}(β) is a fixed point of φ_α (bi-`≤′`).
φ-level-fixed-≤ : ∀ α β → φ α (φ (osuc α) β) ≤′ φ (osuc α) β
φ-level-fixed-≤ α β = deriv-fixed-≤ (φ α) (λ h → ≡→≤′ (φ-cont α h)) β

φ-level-fixed-≥ : ∀ α β → φ (osuc α) β ≤′ φ α (φ (osuc α) β)
φ-level-fixed-≥ α β =
  deriv-fixed-≥ (φ α) (λ {a} {b} → φ-mono₂ α {a} {b}) (φ-infl α) β
