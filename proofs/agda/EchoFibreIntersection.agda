{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoFibreIntersection: multi-witness narrowing (squeakwell rung R8).
--
-- A recovery engine that has observed several modalities of one entity
-- asks for the witnesses satisfying ALL the observations at once. In
-- Echo terms that is the intersection of fibres over one shared
-- witness: `Σ A (λ x → f x ≡ y × g x ≡ z)`. This module pins the three
-- facts hyperpolymath/squeakwell's proof ladder (docs/ROUTE-PLAN.adoc,
-- rung R8) needs about that intersection:
--
--   * Binary narrowing is a fibre.  Intersecting the fibres of `f` at
--     `y` and of `g` at `z` IS the fibre of the pairing `< f , g >` at
--     `(y , z)`: `fibre-intersection-iso`, a K-free `_↔_` with `refl`
--     round-trips (no funext — the equations are on pairs, not on
--     functions).
--   * Narrowing never changes the witness.  Forgetting either
--     constraint is witness-preserving (`forget-left-witness`,
--     `forget-right-witness`), and adding one more constraint to a
--     family of `n` constraints is again witness-preserving in both
--     directions (`narrow-fin-step-to`, `narrow-fin-step-from`). The
--     `Fin n` family form is stated with pointwise equations, so it
--     needs no funext; it is NOT packaged as a `_↔_` because the
--     round-trip on the function side would.
--   * Narrowing shrinks the candidate fibre.  On a finite domain with
--     decidable equality, the honest count of `EchoFiberCount` can
--     only go down when a constraint is added: `narrow-shrinks`
--     (`FiberSize-fin < f , g > (y , z) ≤ FiberSize-fin f y`). This is
--     the quantitative statement behind squeakwell's review queue:
--     every extra observed modality narrows the candidates.
--
-- Honest scope. The survey's proposed "covering masks ⇒ subsingleton
-- fibre" is NOT here: over an opaque value type two full sections that
-- agree on every modality need not be equal without extensionality, and
-- squeakwell's identifiers are opaque. The route plan dropped it; so
-- does this module. Nothing here claims the intersection is inhabited:
-- observations can be jointly unsatisfiable, and the count can be 0.
--
-- Headlines (pinned in Smoke.agda):
--
--   * fibre-intersection-iso   -- Echo < f , g > (y , z) ↔ Narrow f g y z
--   * forget-left-witness      -- forgetting a constraint keeps the witness
--   * forget-right-witness
--   * narrow-fin-step-to       -- Fin (suc n) family = one more binary step
--   * narrow-fin-step-from
--   * narrow-shrinks           -- FiberSize-fin of the pairing ≤ FiberSize-fin of f

module EchoFibreIntersection where

open import Function.Base                         using (_∘_)
open import Level                                 using (Level; _⊔_)
open import Data.Empty                            using (⊥; ⊥-elim)
import      Data.Nat.Base                         as ℕ
open        ℕ                                     using (ℕ; _≤_; z≤n; s≤s)
open import Data.Fin.Base                         using (Fin; zero; suc)
open import Data.Product.Base                     using (Σ; _×_; _,_; proj₁; proj₂; <_,_>)
open import Function.Bundles                      using (_↔_; mk↔ₛ′)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Echo                                  using (Echo)
open import EchoFiberCount                        using (FiberSize-fin)

private
  variable
    ℓa ℓb ℓc : Level
    A : Set ℓa
    B : Set ℓb
    C : Set ℓc

----------------------------------------------------------------------
-- Binary narrowing: two constraints on one witness.
----------------------------------------------------------------------

-- The witnesses `x` with `f x ≡ y` AND `g x ≡ z`: the intersection of
-- the two fibres over a shared witness.
Narrow : (f : A → B) (g : A → C) → B → C → Set _
Narrow {A = A} f g y z = Σ A (λ x → (f x ≡ y) × (g x ≡ z))

pair-fibre→narrow :
  {f : A → B} {g : A → C} {y : B} {z : C} →
  Echo < f , g > (y , z) → Narrow f g y z
pair-fibre→narrow (x , p) = x , cong proj₁ p , cong proj₂ p

narrow→pair-fibre :
  {f : A → B} {g : A → C} {y : B} {z : C} →
  Narrow f g y z → Echo < f , g > (y , z)
narrow→pair-fibre (x , p , q) = x , cong₂ _,_ p q

-- Round trips. Both close by matching the equation on `refl`; the
-- indices `y`, `z` are variables, so this is `--without-K`-safe.
narrow-to-from :
  {f : A → B} {g : A → C} {y : B} {z : C} →
  (e : Echo < f , g > (y , z)) →
  narrow→pair-fibre {f = f} {g = g} (pair-fibre→narrow e) ≡ e
narrow-to-from (x , refl) = refl

narrow-from-to :
  {f : A → B} {g : A → C} {y : B} {z : C} →
  (w : Narrow f g y z) →
  pair-fibre→narrow {f = f} {g = g} (narrow→pair-fibre w) ≡ w
narrow-from-to (x , refl , refl) = refl

-- Headline 1: binary narrowing IS the fibre of the pairing.
fibre-intersection-iso :
  (f : A → B) (g : A → C) (y : B) (z : C) →
  Echo < f , g > (y , z) ↔ Narrow f g y z
fibre-intersection-iso f g y z =
  mk↔ₛ′ pair-fibre→narrow narrow→pair-fibre
        (narrow-from-to {f = f} {g = g}) (narrow-to-from {f = f} {g = g})

----------------------------------------------------------------------
-- Forgetting a constraint keeps the witness.
----------------------------------------------------------------------

forget-left :
  {f : A → B} {g : A → C} {y : B} {z : C} → Narrow f g y z → Echo g z
forget-left (x , _ , q) = x , q

forget-right :
  {f : A → B} {g : A → C} {y : B} {z : C} → Narrow f g y z → Echo f y
forget-right (x , p , _) = x , p

-- Headline 2: narrowing is a refinement of the SAME candidate, never a
-- different one. Both are definitional.
forget-left-witness :
  {f : A → B} {g : A → C} {y : B} {z : C} (w : Narrow f g y z) →
  proj₁ (forget-left {f = f} w) ≡ proj₁ w
forget-left-witness _ = refl

forget-right-witness :
  {f : A → B} {g : A → C} {y : B} {z : C} (w : Narrow f g y z) →
  proj₁ (forget-right {g = g} w) ≡ proj₁ w
forget-right-witness _ = refl

----------------------------------------------------------------------
-- Families of constraints indexed by `Fin n`.
----------------------------------------------------------------------

-- `n` observations `fs i x ≡ ys i` on one witness `x`, stated pointwise
-- (no function equality, hence no funext).
NarrowFin : ∀ {n} (fs : Fin n → A → B) (ys : Fin n → B) → Set _
NarrowFin {A = A} fs ys = Σ A (λ x → ∀ i → fs i x ≡ ys i)

-- Headline 3: a family of `suc n` constraints is one binary narrowing
-- step on top of a family of `n`, in both directions, and the witness
-- is untouched (both maps are `refl` on `proj₁`).
narrow-fin-step-to :
  ∀ {n} (fs : Fin (ℕ.suc n) → A → B) (ys : Fin (ℕ.suc n) → B) →
  NarrowFin fs ys →
  Σ A (λ x → (fs zero x ≡ ys zero) × (∀ i → fs (suc i) x ≡ ys (suc i)))
narrow-fin-step-to fs ys (x , h) = x , h zero , (λ i → h (suc i))

narrow-fin-step-from :
  ∀ {n} (fs : Fin (ℕ.suc n) → A → B) (ys : Fin (ℕ.suc n) → B) →
  Σ A (λ x → (fs zero x ≡ ys zero) × (∀ i → fs (suc i) x ≡ ys (suc i))) →
  NarrowFin fs ys
narrow-fin-step-from fs ys (x , p , h) = x , step
  where
    step : ∀ i → fs i x ≡ ys i
    step zero    = p
    step (suc i) = h i

narrow-fin-step-to-witness :
  ∀ {n} (fs : Fin (ℕ.suc n) → A → B) (ys : Fin (ℕ.suc n) → B)
  (w : NarrowFin fs ys) →
  proj₁ (narrow-fin-step-to fs ys w) ≡ proj₁ w
narrow-fin-step-to-witness _ _ _ = refl

narrow-fin-step-from-witness :
  ∀ {n} (fs : Fin (ℕ.suc n) → A → B) (ys : Fin (ℕ.suc n) → B)
  (w : Σ A (λ x → (fs zero x ≡ ys zero) × (∀ i → fs (suc i) x ≡ ys (suc i)))) →
  proj₁ (narrow-fin-step-from fs ys w) ≡ proj₁ w
narrow-fin-step-from-witness _ _ _ = refl

----------------------------------------------------------------------
-- Narrowing shrinks the honest fibre count.
----------------------------------------------------------------------

-- Decidable equality on pairs from decidable equality on the components.
dec-× :
  ((b₁ b₂ : B) → Dec (b₁ ≡ b₂)) →
  ((c₁ c₂ : C) → Dec (c₁ ≡ c₂)) →
  (p q : B × C) → Dec (p ≡ q)
dec-× _≟B_ _≟C_ (b , c) (b′ , c′) with b ≟B b′ | c ≟C c′
... | yes refl | yes refl = yes refl
... | yes _    | no ¬q    = no (λ e → ¬q (cong proj₂ e))
... | no ¬p    | yes _    = no (λ e → ¬p (cong proj₁ e))
... | no ¬p    | no _     = no (λ e → ¬p (cong proj₁ e))

private
  ≤-step : ∀ {m n} → m ≤ n → m ≤ ℕ.suc n
  ≤-step z≤n     = z≤n
  ≤-step (s≤s p) = s≤s (≤-step p)

-- Headline 4: adding an observation never enlarges the enumerated
-- candidate fibre. Walks the `FiberSize-fin` recursion on both sides in
-- lock-step: a hit for the pair is a hit for `f`; a hit for `f` alone
-- is a candidate the extra observation has ruled out.
narrow-shrinks :
  ∀ {n} (f : Fin n → B) (g : Fin n → C) (y : B) (z : C)
  (_≟B_ : (b₁ b₂ : B) → Dec (b₁ ≡ b₂))
  (_≟C_ : (c₁ c₂ : C) → Dec (c₁ ≡ c₂)) →
  FiberSize-fin < f , g > (y , z) (dec-× _≟B_ _≟C_) ≤ FiberSize-fin f y _≟B_
narrow-shrinks {n = ℕ.zero}  f g y z _≟B_ _≟C_ = z≤n
narrow-shrinks {n = ℕ.suc m} f g y z _≟B_ _≟C_
  with f zero ≟B y | dec-× _≟B_ _≟C_ (< f , g > zero) (y , z)
... | yes _  | yes _ = s≤s (narrow-shrinks (f ∘ suc) (g ∘ suc) y z _≟B_ _≟C_)
... | yes _  | no _  = ≤-step (narrow-shrinks (f ∘ suc) (g ∘ suc) y z _≟B_ _≟C_)
... | no ¬p  | yes q = ⊥-elim (¬p (cong proj₁ q))
... | no _   | no _  = narrow-shrinks (f ∘ suc) (g ∘ suc) y z _≟B_ _≟C_

----------------------------------------------------------------------
-- Companion remark.
--
-- What is deliberately NOT claimed:
--
--   * Inhabitation. `Narrow f g y z` may be empty; joint observations
--     can be inconsistent. squeakwell reports that as an empty
--     candidate fibre, routed to review (rung R13), not as a theorem.
--   * Covering ⇒ subsingleton. The survey's "if the observed masks
--     cover every modality the fibre is a subsingleton" needs equality
--     of full sections from pointwise equality, i.e. extensionality, and
--     opaque identifiers. Dropped in the route plan; not here.
--   * A `_↔_` for the `Fin n` family step. The pointwise maps exist and
--     preserve the witness; the function-side round trip would need
--     funext and is left out rather than taken as a hypothesis.
----------------------------------------------------------------------
