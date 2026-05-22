{-# OPTIONS --safe --without-K #-}

-- Pillar A of docs/echo-types/establishment-plan.adoc.
--
-- `Echo f y` is *definitionally* the homotopy fibre of `f` at `y`
-- (HoTT book Def. 4.2.4). The gate-1 distinctness argument states
-- this in prose; this module turns it into a machine-checked
-- artefact. The bijection is the identity with `refl` round-trips —
-- that triviality is the entire point. Formalising the project's own
-- deflationary admission ("Echo adds no new object; it *is* fib") is
-- a credibility asset, not a redundancy: it pins the identity so the
-- universal-property work (Pillar B) builds on a stated, not
-- asserted, foundation.

module Echo.Bridges.EchoFiberBridge where

open import Echo.Core using (Echo)

open import Level using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function.Bundles using (_↔_; mk↔ₛ′)

-- The homotopy fibre of `f` at `y`, in its standard MLTT / HoTT form:
-- a point of the domain together with a proof that `f` sends it to
-- `y`. The agda-stdlib (v2.3) ships no `fiber`, so it is defined here
-- precisely so the bridge below is honest about being definitional.
fiber : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → B → Set (a ⊔ b)
fiber {A = A} f y = Σ A (λ x → f x ≡ y)

-- Echo IS the homotopy fibre. Not "equivalent up to homotopy" —
-- definitionally equal, so both directions are the identity.
echo→fib :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) →
  Echo f y → fiber f y
echo→fib _ _ e = e

fib→echo :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) →
  fiber f y → Echo f y
fib→echo _ _ e = e

-- The bijection, packaged via stdlib's `Function.Bundles._↔_` and
-- `mk↔ₛ′` — the same equivalence-record convention used throughout
-- `Echo.agda` (`Echo-comp-iso`, `cancel-iso`). Both round-trips are
-- `refl`: there is no path algebra here because there is no gap to
-- bridge.
echo↔fib :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) →
  Echo f y ↔ fiber f y
echo↔fib f y =
  mk↔ₛ′
    (echo→fib f y)
    (fib→echo f y)
    (λ _ → refl)
    (λ _ → refl)
