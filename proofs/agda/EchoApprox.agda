{-# OPTIONS --safe --without-K #-}

-- ε-indexed approximate echoes over a (pseudo-)metric codomain.
--
-- Axis-2 first artifact (`docs/echo-types/taxonomy.md` §2):
--
--   EchoR ε f y := Σ A (λ x → dist (f x) y ≤ ε)
--
-- where `dist` is a pseudo-metric on the codomain `B` and `ε` lives
-- in an ordered tolerance monoid. The exact echo `Echo f y = Σ A (λ x →
-- f x ≡ y)` lifts into `EchoR zero f y` via reflexivity of `dist`.
--
-- Headline lemmas:
--
--   * echo-approx-intro    -- exact match is a zero-tolerance approximate echo
--   * echo-approx-relax    -- ε is monotone: ε₁ ≤ ε₂ ⇒ EchoR ε₁ ⊑ EchoR ε₂
--   * echo-approx-compose  -- non-expansive composition with additive error,
--                             realising the taxonomy §2 conjecture
--
-- The non-expansiveness side condition on the outer leg is the
-- minimal hypothesis under which tolerances accumulate additively;
-- without it the conjecture has no general proof (an amplifying
-- second leg can blow ε₁ up arbitrarily on the way through).

module EchoApprox where

open import Level                                 using (Level; _⊔_; suc)
open import Function.Base                         using (_∘_; id)
open import Data.Product.Base                     using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

----------------------------------------------------------------------
-- Tolerance carrier and pseudo-metric structure
----------------------------------------------------------------------

-- A tolerance carrier is an ordered commutative-monoid-flavoured type
-- with just enough structure to state additive composition:
-- transitive `≤`, reflexivity at every point, and a binary `+` that
-- is monotone on each side.

record Tolerance ℓ : Set (suc ℓ) where
  infix 4 _≤_
  infixl 6 _+_
  field
    Tol      : Set ℓ
    zero     : Tol
    _+_      : Tol → Tol → Tol
    _≤_      : Tol → Tol → Set ℓ
    ≤-refl   : ∀ {ε}             → ε ≤ ε
    ≤-trans  : ∀ {ε₁ ε₂ ε₃}      → ε₁ ≤ ε₂ → ε₂ ≤ ε₃ → ε₁ ≤ ε₃
    +-mono-≤ : ∀ {a b c d}       → a ≤ b → c ≤ d → (a + c) ≤ (b + d)

-- A pseudo-metric on `B` valued in a tolerance carrier `T`. Self-distance
-- is zero (definitionally) and the triangle inequality holds. We do not
-- demand symmetry or separation here; both can be added later if needed.

record PseudoMetric {b ℓ} (B : Set b) (T : Tolerance ℓ) : Set (b ⊔ ℓ) where
  open Tolerance T
  field
    dist      : B → B → Tol
    dist-self : ∀ y         → dist y y ≡ zero
    dist-tri  : ∀ b₁ b₂ b₃  → dist b₁ b₃ ≤ (dist b₁ b₂ + dist b₂ b₃)

----------------------------------------------------------------------
-- Approximate echo
----------------------------------------------------------------------

module Approx
  {a b ℓ} {A : Set a} {B : Set b} {T : Tolerance ℓ}
  (M : PseudoMetric B T)
  where

  open Tolerance    T
  open PseudoMetric M

  -- EchoR ε f y: a witness x : A whose image f x lies within ε of y.
  EchoR : Tol → (A → B) → B → Set (a ⊔ ℓ)
  EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)

  ----------------------------------------------------------------------
  -- Headline 1: exact match ⇒ zero-tolerance approximate match.
  --
  -- Lifts the constructor of `Echo` (`x , refl`) into the metric setting
  -- with no tolerance budget consumed. The proof rewrites `dist (f x)
  -- (f x)` to `zero` via `dist-self` and then uses `≤-refl` at zero.
  ----------------------------------------------------------------------

  echo-approx-intro : (f : A → B) (x : A) → EchoR zero f (f x)
  echo-approx-intro f x =
    x , subst (_≤ zero) (sym (dist-self (f x))) ≤-refl

  ----------------------------------------------------------------------
  -- Headline 2: tolerance is monotone in `ε`. A tighter approximation
  -- is also a looser one. The proof is one transitivity step.
  ----------------------------------------------------------------------

  echo-approx-relax :
    ∀ {ε₁ ε₂ : Tol} {f : A → B} {y : B} →
    ε₁ ≤ ε₂ → EchoR ε₁ f y → EchoR ε₂ f y
  echo-approx-relax ε₁≤ε₂ (x , dfx≤ε₁) = x , ≤-trans dfx≤ε₁ ε₁≤ε₂

  ----------------------------------------------------------------------
  -- Headline 3: additive composition under non-expansiveness.
  --
  -- Realises the taxonomy §2 conjecture
  --   "ε₁-echo(f) + ε₂-echo(g) ⊑ (ε₁ + ε₂)-echo(g ∘ f)".
  --
  -- Form: an ε₁-echo of `f` at some intermediate `b`, plus a bound
  -- `dist (g b) y ≤ ε₂`, plus non-expansiveness of `g`, yields an
  -- (ε₁ + ε₂)-echo of `g ∘ f` at `y`.
  --
  -- Outer leg `g` is endomorphic (`B → B`) so that we stay inside the
  -- single supplied metric. A two-metric version is straightforward
  -- but adds bureaucracy without changing the argument.
  ----------------------------------------------------------------------

  NonExpansive : (B → B) → Set (b ⊔ ℓ)
  NonExpansive g = ∀ b₁ b₂ → dist (g b₁) (g b₂) ≤ dist b₁ b₂

  echo-approx-compose :
    ∀ {ε₁ ε₂ : Tol}
    (f : A → B) (g : B → B) →
    NonExpansive g →
    ∀ {b y : B} →
    EchoR ε₁ f b →
    dist (g b) y ≤ ε₂ →
    EchoR (ε₁ + ε₂) (g ∘ f) y
  echo-approx-compose {ε₁} {ε₂} f g g-nonexp {b} {y} (x , dfx≤ε₁) dgby≤ε₂ =
    x , bound
    where
    -- triangle: dist (g (f x)) y ≤ dist (g (f x)) (g b) + dist (g b) y
    leg : dist (g (f x)) y ≤ (dist (g (f x)) (g b) + dist (g b) y)
    leg = dist-tri (g (f x)) (g b) y

    -- non-expansiveness contracts the f-side residue, additive monotonicity
    -- carries it through the triangle bound.
    contract : (dist (g (f x)) (g b) + dist (g b) y) ≤ (ε₁ + ε₂)
    contract = +-mono-≤ (≤-trans (g-nonexp (f x) b) dfx≤ε₁) dgby≤ε₂

    bound : dist (g (f x)) y ≤ (ε₁ + ε₂)
    bound = ≤-trans leg contract
