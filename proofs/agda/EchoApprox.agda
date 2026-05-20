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
--   * echo-approx-intro          -- exact own-fibre match is zero-tolerance
--   * echo-strict→approx         -- general strict ⇒ zero-tolerance (any y)
--   * echo-approx-relax          -- ε is monotone: ε₁ ≤ ε₂ ⇒ EchoR ε₁ ⊑ EchoR ε₂
--   * echo-approx-compose        -- non-expansive composition with additive
--                                   error, realising the taxonomy §2 conjecture
--   * echo-approx-comp-sound     -- repackages compose into the retract RHS-Σ
--                                   shape from `composition.md` §Q3 (§5 of the
--                                   axis-2 design note)
--   * echo-approx-comp-retract-to  -- canonical-split LHS → RHS section:
--                                     picks b := f x, ε₁ := zero, ε₂ := ε
--   * echo-approx-comp-retract-A   -- A-component round-trip (sound ∘ retract-to)
--                                     preserves the A-witness up to `refl`,
--                                     witnessing the retraction direction
--                                     definitionally
--
-- The non-expansiveness side condition on the outer leg is the
-- minimal hypothesis under which tolerances accumulate additively;
-- without it the conjecture has no general proof (an amplifying
-- second leg can blow ε₁ up arbitrarily on the way through).
--
-- Composition-track context (§5 of the axis-2 design note,
-- `/tmp/echo-types-exploration/axis2-approximate.md`). The approximate
-- analogue of `Echo-comp-iso` is a *retraction*, not a strict
-- isomorphism: the RHS Σ-shape admits multiple splits of the ε
-- budget and the chosen intermediate `b` is not pinned by the input.
-- This module ships the first slice of that retract — soundness (#6),
-- the canonical-split forward section, and an A-component round-trip
-- witness. The B-component round-trip and the full tolerance round-trip
-- need a `+`-left-identity axiom on `Tolerance` (`zero + ε ≡ ε`, not
-- currently in the record); §7 obligations 7 (zero-collapse under
-- separation) and 8 (axis-1 shadow agreement) are deferred to
-- subsequent rungs.

module EchoApprox where

open import Level                                 using (Level; _⊔_; suc)
open import Function.Base                         using (_∘_; id)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Echo                                  using (Echo)

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
  -- Headline 1ʹ: general strict ⇒ zero-tolerance approximate.
  --
  -- Realises §7 obligation 2 of the axis-2 design note: every strict
  -- echo `Echo f y` lifts to a zero-tolerance approximate echo
  -- `EchoR zero f y` (any y, not just own-fibre points). When `y ≡ f x`
  -- with `p ≡ refl` this collapses to `echo-approx-intro`; otherwise
  -- the codomain equation `p : f x ≡ y` is used to transport the
  -- self-distance bound from `(f x, f x)` to `(f x, y)`.
  --
  -- This generalises `echo-approx-intro` from own-fibre points
  -- `(f x)` to arbitrary `y` reached via a strict echo. The cost of
  -- the generalisation is one extra `subst` along `p`.
  ----------------------------------------------------------------------

  echo-strict→approx :
    ∀ {f : A → B} {y : B} → Echo f y → EchoR zero f y
  echo-strict→approx {f = f} (x , p) =
    x , subst (λ z → dist (f x) z ≤ zero)
              p
              (subst (_≤ zero) (sym (dist-self (f x))) ≤-refl)

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

  ----------------------------------------------------------------------
  -- Retraction-shaped composition (composition.md §Q3 / design-note §5).
  --
  -- The approximate analogue of `Echo-comp-iso` is *retract-shaped*:
  --
  --   LHS  := EchoR ε (g ∘ f) y
  --   RHS  := Σ B (λ b → EchoR ε₁ f b × dist (g b) y ≤ ε₂)
  --
  -- with the budget split `ε = ε₁ + ε₂`. The RHS admits multiple
  -- splits of the budget and the chosen intermediate `b` is not
  -- pinned by the input, so a full iso fails by design. What does
  -- hold is a retraction: a forward section that picks a canonical
  -- representative on the RHS and a backward map (`echo-approx-comp-sound`,
  -- a thin repackaging of `echo-approx-compose`) that round-trips
  -- the A-witness definitionally.
  --
  -- This block lands the first slice: soundness (#6), the canonical-
  -- split forward section, and the A-component round-trip. The
  -- B-component and tolerance-budget round-trips need a `+`-left-
  -- identity axiom on `Tolerance` (`zero + ε ≡ ε`, not in the record).
  ----------------------------------------------------------------------

  -- §7 obligation 6: sound RHS-to-LHS direction.
  -- Unpacks the existential and calls `echo-approx-compose`.
  echo-approx-comp-sound :
    ∀ {ε₁ ε₂ : Tol}
    (f : A → B) (g : B → B) →
    NonExpansive g →
    ∀ {y : B} →
    Σ B (λ b → EchoR ε₁ f b × dist (g b) y ≤ ε₂) →
    EchoR (ε₁ + ε₂) (g ∘ f) y
  echo-approx-comp-sound f g g-nonexp (b , ef , dgby≤ε₂) =
    echo-approx-compose f g g-nonexp {b = b} ef dgby≤ε₂

  -- Canonical-split LHS-to-RHS section of the retract.
  --
  -- Given an `EchoR ε (g ∘ f) y` witness `(x , p : dist (g (f x)) y ≤ ε)`,
  -- produce the RHS Σ-shape at the canonical split `(ε₁, ε₂) := (zero, ε)`:
  --
  --   * intermediate `b := f x` (the canonical lift),
  --   * inner echo `EchoR zero f (f x)` via `echo-approx-intro`,
  --   * outer bound is just the original `p`.
  --
  -- This is the "section" half of the retract: a one-sided splitting
  -- of the §Q3 conjecture that always exists, with no extra hypothesis
  -- beyond what `EchoR ε (g ∘ f) y` already supplies. The "wrong"
  -- intermediates are not enumerable, which is precisely why the
  -- approximate analogue is a retract and not a full iso.
  echo-approx-comp-retract-to :
    ∀ {ε : Tol} (f : A → B) (g : B → B) {y : B} →
    EchoR ε (g ∘ f) y →
    Σ B (λ b → EchoR zero f b × dist (g b) y ≤ ε)
  echo-approx-comp-retract-to f g (x , dgfx≤ε) =
    f x , echo-approx-intro f x , dgfx≤ε

  -- A-component round-trip. Starting from an `EchoR ε (g ∘ f) y`,
  -- pushing through the canonical-split section then through
  -- soundness lands back on the *same A-witness `x`* (the tolerance
  -- budget weakens from `ε` to `zero + ε`, which is why this is a
  -- retraction in the A-component rather than a full equality of
  -- echoes). The proof is `refl` — the A-component is preserved
  -- definitionally because every step of the round-trip keeps
  -- `proj₁` pinned to the original `x`.
  --
  -- This pins the "retract direction holds definitionally" promise
  -- of the design note: the witness-on-A round-trips on the nose,
  -- even though the tolerance and intermediate-B components do not.
  echo-approx-comp-retract-A :
    ∀ {ε : Tol} (f : A → B) (g : B → B) (g-nonexp : NonExpansive g)
    {y : B} (e : EchoR ε (g ∘ f) y) →
    proj₁ (echo-approx-comp-sound f g g-nonexp
            (echo-approx-comp-retract-to f g e))
    ≡ proj₁ e
  echo-approx-comp-retract-A f g g-nonexp (x , _) = refl
