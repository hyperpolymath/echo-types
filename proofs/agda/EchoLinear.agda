{-# OPTIONS --safe --without-K #-}

module EchoLinear where

open import Echo
open import EchoCharacteristic using (collapse; echo-true; echo-false; echo-true≢echo-false)
open import EchoResidue
  using
    ( EchoR
    ; TrivialCert
    ; collapse-to-residue
    ; collapse-residue-same
    ; no-section-collapse-to-residue
    )

open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

data Mode : Set where
  linear : Mode
  affine : Mode

LEcho : Mode → Set
LEcho linear = Echo collapse tt
LEcho affine = EchoR ⊤ TrivialCert tt

weaken : LEcho linear → LEcho affine
weaken = collapse-to-residue

weaken-collapses-distinction : weaken echo-true ≡ weaken echo-false
weaken-collapses-distinction = collapse-residue-same

strict-linear-example :
  Σ (LEcho linear)
    (λ e1 → Σ (LEcho linear) (λ e2 → e1 ≢ e2 × weaken e1 ≡ weaken e2))
strict-linear-example = echo-true , echo-false , echo-true≢echo-false , collapse-residue-same

no-section-weaken :
  ¬ (Σ (LEcho affine → LEcho linear)
       (λ raise → ∀ e → raise (weaken e) ≡ e))
no-section-weaken = no-section-collapse-to-residue

affine-canonical : ∀ (e : LEcho affine) → e ≡ (tt , tt)
affine-canonical (tt , tt) = refl

affine-all-equal : ∀ (e1 e2 : LEcho affine) → e1 ≡ e2
affine-all-equal e1 e2 = trans (affine-canonical e1) (sym (affine-canonical e2))

-- Per-decoration composition lemma.
--
-- Mirrors `EchoGraded.degrade-comp` for the two-mode (linear ⊑ affine)
-- linearity decoration: weakening between modes commutes with
-- transitive composition of the mode-ordering. See
-- docs/echo-types/composition.md §6 (decoration commuting) and
-- docs/echo-types/roadmap.md "Per-decoration composition lemmas".
--
-- The mode ordering is the smallest reflexive-and-`linear≤affine`
-- relation: linear ⊑ linear, linear ⊑ affine, affine ⊑ affine. The
-- weakening `degradeMode` reuses `weaken` for the strict step and
-- the identity on the reflexive cases. Composition then closes
-- definitionally on every constructor pair, exactly as in
-- `EchoGraded.degrade-comp`.

data _≤m_ : Mode → Mode → Set where
  linear≤linear : linear ≤m linear
  linear≤affine : linear ≤m affine
  affine≤affine : affine ≤m affine

≤m-trans : ∀ {m1 m2 m3} → m1 ≤m m2 → m2 ≤m m3 → m1 ≤m m3
≤m-trans linear≤linear p23 = p23
≤m-trans linear≤affine affine≤affine = linear≤affine
≤m-trans affine≤affine affine≤affine = affine≤affine

degradeMode : ∀ {m1 m2} → m1 ≤m m2 → LEcho m1 → LEcho m2
degradeMode linear≤linear e = e
degradeMode linear≤affine e = weaken e
degradeMode affine≤affine e = e

-- Headline per-decoration composition lemma: two successive mode
-- weakenings agree with a single weakening along the composed
-- ordering proof.
degradeMode-comp :
  ∀ {m1 m2 m3}
  (p12 : m1 ≤m m2)
  (p23 : m2 ≤m m3)
  (e : LEcho m1) →
  degradeMode p23 (degradeMode p12 e) ≡ degradeMode (≤m-trans p12 p23) e
degradeMode-comp linear≤linear p23 e = refl
degradeMode-comp linear≤affine affine≤affine e = refl
degradeMode-comp affine≤affine affine≤affine e = refl

-- Identity weakening corollary: degrading along a reflexive proof
-- is the identity. Useful when chaining with `degradeMode-comp`.
degradeMode-id-linear : ∀ (e : LEcho linear) → degradeMode linear≤linear e ≡ e
degradeMode-id-linear _ = refl

degradeMode-id-affine : ∀ (e : LEcho affine) → degradeMode affine≤affine e ≡ e
degradeMode-id-affine _ = refl

-- The strict mode step `degradeMode linear≤affine` agrees with
-- `weaken` definitionally, so the existing strict-weakening
-- non-recoverability witness extends to `degradeMode`.
degradeMode-strict-is-weaken :
  ∀ (e : LEcho linear) → degradeMode linear≤affine e ≡ weaken e
degradeMode-strict-is-weaken _ = refl

-- Propositionality of the mode order. Each ordered pair `(m1, m2)`
-- has at most one inhabitant in `_≤m_` — this is the linearity-side
-- analogue of `EchoGraded.≤g-prop` and is what lets us collapse a
-- `(≤m-trans p12 p23)`-shaped composition proof against an
-- independently-given `p13 : m1 ≤m m3` in `degradeMode-compose`.
≤m-prop : ∀ {m1 m2} (p p' : m1 ≤m m2) → p ≡ p'
≤m-prop linear≤linear linear≤linear = refl
≤m-prop linear≤affine linear≤affine = refl
≤m-prop affine≤affine affine≤affine = refl

-- Join on Mode. `affine` is top, so `_⊔m_` is determined by `m1`.
_⊔m_ : Mode → Mode → Mode
linear ⊔m m2 = m2
affine ⊔m _ = affine

-- Join is the categorical least-upper-bound in `_≤m_`: two upper
-- bounds (`≤m-⊔m-left`, `≤m-⊔m-right`) and a universal property
-- (`≤m-⊔m-univ`). Mirrors `EchoGraded.≤g-⊔g-{left, right, univ}`.

≤m-⊔m-left : ∀ m1 m2 → m1 ≤m (m1 ⊔m m2)
≤m-⊔m-left linear linear = linear≤linear
≤m-⊔m-left linear affine = linear≤affine
≤m-⊔m-left affine linear = affine≤affine
≤m-⊔m-left affine affine = affine≤affine

≤m-⊔m-right : ∀ m1 m2 → m2 ≤m (m1 ⊔m m2)
≤m-⊔m-right linear linear = linear≤linear
≤m-⊔m-right linear affine = affine≤affine
≤m-⊔m-right affine linear = linear≤affine
≤m-⊔m-right affine affine = affine≤affine

≤m-⊔m-univ :
  ∀ {m1 m2 m3} → m1 ≤m m3 → m2 ≤m m3 → (m1 ⊔m m2) ≤m m3
≤m-⊔m-univ linear≤linear p2 = p2
≤m-⊔m-univ linear≤affine p2 = p2
≤m-⊔m-univ affine≤affine _ = affine≤affine

-- Free-factoring composition law: any direct ordering proof
-- `p13 : m1 ≤m m3` agrees with the composed-via-`m2` weakening,
-- because `≤m-prop` makes the choice of factoring irrelevant.
-- Linearity-side analogue of `EchoGraded.degrade-compose`.
degradeMode-compose :
  ∀ {m1 m2 m3}
  (p12 : m1 ≤m m2)
  (p23 : m2 ≤m m3)
  (p13 : m1 ≤m m3)
  (e : LEcho m1) →
  degradeMode p23 (degradeMode p12 e) ≡ degradeMode p13 e
degradeMode-compose p12 p23 p13 e
  rewrite ≤m-prop p13 (≤m-trans p12 p23) = degradeMode-comp p12 p23 e

-- Same statement restated through the join structure: any
-- weakening to a common upper bound `m3` factors through the
-- `m1 ⊔m m2` join. Linearity-side analogue of
-- `EchoGraded.degrade-via-join`.
degradeMode-via-join :
  ∀ {m1 m2 m3}
  (p1 : m1 ≤m m3)
  (p2 : m2 ≤m m3)
  (e : LEcho m1) →
  degradeMode p1 e
  ≡ degradeMode (≤m-⊔m-univ p1 p2) (degradeMode (≤m-⊔m-left m1 m2) e)
degradeMode-via-join {m1} {m2} p1 p2 e =
  sym (degradeMode-compose (≤m-⊔m-left m1 m2) (≤m-⊔m-univ p1 p2) p1 e)
