{-# OPTIONS --safe --without-K #-}

-- Echo non-propositionality from non-injective fibres.
--
-- Strengthens the truncation argument (one of the two load-bearing
-- distinctness arguments post-EI-2) by formalising once-and-for-all
-- the lemma that several example modules currently prove pointwise:
--
--   * `EchoCharacteristic.echo-true≢echo-false`     (collapse : Bool → ⊤)
--   * `EchoExamples.echo-plus3≢echo-minus3`         (square9 : SignedNine → ℕ)
--   * `EchoTropical.echo-a≢echo-b`                  (score   : Candidate → ℕ)
--
-- All three witness the same fact: a non-injective `f : A → B` with
-- two distinct preimages of some `y` produces a non-propositional
-- `Echo f y`. This module proves that fact for an arbitrary `f` and
-- recovers each existing pointwise lemma as a corollary.

module EchoTruncation where

open import Echo

open import Level using (Level)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

private
  variable
    ℓa ℓb : Level
    A : Set ℓa
    B : Set ℓb

-- A type is propositional ("a mere proposition") when any two
-- inhabitants are equal. Standard HoTT terminology, kept universe-
-- polymorphic so call sites need no level juggling.
isProp : ∀ {ℓ} (T : Set ℓ) → Set ℓ
isProp T = (x y : T) → x ≡ y

----------------------------------------------------------------------
-- Generic distinctness lemmas.

-- Two echoes whose underlying witnesses are distinct are themselves
-- distinct. The load-bearing step is `cong proj₁`, factoring through
-- `Σ` rather than `Echo`, so the lemma works at any level and for
-- any non-injective f. This encapsulates the `λ q → ne (cong proj₁ q)`
-- fragment that recurs across every example module.
echo-witnesses-distinct :
  {f : A → B} {y : B} {e1 e2 : Echo f y} →
  proj₁ e1 ≢ proj₁ e2 →
  e1 ≢ e2
echo-witnesses-distinct ne q = ne (cong proj₁ q)

-- From two distinct preimages of `y`, exhibit two distinct echoes
-- at `y`. Witness/existential form: more useful than `echo-not-prop`
-- when one wants the actual elements rather than just the negation.
preimages⇒distinct-echoes :
  (f : A → B) {y : B}
  (x1 x2 : A) (p1 : f x1 ≡ y) (p2 : f x2 ≡ y) →
  x1 ≢ x2 →
  Σ (Echo f y) (λ e1 → Σ (Echo f y) (λ e2 → e1 ≢ e2))
preimages⇒distinct-echoes f {y = y} x1 x2 p1 p2 ne =
  e1 , e2 ,
    echo-witnesses-distinct {f = f} {y = y} {e1 = e1} {e2 = e2} ne
  where
    e1 : Echo f y
    e1 = x1 , p1
    e2 : Echo f y
    e2 = x2 , p2

-- Headline: `Echo f y` is not a proposition whenever `f` has two
-- distinct preimages of `y`. The general post-EI-2 truncation
-- argument formalised once; per-example lemmas follow as corollaries
-- below.
echo-not-prop :
  (f : A → B) {y : B}
  (x1 x2 : A) (p1 : f x1 ≡ y) (p2 : f x2 ≡ y) →
  x1 ≢ x2 →
  ¬ isProp (Echo f y)
echo-not-prop f x1 x2 p1 p2 ne prop =
  ne (cong proj₁ (prop (x1 , p1) (x2 , p2)))

----------------------------------------------------------------------
-- Corollaries: each pre-existing pointwise distinctness lemma is a
-- special case of `echo-witnesses-distinct` / `echo-not-prop`.

-- Substitution note: the bootstrapping brief named the carrier
-- modules `TropicalArgmin.agda`, `EpistemicUpdate.agda`, and
-- `LinearErasure.agda`. Those files do not exist under those names;
-- the closest existing carriers of pointwise echo-distinctness for
-- non-injective f are `EchoTropical`, `EchoCharacteristic`, and
-- `EchoExamples`. The corollaries below use the latter set.

-- 1. `collapse : Bool → ⊤` (the maximally collapsing example).
module CollapseExample where
  open import Data.Bool.Base using (Bool; true; false)
  open import Data.Unit.Base using (⊤; tt)
  open import EchoCharacteristic using
    (collapse; echo-true; echo-false; true≢false)

  echo-true≢echo-false : echo-true ≢ echo-false
  echo-true≢echo-false =
    echo-witnesses-distinct
      {f = collapse} {y = tt}
      {e1 = echo-true} {e2 = echo-false}
      true≢false

  collapse-not-prop : ¬ isProp (Echo collapse tt)
  collapse-not-prop =
    echo-not-prop collapse true false refl refl true≢false

-- 2. `square9 : SignedNine → ℕ` (sign-forgetting square).
module Square9Example where
  open import Data.Nat.Base using (ℕ)
  open import EchoExamples using
    (SignedNine; plus3; minus3; plus3≢minus3; square9;
     echo-plus3; echo-minus3)

  echo-plus3≢echo-minus3 : echo-plus3 ≢ echo-minus3
  echo-plus3≢echo-minus3 =
    echo-witnesses-distinct
      {f = square9} {y = 9}
      {e1 = echo-plus3} {e2 = echo-minus3}
      plus3≢minus3

  square9-not-prop : ¬ isProp (Echo square9 9)
  square9-not-prop =
    echo-not-prop square9 plus3 minus3 refl refl plus3≢minus3

-- 3. `score : Candidate → ℕ` (tropical / argmin scoring).
module TropicalExample where
  open import Data.Nat.Base using (ℕ; zero)
  open import EchoTropical using
    (Candidate; a; b; a≢b; score; echo-a; echo-b)

  echo-a≢echo-b : echo-a ≢ echo-b
  echo-a≢echo-b =
    echo-witnesses-distinct
      {f = score} {y = zero}
      {e1 = echo-a} {e2 = echo-b}
      a≢b

  tropical-score-not-prop : ¬ isProp (Echo score zero)
  tropical-score-not-prop =
    echo-not-prop score a b refl refl a≢b
