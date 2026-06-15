{-# OPTIONS --cubical --safe #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Cubical (REAL) counterpart of `EchoImageFactorizationPropPostulated`.
--
-- ## Purpose
--
-- `EchoImageFactorizationPropPostulated` exhibits the (epi, mono)
-- image factorisation by ASSUMING propositional truncation `∥_∥` via
-- four `postulate`s realising `TruncInterface`.  Per the estate
-- Trusted-Base Reduction Policy (`docs/proof-debt.md`) that module is
-- item (c) "necessary axiom": `∥_∥` cannot be CONSTRUCTED in `--safe
-- --without-K` without higher inductive types.
--
-- This module DISCHARGES that axiom.  In the `--cubical` profile the
-- propositional truncation is a genuine higher inductive type, so the
-- four interface obligations become THEOREMS (zero postulates), and
-- the (epi, mono) factorisation is a real proof rather than a
-- consequence of assumed laws.  `grep postulate` here returns nothing.
--
-- ## Why self-contained (not an import of the `--without-K` base)
--
-- Agda forbids a `--cubical` module from importing a module that is
-- `--without-K` but not `--cubical-compatible`.  The `Echo` kernel
-- cone (and `EchoImageFactorizationProp`) is `--safe --without-K`, and
-- re-flagging it to `--cubical-compatible` would change the
-- kernel-guard funext-free certificate (`scripts/kernel-guard.sh`
-- Check A greps for the literal `--safe --without-K`).  So this module
-- RESTATES the minimal pieces locally — `TruncInterface`, `Echo`,
-- `echo-intro`, and the `ImageProp` content — each definitionally
-- identical to its `--safe --without-K` original.  Only the flag
-- island differs; the mathematical content is the same.
--
-- ## What lands (all postulate-free, `--cubical --safe`)
--
--   * `∥_∥`             — the propositional-truncation HIT.
--   * `is-prop-∥∥`, `rec-∥∥` — the propositionality + recursor,
--     proved (not assumed): `is-prop-∥∥` is `squash` transported to
--     the inductive `_≡_`; `rec-∥∥`'s higher-constructor case closes
--     by the cubical endpoint rule on the converted path.
--   * `trunc-cubical : TruncInterface ℓ` — the four obligations,
--     packaged as the SAME record shape the postulated module fakes.
--   * `module ImagePropCubical f` — the (epi, mono) factorisation
--     instantiated at `trunc-cubical`:
--       - `prop-factor-right-injective-real` — MONO side (real).
--       - `prop-factor-left-mere-surjective-real` — EPI side (real).
--
-- ## Headlines (cubical-lane; see `Cubical/All.agda`)
--
--   * `trunc-cubical`
--   * `prop-factor-right-injective-real`
--   * `prop-factor-left-mere-surjective-real`

module EchoImageFactorizationPropCubical where

open import Level                      using (Level; suc)
open import Agda.Primitive.Cubical     using (i0; primTransp)
open import Agda.Builtin.Cubical.Path  using (PathP)
open import Data.Product.Base          using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
                                       using (_≡_; refl; cong)

private variable
  ℓ : Level

----------------------------------------------------------------------
-- Cubical propositional truncation — the construction the postulates
-- only asserted
----------------------------------------------------------------------

-- homogeneous cubical path (kept distinct from the inductive `_≡_`)
_≡ᶜ_ : {A : Set ℓ} → A → A → Set ℓ
_≡ᶜ_ {A = A} x y = PathP (λ _ → A) x y

-- the (-1)-truncation as a higher inductive type
data ∥_∥ (A : Set ℓ) : Set ℓ where
  inc    : A → ∥ A ∥
  squash : (x y : ∥ A ∥) → x ≡ᶜ y

-- inductive-`≡` ↔ cubical-path, both with definitional endpoints
eqToPath : {A : Set ℓ} {x y : A} → x ≡ y → x ≡ᶜ y
eqToPath {x = x} refl = λ _ → x

pathToEq : {A : Set ℓ} {x y : A} → x ≡ᶜ y → x ≡ y
pathToEq {x = x} p = primTransp (λ i → x ≡ p i) i0 refl

----------------------------------------------------------------------
-- The four `TruncInterface` obligations, REAL (no postulates)
----------------------------------------------------------------------

-- propositionality: `squash` is a path; transport it to inductive `_≡_`
is-prop-∥∥ : {A : Set ℓ} (x y : ∥ A ∥) → x ≡ y
is-prop-∥∥ x y = pathToEq (squash x y)

-- recursion into an inductive-`≡` proposition.  The higher-constructor
-- case lands on a converted path; its `i0`/`i1` boundary reduces to
-- `rec-∥∥ … x` / `rec-∥∥ … y` definitionally (cubical endpoint rule),
-- so the clause is well-formed.
rec-∥∥ : {A B : Set ℓ} → ((x y : B) → x ≡ y) → (A → B) → ∥ A ∥ → B
rec-∥∥ pB f (inc a)        = f a
rec-∥∥ pB f (squash x y i) = eqToPath (pB (rec-∥∥ pB f x) (rec-∥∥ pB f y)) i

----------------------------------------------------------------------
-- `TruncInterface` (local restatement, identical to
-- `EchoImageFactorizationProp.TruncInterface`) + its REAL instance
----------------------------------------------------------------------

record TruncInterface (ℓ : Level) : Set (suc ℓ) where
  field
    Trunc   : Set ℓ → Set ℓ
    ∣_∣     : ∀ {A : Set ℓ} → A → Trunc A
    is-prop : ∀ {A : Set ℓ} (x y : Trunc A) → x ≡ y
    rec     : ∀ {A B : Set ℓ}
              → ((x y : B) → x ≡ y)
              → (A → B)
              → Trunc A → B

-- the discharge: the postulated `trunc` becomes a real instance
trunc-cubical : TruncInterface ℓ
trunc-cubical = record
  { Trunc   = ∥_∥
  ; ∣_∣     = inc
  ; is-prop = is-prop-∥∥
  ; rec     = rec-∥∥
  }

----------------------------------------------------------------------
-- Local `Echo` (definitionally identical to `Echo.Echo`) + intro
----------------------------------------------------------------------

Echo : {A B : Set ℓ} → (A → B) → B → Set ℓ
Echo {A = A} f y = Σ A (λ x → f x ≡ y)

echo-intro : {A B : Set ℓ} (f : A → B) (x : A) → Echo f (f x)
echo-intro f x = x , refl

----------------------------------------------------------------------
-- The (epi, mono) factorisation, parametric in `TruncInterface`
-- (restated from `EchoImageFactorizationProp.ImageProp`)
----------------------------------------------------------------------

module ImageProp {A B : Set ℓ} (T : TruncInterface ℓ) (f : A → B) where
  open TruncInterface T

  Image-prop : Set ℓ
  Image-prop = Σ B (λ y → Trunc (Echo f y))

  prop-factor-left : A → Image-prop
  prop-factor-left a = f a , ∣ echo-intro f a ∣

  prop-factor-right : Image-prop → B
  prop-factor-right = proj₁

  prop-factor-commutes : ∀ a → prop-factor-right (prop-factor-left a) ≡ f a
  prop-factor-commutes _ = refl

  -- MONO side: the right leg is injective (second component is a prop).
  prop-factor-right-injective : ∀ {z₁ z₂ : Image-prop}
    → prop-factor-right z₁ ≡ prop-factor-right z₂
    → z₁ ≡ z₂
  prop-factor-right-injective {b , tr₁} {.b , tr₂} refl =
    cong (b ,_) (is-prop tr₁ tr₂)

  -- EPI side: the left leg is mere-surjective onto the image.
  prop-factor-left-mere-surjective : (z : Image-prop)
    → Trunc (Σ A λ a → prop-factor-left a ≡ z)
  prop-factor-left-mere-surjective (b , tr) =
    rec is-prop
        (λ where (a , refl) → ∣ a , cong (f a ,_) (is-prop ∣ echo-intro f a ∣ tr) ∣)
        tr

----------------------------------------------------------------------
-- Consumer at the REAL interface + pinned headlines
----------------------------------------------------------------------

module ImagePropCubical {A B : Set ℓ} (f : A → B) where
  open ImageProp trunc-cubical f public

prop-factor-right-injective-real :
  ∀ {A B : Set ℓ} (f : A → B)
    {z₁ z₂ : Σ B (λ y → ∥ Echo f y ∥)}
  → ImagePropCubical.prop-factor-right f z₁
    ≡ ImagePropCubical.prop-factor-right f z₂
  → z₁ ≡ z₂
prop-factor-right-injective-real f =
  ImagePropCubical.prop-factor-right-injective f

prop-factor-left-mere-surjective-real :
  ∀ {A B : Set ℓ} (f : A → B)
    (z : Σ B (λ y → ∥ Echo f y ∥))
  → ∥ Σ A (λ a → ImagePropCubical.prop-factor-left f a ≡ z) ∥
prop-factor-left-mere-surjective-real f =
  ImagePropCubical.prop-factor-left-mere-surjective f
