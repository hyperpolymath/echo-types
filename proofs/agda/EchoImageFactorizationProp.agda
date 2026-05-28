{-# OPTIONS --safe --without-K #-}

-- (Epi, mono) image factorisation — module-parameterised in the
-- propositional truncation interface.
--
-- Companion to `EchoImageFactorization`.  The base module ships the
-- K-free proof-relevant (equivalence, projection) factorisation
-- (`Image f := Σ B (Echo f)`); this module degrades it to the
-- standard set-theoretic (epi, mono) factorisation by truncating
-- the second component to a proposition.
--
-- The propositional truncation `∥_∥` is taken as an explicit
-- module-parameter rather than postulated, in the spirit of the
-- funext-as-module-parameter discipline used in `EchoOFSUnivF5`
-- (R-2026-05-18 narrowing).  Any consumer can instantiate with:
--
--   * Cubical Agda's native `∥_∥₋₁` HIT (once the file's flag profile
--     allows it),
--   * a hand-rolled HIT under a different module's relaxed flags,
--   * a postulated `∥_∥` interface (under the usual honest-scope
--     discipline; postulates would live in the consumer module).
--
-- This module makes no commitments about how `Trunc` is implemented;
-- it only consumes the interface laws.
--
-- ## What lands
--
--   * `TruncInterface` — record packaging the four ∥_∥ obligations:
--     `Trunc`, `∣_∣`, `is-prop`, `rec`.
--   * `module ImageProp` — module parameterised in
--     `(T : TruncInterface (a ⊔ b)) (f : A → B)`:
--       - `Image-prop f := Σ B (λ y → Trunc (Echo f y))` — the
--         (-1)-truncated image (each fibre collapsed to a prop).
--       - `prop-factor-left : A → Image-prop f` — left leg.
--       - `prop-factor-right : Image-prop f → B` — right leg.
--       - `prop-factor-commutes` — triangle (definitional).
--       - `prop-factor-right-injective` — mono side: the right leg
--         is injective (because the second component is a prop).
--       - `prop-factor-left-mere-surjective` — epi side: every
--         element of `Image-prop` has a MERE preimage (a `Trunc`-wrapped
--         Σ).
--
-- ## What this does NOT prove
--
-- The factorisation here is the (-1)-truncated form, which makes
-- `prop-factor-left` MERELY surjective onto `Image-prop` (not
-- surjective in the set sense — that would need split surjectivity
-- which fails for non-decidable predicates).  The mere-surjectivity
-- + injectivity pair is exactly the standard (epi, mono) discipline
-- in the category of sets with propositional surjectivity as "epi".
--
-- ## Honest scope
--
-- The (epi, mono) factorisation lands AT the truncation interface;
-- it does not construct the truncation itself.  Under the
-- `TruncInterface` parameter, the proof goes through K-free with
-- zero postulates inside THIS module.  The PROPOSITIONALITY claim
-- (`prop-factor-right-injective`) requires the interface's
-- `is-prop` law; the SURJECTIVITY claim
-- (`prop-factor-left-mere-surjective`) requires the interface's
-- `rec` eliminator.
--
-- ## Headlines (pin in `Smoke.agda`)
--
--   * `TruncInterface` (record)
--   * `module ImageProp` (parametric content)

module EchoImageFactorizationProp where

open import Echo                              using (Echo; echo-intro)
open import EchoImageFactorization            using (Image)

open import Level                using (Level; _⊔_; suc)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂)
open import Function.Base        using (id; _∘_)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; cong)

private variable
  a b ℓ : Level
  A : Set a
  B : Set b

----------------------------------------------------------------------
-- Opaque truncation interface
----------------------------------------------------------------------

-- The four obligations every propositional-truncation implementation
-- must satisfy:
--
--   1. `Trunc A` exists as a Set at the same level.
--   2. Every element of `A` has a (canonical) image in `Trunc A`.
--   3. Any two inhabitants of `Trunc A` are equal — this is the
--      propositionality content (= the "(-1)-truncation").
--   4. To define a function `Trunc A → B` it suffices to give a
--      function `A → B` together with a proof that `B` is a
--      proposition — the elimination principle.
--
-- These are independent of any choice of HIT vs postulate; they
-- characterise propositional truncation up to equivalence.

record TruncInterface (ℓ : Level) : Set (suc ℓ) where
  field
    Trunc   : Set ℓ → Set ℓ
    ∣_∣     : ∀ {A : Set ℓ} → A → Trunc A
    is-prop : ∀ {A : Set ℓ} (x y : Trunc A) → x ≡ y
    rec     : ∀ {A B : Set ℓ}
              → ((x y : B) → x ≡ y)
              → (A → B)
              → Trunc A → B

----------------------------------------------------------------------
-- The (epi, mono) image factorisation, parametric in `TruncInterface`
----------------------------------------------------------------------

module ImageProp
  {A : Set ℓ} {B : Set ℓ}
  (T : TruncInterface ℓ)
  (f : A → B) where

  open TruncInterface T

  -- The (-1)-truncated image: each fibre's existence is collapsed
  -- to a proposition.  Distinct echoes at the same `b` collapse to
  -- the same inhabitant of `Image-prop` (so the image really is
  -- "the set of `b`s in the image", not the proof-relevant
  -- `Σ B (Echo f)`).
  Image-prop : Set ℓ
  Image-prop = Σ B (λ y → Trunc (Echo f y))

  -- Left leg: `a ↦ (f a, ∣ echo-intro a ∣)`.
  prop-factor-left : A → Image-prop
  prop-factor-left a = f a , ∣ echo-intro f a ∣

  -- Right leg: project the carrier.
  prop-factor-right : Image-prop → B
  prop-factor-right = proj₁

  -- Triangle: `f ≡ prop-factor-right ∘ prop-factor-left`,
  -- definitional via `proj₁ (f a , _) = f a`.
  prop-factor-commutes : ∀ a → prop-factor-right (prop-factor-left a) ≡ f a
  prop-factor-commutes _ = refl

  ----------------------------------------------------------------------
  -- The MONO side: prop-factor-right is injective
  ----------------------------------------------------------------------

  -- Two inhabitants of `Image-prop` with equal `proj₁`s are equal,
  -- because the second component is a prop (by `is-prop`).  This is
  -- exactly the categorical "mono" property in Set.
  --
  -- The proof unifies the first components via the `refl` premise,
  -- then closes the Σ-equality by `is-prop` on the truncated
  -- second components.  K-free under `--without-K`: the unification
  -- is on a fresh-variable position, and the `is-prop` step is
  -- exactly what truncation provides.

  prop-factor-right-injective : ∀ {z₁ z₂ : Image-prop}
    → prop-factor-right z₁ ≡ prop-factor-right z₂
    → z₁ ≡ z₂
  prop-factor-right-injective {b , tr₁} {.b , tr₂} refl =
    cong (b ,_) (is-prop tr₁ tr₂)

  ----------------------------------------------------------------------
  -- The EPI side: prop-factor-left is mere-surjective
  ----------------------------------------------------------------------

  -- Every element of `Image-prop` has a MERE (truncated) preimage
  -- under `prop-factor-left`.  This is the standard (-1)-truncated
  -- surjectivity, which serves as "epi" in Set under propositional
  -- truncation.
  --
  -- The truncated second component `tr : Trunc (Echo f b)` is
  -- eliminated via `rec` into a `Trunc (Σ A λ a → prop-factor-left a
  -- ≡ z)`.  The target is a prop (by `is-prop` on the outer Trunc),
  -- so the eliminator's "respects propositionality" obligation
  -- discharges immediately.
  --
  -- Inside `rec`, we have `e : Echo f b = (a , p)` where `p : f a ≡
  -- b`.  Then `prop-factor-left a = (f a, ∣echo-intro f a∣)`.  To
  -- show `(f a, ∣echo-intro f a∣) ≡ (b, tr)`, we use a Σ-equality:
  -- the first components are unified by `p : f a ≡ b`, and the
  -- second components are both `Trunc (Echo f b)` so equal by
  -- `is-prop`.  The resulting witness is wrapped in `∣_∣` to land
  -- in `Trunc (Σ ...)`.

  prop-factor-left-mere-surjective : (z : Image-prop)
    → Trunc (Σ A λ a → prop-factor-left a ≡ z)
  prop-factor-left-mere-surjective (b , tr) =
    rec is-prop
        (λ where
          (a , refl) → ∣ a , cong (f a ,_) (is-prop ∣ echo-intro f a ∣ tr) ∣)
        tr
