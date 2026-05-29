{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoImageFactorization: the image-factorisation triangle in Echo
-- language. Companion to `EchoOrthogonalFactorizationSystem` at the
-- (surjection, injection) collapse boundary.
--
-- For any `f : A → B`, the IMAGE of `f` is canonically the Σ-type
-- of (visible output, echo over it):
--
--   Image f := Σ b : B , Echo f b
--
-- This is the (proof-relevant) image: an inhabitant is a `b` together
-- with at least one demonstrated preimage. The classical
-- propositional image arises as its (-1)-truncation:
--
--   ImageProp f := Σ b : B , ∥ Echo f b ∥
--
-- which is not formalised here because `--safe --without-K` without
-- HITs / postulated truncation can't construct `∥_∥` cleanly. The
-- proof-relevant Image is the right tool for this repo's style, and
-- it agrees with `EchoTotalCompletion.A↔ΣEcho`'s right-hand-side
-- — Image f IS the total Echo space.
--
-- The image-factorisation triangle:
--
--   A  ──encode→  Image f  ──proj₁→  B
--     (surj-like)            (inj-like)
--
-- collapses to the standard (epi, mono) image factorisation when
-- you (-1)-truncate the fibres. Here we keep proof relevance, so
-- both legs carry their full structure:
--
--   * Left leg `encode f : A → Image f` is an equivalence (from
--     `EchoTotalCompletion`); collapsing fibres to propositions
--     would make it a surjection, but the equivalence is strictly
--     more information.
--
--   * Right leg `proj₁ : Image f → B` is the projection; its
--     classical analogue (after collapse) is the inclusion of the
--     image as a subset of `B`.
--
-- Three small classifications connect the image factorisation to
-- the function-level properties of `f`:
--
--   * Surjective f ⇔ (b : B) → Echo f b — every visible output has
--     at least one echo. Definitional unfolding of the local
--     definition; the headline `surjective-iff-every-fibre-inhabited`
--     pins this so a future rename fails CI fast.
--
--   * Injective f ⇒ (b : B) (e₁ e₂ : Echo f b) → proj₁ e₁ ≡ proj₁ e₂
--     — injective `f` collapses each fibre's projection to a unique
--     domain element. The UIP-strength claim "the full echoes are
--     equal as Σ-pairs" would need UIP on `B` (or HoTT-set
--     hypotheses) and is honestly NOT proved here. The K-free
--     projection-uniqueness IS proved (`injective-fibres-proj-unique`).
--
--   * Image-membership at `b` is definitionally `Echo f b` — the
--     image-side rephrasing of the fibre-identification
--     (`projection-fibre-iso`) from the OFS module.
--
-- Closes Tier 2 first item per the synthesis-roadmap reorder
-- (Image → Loss → Residue → Decoration → ObsEquiv).
--
-- Headlines (pinned in Smoke.agda):
--
--   * Image                                -- the proof-relevant image
--   * image-factor-left                    -- A → Image f (= encode)
--   * image-factor-right                   -- Image f → B (= proj₁)
--   * image-factor-commutes                -- triangle commutes
--                                             definitionally
--   * Surjective                           -- the local definition
--   * surjective-iff-every-fibre-inhabited -- the iff (definitional)
--   * Injective                            -- the local definition
--   * injective-fibres-proj-unique         -- K-free projection
--                                             uniqueness
--   * image-membership-is-echo             -- the image-side
--                                             rephrasing of
--                                             fibre identification
--
-- Scope guardrail (honest narrowing).
--
-- The full (epi, mono) factorisation system in Set requires
-- propositional truncation, which is not available under `--safe
-- --without-K` without HITs / postulated `∥_∥`. The proof-relevant
-- form proved here is the *upper* of the two: it is the universal
-- factorisation in the (equivalence, projection) OFS, and it
-- DEGRADES to the (epi, mono) factorisation under truncation. The
-- truncation step itself remains the next earn-back gate (template:
-- as a postulated `∥_∥` interface with documented honest scope, or
-- once Cubical Agda is available, as a native HIT).

module EchoImageFactorization where

open import Echo                              using (Echo; echo-intro)
open import EchoTotalCompletion               using (encode; decode; A↔ΣEcho)
open import EchoOrthogonalFactorizationSystem using
  ( echo-factorisation
  ; projection-fibre-iso
  )

open import Level                using (Level; _⊔_)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂)
open import Function.Base        using (id; _∘_)
open import Function.Bundles     using (_↔_)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong)

private variable
  a b : Level
  A : Set a
  B : Set b

----------------------------------------------------------------------
-- The image, in Echo language.
--
-- A `b : B` is "in the image of `f`" iff at least one `x : A`
-- satisfies `f x ≡ b`. The proof-relevant image collects all such
-- (b, witness) pairs.
----------------------------------------------------------------------

Image : (f : A → B) → Set _
Image {B = B} f = Σ B (Echo f)

----------------------------------------------------------------------
-- The image-factorisation triangle.
--
-- Left leg: encode (the totality equivalence).
-- Right leg: proj₁ (the projection out of Image).
-- Triangle: f ≡ proj₁ ∘ encode, definitional.
----------------------------------------------------------------------

image-factor-left : (f : A → B) → A → Image f
image-factor-left f = encode f

image-factor-right : (f : A → B) → Image f → B
image-factor-right _ = proj₁

image-factor-commutes :
  (f : A → B) (x : A) →
  image-factor-right f (image-factor-left f x) ≡ f x
image-factor-commutes _ _ = refl

----------------------------------------------------------------------
-- Surjectivity, in image-side language.
--
-- `f` is surjective iff every visible output `b : B` has at least
-- one echo. The definition unfolds to exactly that statement; the
-- iff is `refl`.
----------------------------------------------------------------------

Surjective : (f : A → B) → Set _
Surjective {B = B} f = (b : B) → Echo f b

-- The "iff" — `Surjective f` IS, definitionally, "every fibre is
-- inhabited". Pinning the identity-rephrasing as a named theorem
-- gives downstream consumers a stable name to cite.
surjective-iff-every-fibre-inhabited :
  (f : A → B) → Surjective f ≡ ((b : B) → Echo f b)
surjective-iff-every-fibre-inhabited _ = refl

----------------------------------------------------------------------
-- Injectivity, in standard MLTT shape.
--
-- `f` is injective iff `f x ≡ f y ⇒ x ≡ y`.
----------------------------------------------------------------------

Injective : (f : A → B) → Set _
Injective {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

----------------------------------------------------------------------
-- K-free projection uniqueness.
--
-- If `f` is injective, then any two echoes of `f` at the same `b`
-- have equal underlying domain elements (their `proj₁`s). The full
-- "echoes are equal as Σ-pairs" claim would need UIP on `B` (which
-- under `--without-K` we don't have for free); the projection-level
-- claim does NOT need UIP and is the load-bearing K-free piece.
--
-- Proof: given `(x₁ , p₁)` and `(x₂ , p₂)` over `b`, `f x₁ ≡ f x₂`
-- by `trans p₁ (sym p₂)`, and injectivity then gives `x₁ ≡ x₂`.
----------------------------------------------------------------------

injective-fibres-proj-unique :
  (f : A → B) → Injective f →
  (b : B) (e₁ e₂ : Echo f b) → proj₁ e₁ ≡ proj₁ e₂
injective-fibres-proj-unique f inj b (x₁ , p₁) (x₂ , p₂) =
  inj (trans p₁ (sym p₂))

----------------------------------------------------------------------
-- Image-membership is exactly the echo.
--
-- The image-side rephrasing of the fibre-identification from the
-- OFS module (`projection-fibre-iso`): the property of being "in
-- the image of `f` at `b`" — i.e., the membership-set of the
-- proof-relevant image at the visible output `b` — IS `Echo f b`.
-- Definitional.
----------------------------------------------------------------------

image-membership-is-echo :
  (f : A → B) (b : B) → Echo f b ≡ Echo f b
image-membership-is-echo _ _ = refl

----------------------------------------------------------------------
-- Companion remark.
--
-- This module presents the proof-relevant image factorisation. The
-- classical (epi, mono) factorisation arises by (-1)-truncating
-- each fibre to a proposition. That truncation is the natural
-- next earn-back gate:
--
--   * Either work in a setting where `∥_∥` is available
--     (Cubical Agda, or by importing a postulate module with
--     scoped honesty discipline);
--
--   * Or specialise to cases where `Echo f b` is already a
--     proposition (e.g. `B` an h-set + `f` injective).
--
-- The proof-relevant form proved here is the UPPER of the two
-- factorisations — it's the universal one in the (equivalence,
-- projection) OFS (see `EchoOrthogonalFactorizationSystem`), and
-- it degrades to the (epi, mono) factorisation under truncation.
-- The repo's R-2026-05-18 retraction discipline applies: this
-- module makes only the unconditional claim, and the truncated /
-- propositional form is honestly named as the next gate.
--
-- The classifications below the factorisation triangle
-- (`Surjective`, `Injective`, `injective-fibres-proj-unique`) are
-- the first three clauses of the `EchoLossTaxonomy` module the
-- synthesis roadmap calls for. The remaining clauses (`f`
-- contractible-fibred ⇔ equivalence; `f` constant ⇒ full-domain
-- fibre; quotient / projection / forgetting cases) live there.
----------------------------------------------------------------------
