{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoKernel — the funext-free core of echo-types.
--
-- This module is the *curated public surface* of the Echo foundation.
-- Every other `Echo*` module in the tree transitively imports `Echo`;
-- this re-export names that dependency-light core explicitly and pins
-- the load-bearing lemma *types* so the kernel API cannot silently
-- weaken without breaking this file's typecheck.
--
-- Provenance / honesty (read before citing anything here):
--
--   * `--safe --without-K`, zero postulates, zero escape pragmas.
--   * The kernel's import cone is `Echo` + agda-stdlib only
--     (`Level`, `Function.Base`, `Function.Bundles`,
--     `Data.Product.Base`, `Relation.Binary.PropositionalEquality`
--     [+ `.Properties`]). It contains *no* `Axiom.Extensionality` /
--     funext anywhere — so every lemma re-exported below is
--     funext-free, and this module's successful `--safe --without-K`
--     build is itself the funext-free certificate.
--   * The genuine funext-relativity in echo-types is the
--     *pointwise-only* mediator property (`EchoPullback`,
--     `echo-pullback-univ`), which lives strictly *outside* this
--     kernel. The kernel deliberately keeps the cancel-iso
--     round-trips first-order by taking the triangle identities
--     (`triangle₁`, `triangle₂`) as explicit hypotheses rather than
--     deriving them via funext.
--
-- Non-claims (per `docs/retractions.adoc` R-2026-05-18, not
-- un-retracted here): the kernel is a definitionally-grounded,
-- loss-graded *reindexing* surface. It is *not* a graded comonad, it
-- carries *no* universal/terminal property, and it is *not* a
-- conservativity metatheorem. Nothing below asserts any of those.
--
-- Kernel vs derived classification: see
-- `docs/echo-types/echo-kernel-note.adoc` (one-page note, kept
-- current in the same PR as this module).

module EchoKernel where

-- The whole funext-free core surface. Everything downstream that
-- "imports Echo" is importing exactly this.
open import Echo public

------------------------------------------------------------------------
-- Kernel contract.
--
-- The load-bearing lemmas the derived layer actually depends on,
-- restated with explicit signatures and bound by definitional
-- equality to the `Echo` proofs. This is a *contract*, not new
-- mathematics: it forces the kernel's public types to remain exactly
-- as documented, and re-checks each in the funext-free,
-- extensionality-free, `--safe --without-K` cone. If any `Echo`
-- lemma is weakened, generalised, or acquires a funext dependency,
-- this section fails to typecheck.
------------------------------------------------------------------------

module Kernel-contract where

  open import Level using (Level; _⊔_)
  open import Function.Base using (_∘_; id)
  open import Data.Product.Base using (Σ; _,_; _×_)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong)
  open import Function.Bundles using (_↔_)

  -- Echo functor: the structured remainder of an information-losing f.
  kernel-Echo :
    ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → B → Set (a ⊔ b)
  kernel-Echo = Echo

  -- Introduction into one's own fibre.
  kernel-echo-intro :
    ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → Echo f (f x)
  kernel-echo-intro = echo-intro

  -- Fibrewise functorial action over a fixed base.
  kernel-map-over :
    ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
    {f : A → B} {f' : A' → B} →
    MapOver f f' → ∀ {y : B} → Echo f y → Echo f' y
  kernel-map-over = map-over

  -- Functoriality: identity law.
  kernel-map-over-id :
    ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B} (e : Echo f y) →
    map-over (id , (λ x → refl)) e ≡ e
  kernel-map-over-id = map-over-id

  -- Functoriality: composition law.
  kernel-map-over-comp :
    ∀ {a a' a'' b}
    {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
    {f : A → B} {f' : A' → B} {f'' : A'' → B}
    (u1 : A → A') (c1 : ∀ x → f' (u1 x) ≡ f x)
    (u2 : A' → A'') (c2 : ∀ x → f'' (u2 x) ≡ f' x)
    {y : B} (e : Echo f y) →
    map-over {f = f} {f' = f''}
      (u2 ∘ u1 , (λ x → trans (c2 (u1 x)) (c1 x))) e
    ≡ map-over {f = f'} {f' = f''} (u2 , c2)
        (map-over {f = f} {f' = f'} (u1 , c1) e)
  kernel-map-over-comp = map-over-comp

  -- Composition accumulation iso (unconditional; closes the
  -- accumulation law of composition.md §1).
  kernel-Echo-comp-iso :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B) (g : B → C) (y : C) →
    Echo (g ∘ f) y ↔ Σ B (λ b → Echo f b × (g b ≡ y))
  kernel-Echo-comp-iso = Echo-comp-iso

  -- The single load-bearing path-algebra lemma. It is naturality of
  -- a homotopy `h : f ∼ id` along a path — first-order, funext-free.
  kernel-hom-natural-id :
    ∀ {a} {A : Set a} (f : A → A) (h : ∀ z → f z ≡ z)
    {x y : A} (p : x ≡ y) →
    trans (cong f p) (h y) ≡ trans (h x) p
  kernel-hom-natural-id = hom-natural-id

  -- Cancel iso, with the two triangle coherences kept as explicit
  -- hypotheses (this is *how* the kernel stays funext-free; funext
  -- would otherwise be needed to relate the two quasi-inverse laws).
  kernel-cancel-iso :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B) (g : B → C) (s : C → B)
    (s-left  : ∀ b → s (g b) ≡ b)
    (s-right : ∀ y → g (s y) ≡ y)
    (triangle₁ : ∀ b → cong g (s-left b) ≡ s-right (g b))
    (triangle₂ : ∀ y → cong s (s-right y) ≡ s-left (s y))
    (y : C) →
    Echo (g ∘ f) y ↔ Echo f (s y)
  kernel-cancel-iso = cancel-iso
