{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Q2.1 — Generalisation of `echo-not-prop`.
--
-- This module is the artefact named in the Q2.1 attack path
-- (`docs/next-questions.adoc` §Q2.1): "State and prove the general
-- theorem in `proofs/agda/characteristic/NonTruncatable.agda`".
--
-- Gate-3 supplies three n=2 special cases that an `Echo` type is not
-- a mere proposition (`EchoExamples` / `EchoTropical` /
-- `EchoCharacteristic`, recovered as corollaries in
-- `EchoTruncation`). Q2.1 asks for the general statement:
--
--   For f : A → B and y : B, if there exist x₁ ≢ x₂ with
--   f x₁ ≡ y and f x₂ ≡ y, then ¬ isProp (Echo f y).
--
-- That statement is already proved generically as
-- `EchoTruncation.echo-not-prop`. This module (1) re-exports it under
-- the Q2.1 name so the gate paperwork points at a single audited
-- artefact, and (2) closes the genuinely open end of Q2.1: the
-- *non-injectivity* form, which does not receive the witnessing
-- value `y` but **constructs** it from a bare non-injectivity
-- witness on `f`. The received-`y` form needs the caller to have
-- already factored their non-injectivity through a common output;
-- the constructed-`y` form is the statement an external reader
-- means by "non-injective ⇒ non-truncatable".
--
----------------------------------------------------------------------
-- Gate-2 falsifier audit (honest).
--
-- Gate-2 falsifier: "naturally echo-shaped, not reducible to generic
-- Σ/fiber lemmas". Verdict for the *received-y* form (`Q2-1`):
-- PARTIALLY REDUCIBLE. Its proof is `ne (cong proj₁ (prop e₁ e₂))`,
-- which is the generic fact "a Σ-type with two elements differing in
-- the first component is not an `isProp`" — true of any Σ, not
-- specific to `Echo`. The only echo-specific content is in the
-- *statement*: the two Σ-elements are constrained to be preimages of
-- a *common* `y`. So `Q2-1` is echo-shaped in statement but its
-- proof factors through `Σ`. Under the strict gate-2 bar this is the
-- same demotion `VisibleConstraintAudit` applied to
-- `visible-constraint`: kept for expository value, **not** nominated
-- as a characteristic theorem on its own.
--
-- The *constructed-y* form (`non-injective⇒echo-not-prop`) is
-- strictly more than a Σ fact: it asserts that ordinary
-- non-injectivity of a function (`f x₁ ≡ f x₂`, `x₁ ≢ x₂`) — a
-- property with no Σ in sight — *forces* the existence of a
-- non-propositional echo fibre. The Σ-genericity argument does not
-- reach it, because the bad `y` is produced, not assumed. This is
-- the form worth forwarding to gate-2 as a nominee; the audit
-- conclusion is recorded for the integrator, not pre-decided here.
----------------------------------------------------------------------

module characteristic.NonTruncatable where

open import Echo using (Echo)
open import EchoTruncation using (isProp; echo-not-prop)

open import Level using (Level)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (¬_)

private
  variable
    ℓa ℓb : Level
    A : Set ℓa
    B : Set ℓb

----------------------------------------------------------------------
-- Q2.1, received-y form.  Re-export of the once-and-for-all generic
-- lemma, under the gate name, so `next-questions.adoc` §Q2.1 and
-- `roadmap-gates.adoc` Gate 2 point at one audited artefact.

Q2-1 :
  (f : A → B) {y : B}
  (x₁ x₂ : A) (p₁ : f x₁ ≡ y) (p₂ : f x₂ ≡ y) →
  x₁ ≢ x₂ →
  ¬ isProp (Echo f y)
Q2-1 = echo-not-prop

----------------------------------------------------------------------
-- Q2.1, constructed-y form (the genuinely open end, now closed).
--
-- From a bare non-injectivity witness on `f` — two distinct inputs
-- with equal output — *produce* an output value whose echo fibre is
-- not a mere proposition.  The witnessing `y` is `f x₁`; `x₁` lands
-- in its own fibre by `refl`, and `x₂` lands in the same fibre by
-- `sym eq`.  No common output is assumed: it is constructed.

non-injective⇒echo-not-prop :
  (f : A → B) (x₁ x₂ : A) →
  f x₁ ≡ f x₂ →
  x₁ ≢ x₂ →
  Σ B (λ y → ¬ isProp (Echo f y))
non-injective⇒echo-not-prop f x₁ x₂ eq ne =
  f x₁ , Q2-1 f x₁ x₂ refl (sym eq) ne
