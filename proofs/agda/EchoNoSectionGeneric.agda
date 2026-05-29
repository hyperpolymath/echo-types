{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoNoSectionGeneric: generalise no-section from "an example" to
-- "a theorem of the structure".
--
-- The repo's single most-cited theorem
-- (`EchoResidue.no-section-collapse-to-residue`,
-- `EchoLinear.no-section-weaken`) is proved at exactly one concrete
-- instance: the `Bool → ⊤` collapse with the trivial residue. The
-- proof is a three-line `trans/sym/cong` pattern that has nothing to
-- do with `Bool` or `⊤` specifically. It works for ANY collapsing
-- map together with a witness of two distinct elements landing on
-- the same image.
--
-- This module ships the generic theorem and recovers the existing
-- instance as a one-line corollary. Two consequences:
--
--   1. Future no-section reasoning over different Echo instances no
--      longer needs to re-derive the `trans/sym/cong` pattern; the
--      `no-section-of-collapsing-map` headline takes care of it
--      uniformly.
--
--   2. The existing `no-section-collapse-to-residue` becomes an
--      instance of the headline, demonstrably (the corollary
--      `no-section-collapse-to-residue′` below typechecks because
--      the existing collapse + distinctness data ARE the headline's
--      hypotheses). The narrowing "this is a property of *this*
--      collapse" becomes the structural fact "this is a property of
--      *every* collapse-with-distinct-preimages-and-shared-image".
--
-- The Echo-specific corollary `no-section-when-non-injective-at-y`
-- specialises further: any non-injective `f` at `y` (i.e. two
-- distinct echoes of `f` at the same visible output) gives no
-- section over the trivial residue. This is the form the
-- abstraction-barrier narrative wants.
--
-- Closes Tier 1 #2 of the synthesis roadmap (see CLAUDE.md session
-- arc 2026-05-27 keystone).
--
-- Headlines (pinned in Smoke.agda):
--
--   * no-section-of-collapsing-map     -- the headline generic theorem
--   * no-section-collapse-to-residue′  -- existing theorem recovered as
--                                         instance
--   * no-section-when-non-injective-at-y
--                                       -- Echo-specific corollary
--
-- Scope guardrail. The headline is a clean generalisation of the
-- existing `trans/sym/cong` pattern. It does NOT claim a stronger
-- categorical statement (e.g. "no collapsing map admits a section
-- in any model") — the hypothesis is the concrete data
-- "two specific elements collapse to the same image but are
-- distinct", which is the minimal sufficient input for the
-- proof. The companion remark at the end of the file documents
-- the further generalisations available.

module EchoNoSectionGeneric where

open import Echo                 using (Echo; echo-intro)
open import EchoCharacteristic   using (collapse; echo-true; echo-false; echo-true≢echo-false)
open import EchoResidue          using ( EchoR; TrivialCert
                                       ; collapse-to-residue
                                       ; collapse-residue-same
                                       ; echo-to-residue
                                       )

open import Level                using (Level; _⊔_)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base       using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary     using (¬_)

private variable
  a r : Level
  A : Set a
  R : Set r

----------------------------------------------------------------------
-- The headline generic theorem.
--
-- For ANY collapsing map `lower : A → R`, if two specific elements
-- `e₁ e₂ : A` are distinct (`e₁ ≢ e₂`) but collapse to the same
-- residue (`lower e₁ ≡ lower e₂`), then `lower` admits NO section
-- — there is no `raise : R → A` satisfying `raise ∘ lower ≡ id`
-- pointwise.
--
-- The proof is the same `trans/sym/cong` pattern that
-- `no-section-collapse-to-residue` runs, now stated at the level of
-- abstraction it actually lives at. Three lines.
----------------------------------------------------------------------

no-section-of-collapsing-map :
  (lower : A → R)
  (e₁ e₂ : A)
  (e₁≢e₂ : e₁ ≢ e₂)
  (lower-collapses : lower e₁ ≡ lower e₂) →
  ¬ Σ (R → A) (λ raise → ∀ e → raise (lower e) ≡ e)
no-section-of-collapsing-map lower e₁ e₂ e₁≢e₂ lower-collapses (raise , sec) =
  e₁≢e₂ (trans (sym (sec e₁)) (trans (cong raise lower-collapses) (sec e₂)))

----------------------------------------------------------------------
-- Existing instance, recovered.
--
-- `EchoResidue.no-section-collapse-to-residue` is the headline
-- specialised to:
--
--   * `lower := collapse-to-residue`
--   * `e₁ := echo-true`, `e₂ := echo-false`
--   * `e₁≢e₂ := echo-true≢echo-false`
--   * `lower-collapses := collapse-residue-same`
--
-- The corollary typechecks because the existing repo provides
-- exactly those four pieces of data under the names cited. This
-- demonstrates (mechanically, not just narratively) that the
-- existing theorem IS an instance of the generic structure.
----------------------------------------------------------------------

no-section-collapse-to-residue′ :
  ¬ Σ (EchoR ⊤ TrivialCert tt → Echo collapse tt)
       (λ reify → ∀ e → reify (collapse-to-residue e) ≡ e)
no-section-collapse-to-residue′ =
  no-section-of-collapsing-map
    collapse-to-residue
    echo-true echo-false
    echo-true≢echo-false
    collapse-residue-same

----------------------------------------------------------------------
-- Echo-specific corollary: non-injective `f` at `y` admits no
-- section over the trivial residue.
--
-- For any `f : A → B` and any `y : B`, if two specific echoes
-- `e₁ e₂ : Echo f y` are distinct, then no section exists for the
-- trivial-residue weakening — because the trivial residue at `y`
-- is `(tt , tt)` regardless of which echo you started from, so two
-- distinct echoes always collapse to the same residue.
--
-- This is the form the abstraction-barrier / Echo-vs-Σ narrative
-- wants: the no-section property is a property of NON-INJECTIVITY,
-- not of the specific `Bool → ⊤` instance.
----------------------------------------------------------------------

trivial-weaken :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) →
  Echo f y → EchoR ⊤ TrivialCert tt
trivial-weaken f y _ = tt , tt

trivial-weaken-collapses :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) (e₁ e₂ : Echo f y) →
  trivial-weaken f y e₁ ≡ trivial-weaken f y e₂
trivial-weaken-collapses _ _ _ _ = refl

no-section-when-non-injective-at-y :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B)
  (e₁ e₂ : Echo f y) (e₁≢e₂ : e₁ ≢ e₂) →
  ¬ Σ (EchoR ⊤ TrivialCert tt → Echo f y)
       (λ raise → ∀ e → raise (trivial-weaken f y e) ≡ e)
no-section-when-non-injective-at-y f y e₁ e₂ e₁≢e₂ =
  no-section-of-collapsing-map
    (trivial-weaken f y)
    e₁ e₂
    e₁≢e₂
    (trivial-weaken-collapses f y e₁ e₂)

----------------------------------------------------------------------
-- Companion remark.
--
-- Further generalisations available but NOT taken here, to keep
-- the module a minimal "raise the example to a theorem" slice:
--
--   * Quantify over the distinctness witness:
--       Σ (Σ e₁ e₂ , e₁ ≢ e₂ × lower e₁ ≡ lower e₂) → no-section
--     (currying back to the headline; same content, different
--     surface shape).
--
--   * State as a contrapositive: "if `lower` admits a section, it
--     is injective on at least the witnessed pair" — same content
--     by `¬¬`-elimination on decidable equality, only useful when
--     equality is decidable.
--
--   * Categorical lift: "no retraction in any category enriched
--     over Set" — requires a categorical setup not present in this
--     repo, and the slogan is no stronger than the headline.
--
-- The headline as stated is the minimal sufficient generalisation
-- to convert the existing single-instance theorem into a uniform
-- structural fact. Further generalisations are cosmetic.
----------------------------------------------------------------------
