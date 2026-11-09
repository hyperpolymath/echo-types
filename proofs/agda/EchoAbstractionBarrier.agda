{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Track B of the "Echo ≠ Σ" identity-claim consolidation
-- (`roadmap.adoc` §Lane 2; sketch at
-- `core/skepticisms/is-this-just-sigma-types.md` §4 and
-- `docs/echo-types/sigma-distinctness-map.adoc` §"Demand 4").
--
-- Scope guardrail (load-bearing — read before any prose claim about
-- this module). This module ships a CONSUMER-SIDE FREE THEOREM AT THE
-- HEADLINE AFFINE INSTANCE (`LEcho affine = EchoR ⊤ TrivialCert tt`).
-- It is NOT a general Reynolds-style parametricity result. Agda has
-- no parametricity primitive, and a statement quantifying over all
-- consumer types `X` and all echo carriers would require either an
-- axiom or a paper-only proof — both violate the no-postulate
-- invariant. The honest claim is: at the affine instance the residue
-- carrier is contractible (`EchoLinear.affine-canonical`), so every
-- consumer factors through that contraction and provably cannot
-- distinguish two known-distinct linear preimages. This is the
-- strongest statement available inside `--safe --without-K` without
-- funext.
--
-- The module ships two theorems:
--
--   `affine-consumer-cannot-distinguish` — POSITIVE: any
--   `g : LEcho affine → X` assigns the same value to the weakened
--   images of `echo-true` and `echo-false`. Direct corollary of
--   `affine-all-equal`: functions out of the contractible affine
--   carrier are constant.
--
--   `sigma-distinguishes` — NEGATIVE: the raw Σ-projection `proj₁`
--   IS a consumer that distinguishes `echo-true` from `echo-false`.
--
-- Audit 2026-11-09: there is no enforced abstraction barrier. `Echo` is
-- a transparent Σ (no `abstract` block), and `proj₁` is used on Echo
-- throughout the repo. The pair of theorems shows what a barrier WOULD
-- buy (affine consumers are blind, proj₁ is not); hiding `proj₁` is a
-- convention, not a checked guarantee.
--
-- Honest framing notes:
-- * "Theorem 1" (consumer factorisation) from the original sketch was
--   dropped — its only statable form was `g (weaken e) ≡ g (weaken e)`,
--   degenerate. The real content lives in T2 + T3.
-- * The R-2026-05-18 narrowing applies. The graded structure is a
--   thin-poset reindexing modality, not a graded comonad. The
--   abstraction here is consumer-side at the affine instance, not
--   relational parametricity over the model.

module EchoAbstractionBarrier where

open import Echo            using (Echo)
open import EchoCharacteristic
  using (collapse; echo-true; echo-false; true≢false)
open import EchoLinear
  using ( Mode; linear; affine; LEcho
        ; weaken
        ; affine-all-equal
        )

open import Data.Bool.Base  using (Bool)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.Unit.Base  using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                            using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)
open import Level            using (Level)

private variable
  ℓ : Level

----------------------------------------------------------------------
-- Theorem 2 (positive). Any consumer at the affine mode assigns the
-- same value to the weakened images of the two known-distinct linear
-- echoes.
--
-- Direct corollary of `affine-all-equal` (`EchoLinear.agda:57-58`),
-- which is itself a corollary of `affine-canonical` — the affine
-- residue carrier is contractible. Hence `cong g` of the canonical
-- equality discharges the theorem in one line.

affine-consumer-cannot-distinguish :
  {X : Set ℓ} (g : LEcho affine → X) →
  g (weaken echo-true) ≡ g (weaken echo-false)
affine-consumer-cannot-distinguish g =
  cong g (affine-all-equal (weaken echo-true) (weaken echo-false))

----------------------------------------------------------------------
-- Theorem 3 (negative companion — the raw-Σ counter-program).
-- `proj₁ : Echo collapse tt → Bool` is a consumer over the *raw* Σ
-- encoding that distinguishes the two linear echoes. Its existence is
-- what the Echo interface (at affine mode) is designed to prevent
-- exporting: T2 above guarantees no affine-mode consumer can match
-- this behaviour.
--
-- The proof is `true≢false` directly, because `proj₁ echo-true`
-- reduces definitionally to `true` (via `echo-intro f x = x , refl`)
-- and `proj₁ echo-false` reduces to `false`.

sigma-distinguishes :
  Σ (Echo collapse tt → Bool)
    (λ g → g echo-true ≢ g echo-false)
sigma-distinguishes = proj₁ , true≢false
