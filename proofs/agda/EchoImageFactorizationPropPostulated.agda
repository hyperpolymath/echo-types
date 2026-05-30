{-# OPTIONS --without-K #-}

-- hypatia: allow code_safety/agda_postulate -- ∥_∥ cannot be constructed in --safe --without-K without HITs / Cubical; the four postulates below are the scoped, documented TruncInterface demonstration. Exploratory per docs/echo-types/echo-kernel-note.adoc; guardrail-exempted in tools/check-guardrails.sh; base EchoImageFactorizationProp remains --safe --without-K with zero postulates.

-- Postulated-truncation consumer for `EchoImageFactorizationProp`.
--
-- ## Purpose
--
-- `EchoImageFactorizationProp` is module-parameterised in a
-- `TruncInterface`, deliberately scoped to ship the (epi, mono)
-- factorisation content WITHOUT committing to any particular
-- implementation of propositional truncation.  The base module
-- itself is `--safe --without-K` with zero postulates; the
-- propositional-truncation OBLIGATION is bumped to the consumer.
--
-- This module demonstrates the parameter is USABLE by exhibiting a
-- concrete `TruncInterface ℓ` instance built from four postulates
-- matching the four interface fields, then opens
-- `ImageProp T f` to confirm the parametric content goes through
-- on a concrete consumer.
--
-- ## Honest scope
--
-- This is a POSTULATED-INTERFACE demonstration, NOT a HIT
-- construction.  The postulates assert that propositional
-- truncation exists and satisfies its standard laws — they do not
-- prove the existence; they assume it.
--
-- The classification consequence:
--
--   * The flag profile is `--without-K` only (no `--safe`),
--     because `--safe` forbids `postulate` entirely.  This module
--     therefore lives OUTSIDE the kernel cone and outside
--     `proofs/agda/All.agda` (per the existing
--     `EchoDecorationBridge` Exploratory precedent in
--     `docs/echo-types/echo-kernel-note.adoc`).
--   * Classification: Exploratory.  Listed in the note to satisfy
--     `scripts/kernel-guard.sh` Check B (classification-drift
--     lint), not load-bearing.
--   * The base `EchoImageFactorizationProp` remains kernel-cone
--     compatible (`--safe --without-K`, zero postulates) and is
--     the load-bearing artefact.
--
-- ## What this module ships
--
--   * Four `postulate` declarations realising the
--     `TruncInterface ℓ` record fields.
--   * `trunc : TruncInterface ℓ` — the packaged interface.
--   * `module ImagePropPostulated f` re-opening
--     `EchoImageFactorizationProp.ImageProp trunc f` for any
--     `f : A → B` at the chosen levels.
--   * `prop-factor-right-injective-demo` — a pinned re-export of
--     the mono-side theorem from the parametric content,
--     specialised to the postulated interface.
--   * `prop-factor-left-mere-surjective-demo` — same for the
--     epi-side.
--
-- ## What this module deliberately DOES NOT prove
--
--   * That the postulated `Trunc` IS the standard (-1)-truncation.
--     It satisfies the interface laws by assumption; that is all
--     the parametric proofs in `ImageProp` need.
--   * Anything about the postulates' consistency.  The standard
--     HoTT discipline says the four laws together characterise
--     `Trunc A` up to equivalence (and Cubical Agda or a hand-
--     rolled HIT realises them concretely); we cite that
--     literature rather than mechanise it.
--
-- The mechanical contribution: pin that the parameterised
-- `EchoImageFactorizationProp.ImageProp` module can be CONSUMED
-- via interface plug-in.  The demonstrative side-effect is a
-- visible auditable check that the base module's parameter slots
-- match a real `TruncInterface ℓ` shape.
--
-- ## Headlines (this module's contribution)
--
--   * `trunc`                                    — the packaged interface
--   * `prop-factor-right-injective-demo`         — mono side, plugged
--   * `prop-factor-left-mere-surjective-demo`    — epi side, plugged

module EchoImageFactorizationPropPostulated where

open import EchoImageFactorizationProp using (TruncInterface; module ImageProp)
open import Echo                       using (Echo)

open import Level                   using (Level; suc)
open import Data.Product.Base       using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
                                    using (_≡_)

private variable
  ℓ : Level

----------------------------------------------------------------------
-- Postulated truncation interface
----------------------------------------------------------------------

-- The four standard propositional-truncation obligations.  Cubical
-- Agda or a hand-rolled HIT realises these concretely; here we take
-- them as assumed.

postulate
  Trunc-pos    : Set ℓ → Set ℓ
  ∣_∣-pos      : ∀ {A : Set ℓ} → A → Trunc-pos A
  is-prop-pos  : ∀ {A : Set ℓ} (x y : Trunc-pos A) → x ≡ y
  rec-pos      : ∀ {A B : Set ℓ}
                 → ((x y : B) → x ≡ y)
                 → (A → B)
                 → Trunc-pos A → B

----------------------------------------------------------------------
-- Packaged `TruncInterface ℓ` from the postulates
----------------------------------------------------------------------

-- Repackage the four postulates as the `TruncInterface ℓ` record
-- consumed by `EchoImageFactorizationProp.module ImageProp`.

trunc : TruncInterface ℓ
trunc = record
  { Trunc   = Trunc-pos
  ; ∣_∣     = ∣_∣-pos
  ; is-prop = is-prop-pos
  ; rec     = rec-pos
  }

----------------------------------------------------------------------
-- Consumer demonstration: open `ImageProp trunc f` and re-export
----------------------------------------------------------------------

-- Both `A` and `B` need to live at the SAME level `ℓ` per
-- `ImageProp`'s implicit-equal-level signature.  Same-level is the
-- common Σ-product case in practice; cross-level consumers would
-- need to lift to a common level (`Level.Lift`).

module ImagePropPostulated {A B : Set ℓ} (f : A → B) where
  -- Open the parametric module with the postulated interface
  -- plugged in.  Every name inside `ImageProp` is now available
  -- under this module's namespace.
  open ImageProp trunc f public

----------------------------------------------------------------------
-- Demonstrative pinned exports
----------------------------------------------------------------------

-- Headline 1 — MONO side, plugged.  Pin the mono-side theorem at
-- the postulated-interface specialisation.  This confirms the
-- parametric content goes through under interface plug-in (the
-- proof type-checks at the concrete instance).

prop-factor-right-injective-demo :
  ∀ {A B : Set ℓ} (f : A → B)
    {z₁ z₂ : Σ B (λ y → Trunc-pos (Echo f y))}
  → ImagePropPostulated.prop-factor-right f z₁
    ≡
    ImagePropPostulated.prop-factor-right f z₂
  → z₁ ≡ z₂
prop-factor-right-injective-demo f =
  ImagePropPostulated.prop-factor-right-injective f

-- Headline 2 — EPI side, plugged.  Pin the epi-side theorem at the
-- postulated-interface specialisation.  The truncated existence is
-- exactly the standard (-1)-truncated surjectivity.

prop-factor-left-mere-surjective-demo :
  ∀ {A B : Set ℓ} (f : A → B)
    (z : Σ B (λ y → Trunc-pos (Echo f y)))
  → Trunc-pos (Σ A λ a → ImagePropPostulated.prop-factor-left f a ≡ z)
prop-factor-left-mere-surjective-demo f =
  ImagePropPostulated.prop-factor-left-mere-surjective f
