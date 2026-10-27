-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- EchoReversibilityBridge: the constructive discharge of the 007 language's
-- Layer-10 reversibility (echo-residue) "phase-2" proof obligations against
-- this library of record.
--
-- 007 (https://github.com/hyperpolymath/007) models reversibility with an
-- echo residue: `reversible as <name>` arms a residue cell holding an
-- `Echo f y`, and `reverse <name>` consumes it to recover the input. Its
-- Idris2 spec (`proofs/idris2/EchoResidue.idr`,
-- `proofs/idris2/EchoResidueLinear.idr`) pins three obligations:
--
--   1. encode / decode round-trips  — an irreversible `f` together with its
--      residue is a total, reversible representation;
--   2. `reverseLinear : (1 e : Echo f y) → (x ** f x ≡ y)` — replaying a held
--      residue recovers the input (the `Holding`/`takeForReverse = Just`
--      branch of `ResidueCell`);
--   3. the linear discipline "affine capability, linear consumption" — the
--      undo capability may be dropped (weakened) but, once dropped, the
--      linear residue cannot be recovered (`Spent` does not reverse).
--
-- This module re-states the *interface* those obligations describe and shows
-- echo-types' own `Echo` / `EchoTotalCompletion` / `EchoLinear` satisfy it,
-- under `--safe --without-K` with zero postulates. The Agda here is the
-- source of truth; 007's Rust checker and Idris2 spec mirror this model.

{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}

module EchoReversibilityBridge where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Echo using (Echo; echo-intro)
open import EchoTotalCompletion using (encode; decode; decode-encode; encode-decode)
open import EchoLinear using (linear; affine; LEcho; weaken; no-section-weaken)

private variable
  a b : Level
  A : Set a
  B : Set b

------------------------------------------------------------------------
-- Obligations 1 + 2: the reversible-completion interface, met by Echo.
------------------------------------------------------------------------

-- The minimal data 007's reversibility model needs from a residue carrier:
-- arm a residue from an input (`hold`), take-it-for-reverse to recover an
-- input (`takeForReverse`), and the once-only correctness that replaying a
-- freshly-armed residue returns the original input (`reverse-recovers`).
--
-- `takeForReverse` here is the *total* `Just`-branch of 007's
-- `takeForReverse : … → Maybe a`, i.e. `reverseLinear`'s witness extraction
-- on a `Holding` cell; the `Maybe` wrapper is the runtime `Holding`/`Spent`
-- bookkeeping, not part of the type-level correspondence.
--
-- The residue carrier `Residue` is a parameter: an instance witnesses that a
-- *particular* carrier (here `Echo f`) supports armed reversal.
record ReversibleCompletion {a b} {A : Set a} {B : Set b}
       (f : A → B) (Residue : B → Set (a ⊔ b)) : Set (a ⊔ b) where
  field
    hold             : (x : A) → Residue (f x)
    takeForReverse   : {y : B} → Residue y → A
    reverse-recovers : (x : A) → takeForReverse (hold x) ≡ x

-- echo-types' `Echo f` is such a carrier. `hold` is `echo-intro` (= 007's
-- `encode` / the `Holding` cell); `takeForReverse` is the witness projection
-- (= `reverseLinear`'s `fst`); recovery is `refl`, because
-- `proj₁ (echo-intro f x) = proj₁ (x , refl) = x` definitionally.
echo-reversible : (f : A → B) → ReversibleCompletion f (Echo f)
echo-reversible f = record
  { hold             = echo-intro f
  ; takeForReverse   = proj₁
  ; reverse-recovers = λ _ → refl
  }

-- 007's narrative slogan — "an irreversible computation together with its
-- echo residue is a reversible representation" — is exactly echo-types'
-- totality iso read in the residue→input direction: the total echo space
-- `Σ B (Echo f)` recovers the domain `A`. (The A→Σ direction is
-- `EchoTotalCompletion.A↔ΣEcho`; this is its symmetric partner.)
reversibility-via-totality : (f : A → B) → Σ B (Echo f) ↔ A
reversibility-via-totality f =
  mk↔ₛ′ (decode f) (encode f) (decode-encode f) (encode-decode f)

------------------------------------------------------------------------
-- Obligation 3: the phase-2 linear discipline.
------------------------------------------------------------------------

-- "Affine capability": a live (linear) undo residue may always be weakened
-- to an affine one — the capability dropped. Never an error in 007.
capability-can-be-dropped : LEcho linear → LEcho affine
capability-can-be-dropped = weaken

-- "Linear consumption / Spent-does-not-reverse": there is NO section of
-- `weaken` — once the residue is degraded (the undo dropped, the cell
-- `Spent`) the linear residue cannot be recovered. This is echo-types'
-- `no-section-weaken`, the library-of-record discharge of the irreversibility
-- of dropping the capability.
no-recovery-once-dropped :
  ¬ (Σ (LEcho affine → LEcho linear)
       (λ raise → ∀ e → raise (weaken e) ≡ e))
no-recovery-once-dropped = no-section-weaken
