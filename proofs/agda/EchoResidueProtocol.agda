{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoResidueProtocol where

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Echo using (Echo)
open import EchoCharacteristic using (echo-true)
open import EchoResidueCell using (ResidueCell; holding; spent; takeForReverse; consume)

-- One authoritative state trajectory is an explicit model assumption.
-- A runtime or typing discipline must still enforce that assumption. These
-- sequential traces do not make pure Agda values affine or linear, prevent
-- aliases, establish heap uniqueness/concurrency safety, or refine a runtime.
-- There is no rearming transition in this model.
data Event {a : Level} (A : Set a) : Set a where
  idle : Event A
  reversed : A → Event A

data Step {a b : Level} {A : Set a} {B : Set b} {f : A → B} {y : B} :
  ResidueCell f y → Event A → ResidueCell f y → Set (a ⊔ b) where
  idle-step : ∀ {c} → Step c idle c
  reverse-step : (e : Echo f y) → Step (holding e) (reversed (proj₁ e)) spent

-- Each next step starts at precisely the state returned by its predecessor.
data Trace {a b : Level} {A : Set a} {B : Set b} {f : A → B} {y : B} :
  ResidueCell f y → List (Event A) → ResidueCell f y → Set (a ⊔ b) where
  done : ∀ {c} → Trace c [] c
  more : ∀ {c d e action actions} → Step c action d → Trace d actions e →
    Trace c (action ∷ actions) e

reversal-count : ∀ {a} {A : Set a} → List (Event A) → ℕ
reversal-count [] = zero
reversal-count (idle ∷ actions) = reversal-count actions
reversal-count (reversed x ∷ actions) = suc (reversal-count actions)

spent-trace-zero : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {actions end} → Trace {f = f} {y = y} spent actions end →
  reversal-count actions ≡ zero
spent-trace-zero done = refl
spent-trace-zero (more idle-step trace) = spent-trace-zero trace

trace-at-most-one : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {start actions end} → Trace {f = f} {y = y} start actions end →
  reversal-count actions ≤ suc zero
trace-at-most-one done = z≤n
trace-at-most-one (more idle-step trace) = trace-at-most-one trace
trace-at-most-one (more (reverse-step e) trace) rewrite spent-trace-zero trace = s≤s z≤n

reversing-step-agrees : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {start end x} → Step {f = f} {y = y} start (reversed x) end →
  (takeForReverse start ≡ just x) × (consume start ≡ end)
reversing-step-agrees (reverse-step e) = refl , refl

one-reversal-trace : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  (e : Echo f y) → Trace (holding e) (reversed (proj₁ e) ∷ []) spent
one-reversal-trace e = more (reverse-step e) done

no-two-reversal-trace : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {start end x z} → Trace {f = f} {y = y} start (reversed x ∷ reversed z ∷ []) end → ⊥
no-two-reversal-trace trace with trace-at-most-one trace
... | s≤s ()

-- Concrete negative control: even reusing the same recovered Bool cannot
-- produce two reversals along a valid single-cell state trajectory.
no-two-true-reversals : ∀ {end} →
  Trace (holding echo-true) (reversed true ∷ reversed true ∷ []) end → ⊥
no-two-true-reversals = no-two-reversal-trace
