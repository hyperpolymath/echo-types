{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoFiniteResidue where

open import Level using (Level; _⊔_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (injective⇒≤)
open import Data.Nat.Base using (ℕ; _≤_; s≤s)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong₂)

-- Recover SOURCE VALUES from the retained pair. This contract does not
-- reconstruct equality witnesses in Echo, make every residue valid, or
-- identify a physical/bit/entropy cost. A total decoder is supplied explicitly.
record ExactRecovery {a b r : Level} {A : Set a} {B : Set b} {R : Set r}
  (observe : A → B) (retain : A → R) : Set (a ⊔ b ⊔ r) where
  field
    recover : B → R → A
    roundtrip : ∀ x → recover (observe x) (retain x) ≡ x

recovery-separates : ∀ {a b r} {A : Set a} {B : Set b} {R : Set r}
  {observe : A → B} {retain : A → R} → ExactRecovery observe retain →
  ∀ {x z} → observe x ≡ observe z → retain x ≡ retain z → x ≡ z
recovery-separates recovery {x} {z} same-output same-residue =
  trans (sym (ExactRecovery.roundtrip recovery x))
    (trans (cong₂ (ExactRecovery.recover recovery) same-output same-residue)
           (ExactRecovery.roundtrip recovery z))

-- Distinct sources in one fibre must remain distinguishable in the residue.
-- This is also the boundary for PUBLIC exact reconstruction: it preserves
-- these source distinctions, independently of any security-policy model.
recovery-forbids-residue-collision :
  ∀ {a b r} {A : Set a} {B : Set b} {R : Set r}
  {observe : A → B} {retain : A → R} → ExactRecovery observe retain →
  ∀ {x z} → x ≢ z → observe x ≡ observe z → retain x ≢ retain z
recovery-forbids-residue-collision recovery different same-output same-residue =
  different (recovery-separates recovery same-output same-residue)

-- A supplied injection enumerates n distinct sources in ONE output fibre.
-- It need not enumerate the entire source type or the entire fibre. The
-- representation class is Fin k, and the cost is alphabet cardinality k.
-- This is a specialization of the standard finite pigeonhole bound.
finite-fibre-bound : ∀ {a b} {A : Set a} {B : Set b}
  {observe : A → B} {n k : ℕ} {retain : A → Fin k} →
  ExactRecovery observe retain →
  (select : Fin n → A) →
  (∀ {i j} → select i ≡ select j → i ≡ j) →
  (y : B) → (∀ i → observe (select i) ≡ y) → n ≤ k
finite-fibre-bound {retain = retain} recovery select injective y in-fibre =
  injective⇒≤ {f = λ i → retain (select i)}
    (λ {i} {j} same-residue → injective
      (recovery-separates recovery
        (trans (in-fibre i) (sym (in-fibre j))) same-residue))

-- The lower bound is attained for constant observations on Fin n by
-- retaining the source itself. This is a tight example, not a uniform
-- optimum construction for arbitrary observations or encodings.
constant-recovery : (n : ℕ) →
  ExactRecovery {A = Fin n} (λ _ → tt) (λ x → x)
constant-recovery n = record
  { recover = λ _ r → r
  ; roundtrip = λ x → refl
  }

constant-bound : ∀ {n k} (retain : Fin n → Fin k) →
  ExactRecovery (λ _ → tt) retain → n ≤ k
constant-bound retain recovery =
  finite-fibre-bound recovery (λ i → i) (λ p → p) tt (λ _ → refl)

-- A concrete impossible encoding: two source values cannot be recovered
-- from a constant observation and a one-symbol residue alphabet.
no-one-symbol-for-two : (retain : Fin 2 → Fin 1) →
  ExactRecovery (λ _ → tt) retain → ⊥
no-one-symbol-for-two retain recovery with constant-bound retain recovery
... | s≤s ()
