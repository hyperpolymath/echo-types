{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoSourcePreserving where

open import Level using (Level)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Echo using (Echo; echo-intro)

-- Fibre equivalence alone forgets which source supplied an observation.
record FibreIso {a : Level} {A : Set a} (f g : A → A) : Set a where
  field
    to : ∀ {y} → Echo f y → Echo g y
    from : ∀ {y} → Echo g y → Echo f y
    from-to : ∀ {y} (e : Echo f y) → from (to e) ≡ e
    to-from : ∀ {y} (e : Echo g y) → to (from e) ≡ e

SourcePreserving : ∀ {a} {A : Set a} {f g : A → A} → FibreIso f g → Set a
SourcePreserving {f = f} i = ∀ {y} (e : Echo f y) → proj₁ (FibreIso.to i e) ≡ proj₁ e

-- Only the forward map and its source equation are needed for this direction.
source-preserving-implies-identity :
  ∀ {a} {A : Set a} {f : A → A}
  (i : FibreIso f (λ x → x)) → SourcePreserving i → ∀ x → f x ≡ x
source-preserving-implies-identity {f = f} i preserves x =
  trans (sym (proj₂ (FibreIso.to i (echo-intro f x))))
        (preserves (echo-intro f x))

cancel-left : ∀ {a} {A : Set a} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) → trans (sym p) (trans p q) ≡ q
cancel-left refl q = refl

cancel-right : ∀ {a} {A : Set a} {x y z : A}
  (p : x ≡ y) (q : x ≡ z) → trans p (trans (sym p) q) ≡ q
cancel-right refl q = refl

identity-fibre-iso : ∀ {a} {A : Set a} {f : A → A} →
  (∀ x → f x ≡ x) → FibreIso f (λ x → x)
identity-fibre-iso h = record
  { to = λ { (x , p) → x , trans (sym (h x)) p }
  ; from = λ { (x , p) → x , trans (h x) p }
  ; from-to = λ { (x , p) → pair-cong (cancel-right (h x) p) }
  ; to-from = λ { (x , p) → pair-cong (cancel-left (h x) p) }
  }
  where
  pair-cong : ∀ {a b} {X : Set a} {P : X → Set b} {x : X} {p q : P x} →
    p ≡ q → _≡_ {A = Σ X P} (x , p) (x , q)
  pair-cong refl = refl

identity-fibre-iso-preserves-source : ∀ {a} {A : Set a} {f : A → A}
  (h : ∀ x → f x ≡ x) → SourcePreserving (identity-fibre-iso h)
identity-fibre-iso-preserves-source h e = refl

-- Counterexample to the unqualified fibre-equivalence identity criterion.
negation-fibre-iso : FibreIso not (λ x → x)
negation-fibre-iso = record
  { to = λ { (true , p) → false , p ; (false , p) → true , p }
  ; from = λ { (true , p) → false , p ; (false , p) → true , p }
  ; from-to = λ { (true , p) → refl ; (false , p) → refl }
  ; to-from = λ { (true , p) → refl ; (false , p) → refl }
  }

negation-not-identity : (∀ x → not x ≡ x) → ⊥
negation-not-identity h with h true
... | ()

negation-iso-not-source-preserving : SourcePreserving negation-fibre-iso → ⊥
negation-iso-not-source-preserving preserves =
  negation-not-identity (source-preserving-implies-identity negation-fibre-iso preserves)
