{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoSourcePreservingComparison where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Echo using (Echo; echo-intro)
open import EchoSourcePreserving using (cancel-left; cancel-right)

record SourcePreservingFibreMap {a b : Level} {A : Set a} {B : Set b}
  (f g : A → B) : Set (a ⊔ b) where
  field
    map : ∀ {y} → Echo f y → Echo g y
    source-preserved : ∀ {y} (e : Echo f y) → proj₁ (map e) ≡ proj₁ e

record FibreComparisonIso {a b : Level} {A : Set a} {B : Set b}
  (f g : A → B) : Set (a ⊔ b) where
  field
    forward : SourcePreservingFibreMap f g
    backward : SourcePreservingFibreMap g f
    backward-forward : ∀ {y} (e : Echo f y) →
      SourcePreservingFibreMap.map backward (SourcePreservingFibreMap.map forward e) ≡ e
    forward-backward : ∀ {y} (e : Echo g y) →
      SourcePreservingFibreMap.map forward (SourcePreservingFibreMap.map backward e) ≡ e

pointwise-fibre-map : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} →
  (∀ x → f x ≡ g x) → SourcePreservingFibreMap f g
pointwise-fibre-map h = record
  { map = λ { (x , p) → x , trans (sym (h x)) p }
  ; source-preserved = λ e → refl
  }

-- One forward map suffices; no inverse assumption is used here.
source-map-pointwise : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} →
  SourcePreservingFibreMap f g → ∀ x → f x ≡ g x
source-map-pointwise {f = f} {g = g} m x =
  trans (sym (proj₂ (SourcePreservingFibreMap.map m (echo-intro f x))))
        (cong g (SourcePreservingFibreMap.source-preserved m (echo-intro f x)))

-- These inverse equations concern the maps induced by the given pointwise
-- equation. They do not classify arbitrary fibre equivalences.
pointwise-fibre-iso : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} →
  (∀ x → f x ≡ g x) → FibreComparisonIso f g
pointwise-fibre-iso h = record
  { forward = pointwise-fibre-map h
  ; backward = record
      { map = λ { (x , p) → x , trans (h x) p }
      ; source-preserved = λ e → refl
      }
  ; backward-forward = λ { (x , p) → pair-cong (cancel-right (h x) p) }
  ; forward-backward = λ { (x , p) → pair-cong (cancel-left (h x) p) }
  }
  where
  pair-cong : ∀ {a b} {X : Set a} {P : X → Set b} {x : X} {p q : P x} →
    p ≡ q → _≡_ {A = Σ X P} (x , p) (x , q)
  pair-cong refl = refl
