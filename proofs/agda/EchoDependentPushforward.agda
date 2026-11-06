{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EchoDependentPushforward where

open import Level using (Level)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Echo using (Echo)

-- Fam(A), with families at one common universe and pointwise hom equality.
-- This is explicit hom-setoid mathematics; no function extensionality,
-- resizing, global UIP, or claim that all Agda types are h-sets is used.
Hom : ∀ {ℓ} {A : Set ℓ} → (A → Set ℓ) → (A → Set ℓ) → Set ℓ
Hom {A = A} P Q = ∀ a → P a → Q a

HomEq : ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ} → Hom P Q → Hom P Q → Set ℓ
HomEq u v = ∀ a x → u a x ≡ v a x

idH : ∀ {ℓ} {A : Set ℓ} {P : A → Set ℓ} → Hom P P
idH a x = x

composeH : ∀ {ℓ} {A : Set ℓ} {P Q R : A → Set ℓ} → Hom Q R → Hom P Q → Hom P R
composeH v u a x = v a (u a x)

hom-refl : ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ} (u : Hom P Q) → HomEq u u
hom-refl u a x = refl

hom-sym : ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ} {u v : Hom P Q} → HomEq u v → HomEq v u
hom-sym e a x = sym (e a x)

hom-trans : ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ} {u v w : Hom P Q} →
  HomEq u v → HomEq v w → HomEq u w
hom-trans e d a x = trans (e a x) (d a x)

compose-cong : ∀ {ℓ} {A : Set ℓ} {P Q R : A → Set ℓ}
  {u u' : Hom P Q} {v v' : Hom Q R} → HomEq u u' → HomEq v v' →
  HomEq (composeH v u) (composeH v' u')
compose-cong {v = v} e d a x = trans (cong (v a) (e a x)) (d a _)

identity-left : ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ} (u : Hom P Q) → HomEq (composeH idH u) u
identity-left u a x = refl

identity-right : ∀ {ℓ} {A : Set ℓ} {P Q : A → Set ℓ} (u : Hom P Q) → HomEq (composeH u idH) u
identity-right u a x = refl

compose-assoc : ∀ {ℓ} {A : Set ℓ} {P Q R S : A → Set ℓ}
  (w : Hom R S) (v : Hom Q R) (u : Hom P Q) →
  HomEq (composeH (composeH w v) u) (composeH w (composeH v u))
compose-assoc w v u a x = refl

Push : ∀ {ℓ} {A B : Set ℓ} → (A → B) → (A → Set ℓ) → B → Set ℓ
Push {A = A} f P b = Σ A (λ a → (f a ≡ b) × P a)

Reindex : ∀ {ℓ} {A B : Set ℓ} → (A → B) → (B → Set ℓ) → A → Set ℓ
Reindex f Q a = Q (f a)

push-map : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P P' : A → Set ℓ} → Hom P P' → Hom (Push f P) (Push f P')
push-map f u b (a , e , x) = a , e , u a x

reindex-map : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {Q Q' : B → Set ℓ} → Hom Q Q' → Hom (Reindex f Q) (Reindex f Q')
reindex-map f v a x = v (f a) x

push-cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P P' : A → Set ℓ} {u v : Hom P P'} →
  HomEq u v → HomEq (push-map f u) (push-map f v)
push-cong f h b (a , e , x) = cong (λ z → a , e , z) (h a x)

push-id : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} → HomEq (push-map f (idH {P = P})) idH
push-id f b (a , e , x) = refl

push-compose : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P Q R : A → Set ℓ} (v : Hom Q R) (u : Hom P Q) →
  HomEq (push-map f (composeH v u)) (composeH (push-map f v) (push-map f u))
push-compose f v u b (a , e , x) = refl

reindex-cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {Q Q' : B → Set ℓ} {u v : Hom Q Q'} →
  HomEq u v → HomEq (reindex-map f u) (reindex-map f v)
reindex-cong f e a x = e (f a) x

reindex-id : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {Q : B → Set ℓ} → HomEq (reindex-map f (idH {P = Q})) idH
reindex-id f a x = refl

reindex-compose : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P Q R : B → Set ℓ} (v : Hom Q R) (u : Hom P Q) →
  HomEq (reindex-map f (composeH v u)) (composeH (reindex-map f v) (reindex-map f u))
reindex-compose f v u a x = refl

-- Natural hom correspondence: Hom(Push f P,Q) ≅ Hom(P,Reindex f Q).
transpose : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} {Q : B → Set ℓ} →
  Hom (Push f P) Q → Hom P (Reindex f Q)
transpose f h a x = h (f a) (a , refl , x)

untranspose : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} {Q : B → Set ℓ} →
  Hom P (Reindex f Q) → Hom (Push f P) Q
untranspose f k b (a , refl , x) = k a x

transpose-cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} {Q : B → Set ℓ}
  {h h' : Hom (Push f P) Q} → HomEq h h' → HomEq (transpose f h) (transpose f h')
transpose-cong f e a x = e (f a) (a , refl , x)

untranspose-cong : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} {Q : B → Set ℓ}
  {k k' : Hom P (Reindex f Q)} → HomEq k k' →
  HomEq (untranspose f {P = P} {Q = Q} k) (untranspose f {P = P} {Q = Q} k')
untranspose-cong f e b (a , refl , x) = e a x

transpose-untranspose : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} {Q : B → Set ℓ}
  (k : Hom P (Reindex f Q)) →
  HomEq (transpose f {P = P} {Q = Q} (untranspose f {P = P} {Q = Q} k)) k
transpose-untranspose f k a x = refl

untranspose-transpose : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P : A → Set ℓ} {Q : B → Set ℓ}
  (h : Hom (Push f P) Q) → HomEq (untranspose f (transpose f h)) h
untranspose-transpose f h b (a , refl , x) = refl

transpose-natural-source : ∀ {ℓ} {A B : Set ℓ} (f : A → B)
  {P P' : A → Set ℓ} {Q : B → Set ℓ} (u : Hom P' P) (h : Hom (Push f P) Q) →
  HomEq (transpose f (composeH h (push-map f u))) (composeH (transpose f h) u)
transpose-natural-source f u h a x = refl

transpose-natural-target : ∀ {ℓ} {A B : Set ℓ} (f : A → B)
  {P : A → Set ℓ} {Q Q' : B → Set ℓ} (v : Hom Q Q') (h : Hom (Push f P) Q) →
  HomEq (transpose f (composeH v h)) (composeH (reindex-map f v) (transpose f h))
transpose-natural-target f v h a x = refl

unit : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (P : A → Set ℓ) → Hom P (Reindex f (Push f P))
unit f P a x = a , refl , x

counit : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (Q : B → Set ℓ) → Hom (Push f (Reindex f Q)) Q
counit f Q = untranspose f idH

unit-natural : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {P P' : A → Set ℓ} (u : Hom P P') →
  HomEq (composeH (reindex-map f (push-map f u)) (unit f P)) (composeH (unit f P') u)
unit-natural f u a x = refl

counit-natural : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {Q Q' : B → Set ℓ} (v : Hom Q Q') →
  HomEq (composeH v (counit f Q)) (composeH (counit f Q') (push-map f (reindex-map f v)))
counit-natural f v b (a , refl , x) = refl

triangle-push : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (P : A → Set ℓ) →
  HomEq (composeH (counit f (Push f P)) (push-map f (unit f P))) idH
triangle-push f P b (a , refl , x) = refl

triangle-reindex : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (Q : B → Set ℓ) →
  HomEq (composeH (reindex-map f (counit f Q)) (unit f (Reindex f Q))) idH
triangle-reindex f Q a x = refl

-- Echo is the pushforward of the terminal family, with explicit inverse maps.
echo-to-push : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {b} → Echo f b → Push f (λ _ → ⊤ {ℓ}) b
echo-to-push f (a , e) = a , e , tt

push-to-echo : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {b} → Push f (λ _ → ⊤ {ℓ}) b → Echo f b
push-to-echo f (a , e , tt) = a , e

echo-roundtrip : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {b} (e : Echo f b) → push-to-echo f (echo-to-push f e) ≡ e
echo-roundtrip f (a , e) = refl

terminal-push-roundtrip : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {b} (e : Push f (λ _ → ⊤ {ℓ}) b) →
  echo-to-push f (push-to-echo f e) ≡ e
terminal-push-roundtrip f (a , e , tt) = refl

-- Dependent pushforward composition, natural in the input family.
push-composite-to : ∀ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C) {P : A → Set ℓ} →
  Hom (Push g (Push f P)) (Push (λ a → g (f a)) P)
push-composite-to f g c (b , q , a , refl , x) = a , q , x

push-composite-from : ∀ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C) {P : A → Set ℓ} →
  Hom (Push (λ a → g (f a)) P) (Push g (Push f P))
push-composite-from f g c (a , q , x) = f a , q , a , refl , x

push-composite-from-to : ∀ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C) {P : A → Set ℓ} →
  HomEq (composeH (push-composite-from f g {P}) (push-composite-to f g)) idH
push-composite-from-to f g c (b , q , a , refl , x) = refl

push-composite-to-from : ∀ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C) {P : A → Set ℓ} →
  HomEq (composeH (push-composite-to f g {P}) (push-composite-from f g)) idH
push-composite-to-from f g c (a , q , x) = refl

push-composite-natural : ∀ {ℓ} {A B C : Set ℓ} (f : A → B) (g : B → C)
  {P P' : A → Set ℓ} (u : Hom P P') →
  HomEq (composeH (push-map (λ a → g (f a)) u) (push-composite-to f g))
        (composeH (push-composite-to f g) (push-map g (push-map f u)))
push-composite-natural f g u c (b , q , a , refl , x) = refl
