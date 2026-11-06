{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- A bounded counterexample to the universal claim that information loss
-- excludes graded comonads.  Grades form the discrete monoid (ℕ, +, 0):
-- grade zero preserves a value and every positive grade erases it.
-- This does not identify the construction with Echo's proposed ordered
-- or tropical model, or claim that its intended erasure map has a section.
module EchoErasingGradedComonad where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-identityˡ; +-identityʳ; +-assoc; ≡-irrelevant; ≤-refl; ≤-trans; +-mono-≤)
open import Data.Unit.Base using (⊤; tt)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong; sym; trans)

open import EchoGradedComonadInterface using (GradedComonadStructure)
open import EchoGradedComonadNaturality using (NaturalGradedComonad)

D : ℕ → Set → Set
D zero A = A
D (suc n) A = ⊤

mapD : ∀ n {A B} → (A → B) → D n A → D n B
mapD zero f x = f x
mapD (suc n) f x = tt

mapD-id : ∀ n {A} (x : D n A) → mapD n (λ a → a) x ≡ x
mapD-id zero x = refl
mapD-id (suc n) x = refl

mapD-∘ : ∀ n {A B C} (f : B → C) (h : A → B) (x : D n A) →
  mapD n (λ a → f (h a)) x ≡ mapD n f (mapD n h x)
mapD-∘ zero f h x = refl
mapD-∘ (suc n) f h x = refl

ε : ∀ {A} → D zero A → A
ε x = x

δ : ∀ g h {A} → D (g + h) A → D g (D h A)
δ zero h x = x
δ (suc g) h x = tt

gc-counit-r : ∀ g {A} (x : D (zero + g) A) →
  ε (δ zero g x) ≡ subst (λ k → D k A) (+-identityˡ g) x
gc-counit-r g x = refl

gc-counit-l : ∀ g {A} (x : D (g + zero) A) →
  mapD g ε (δ g zero x) ≡ subst (λ k → D k A) (+-identityʳ g) x
gc-counit-l zero x = refl
gc-counit-l (suc g) x = refl

gc-coassoc : ∀ g h k {A} (x : D ((g + h) + k) A) →
  δ g h (δ (g + h) k x) ≡
  mapD g (δ h k)
    (δ g (h + k) (subst (λ j → D j A) (+-assoc g h k) x))
gc-coassoc zero zero k x = refl
gc-coassoc zero (suc h) k x = refl
gc-coassoc (suc g) h k x = refl

erasing-instance : GradedComonadStructure
erasing-instance = record
  { G = ℕ
  ; 1G = zero
  ; _·G_ = _+_
  ; ·G-identityˡ = +-identityˡ
  ; ·G-identityʳ = +-identityʳ
  ; ·G-assoc = +-assoc
  ; D = D
  ; mapD = mapD
  ; mapD-id = mapD-id
  ; mapD-∘ = mapD-∘
  ; ε = ε
  ; δ = δ
  ; gc-counit-r = gc-counit-r
  ; gc-counit-l = gc-counit-l
  ; gc-coassoc = gc-coassoc
  }

mapD-cong : ∀ g {A B} {f h : A → B} →
  (∀ a → f a ≡ h a) → ∀ (x : D g A) → mapD g f x ≡ mapD g h x
mapD-cong zero p x = p x
mapD-cong (suc g) p x = refl

ε-natural : ∀ {A B} (f : A → B) (x : D zero A) →
  ε (mapD zero f x) ≡ f (ε x)
ε-natural f x = refl

δ-natural : ∀ g h {A B} (f : A → B) (x : D (g + h) A) →
  δ g h (mapD (g + h) f x) ≡ mapD g (mapD h f) (δ g h x)
δ-natural zero h f x = refl
δ-natural (suc g) h f x = refl

-- This is Nat-specific equality proof uniqueness, obtained in the standard
-- library from decidable Nat equality; it is not a global UIP assumption.
nat-grade-isSet : ∀ {g h : ℕ} (p q : g ≡ h) → p ≡ q
nat-grade-isSet = ≡-irrelevant

erasing-natural : NaturalGradedComonad erasing-instance
erasing-natural = record
  { mapD-cong = mapD-cong
  ; ε-natural = ε-natural
  ; δ-natural = δ-natural
  ; grade-isSet = nat-grade-isSet
  }

erase : ∀ n {A} → A → D (suc n) A
erase n x = tt

bool-input-collision : ∀ n → erase n false ≡ erase n true
bool-input-collision n = refl

false≢true : false ≡ true → ⊥
false≢true ()

-- No left inverse: no recovery function can recover BOTH original inputs.
-- This is deliberately the orientation recover ∘ erase = id, which is
-- the one refuted by a collision (erase ∘ recover = id does hold on ⊤).
positive-erasure-no-left-inverse : ∀ n (recover : D (suc n) Bool → Bool) →
  (∀ b → recover (erase n b) ≡ b) → ⊥
positive-erasure-no-left-inverse n recover left-inverse =
  false≢true (trans (sym (left-inverse false))
    (trans (cong recover (bool-input-collision n)) (left-inverse true)))

----------------------------------------------------------------------
-- A monotone degradation extension for the usual Nat order.
-- Increasing the grade preserves zero-grade data until the first positive
-- grade, then erases it.  The following equations verify naturality,
-- identity/composition, and compatibility with graded comultiplication.
-- They do not assert equivalence with any proposed Echo ordering/model.

grade-change : ∀ {m n A} → m ≤ n → D m A → D n A
grade-change {zero} {zero} p x = x
grade-change {zero} {suc n} p x = tt
grade-change {suc m} {suc n} p x = tt

grade-change-natural : ∀ {m n A B} (p : m ≤ n) (f : A → B)
  (x : D m A) → mapD n f (grade-change p x) ≡
  grade-change p (mapD m f x)
grade-change-natural {zero} {zero} p f x = refl
grade-change-natural {zero} {suc n} p f x = refl
grade-change-natural {suc m} {suc n} p f x = refl

grade-change-id : ∀ n {A} (x : D n A) →
  grade-change {n} {n} {A} ≤-refl x ≡ x
grade-change-id zero x = refl
grade-change-id (suc n) x = refl

grade-change-compose : ∀ {m n k A} (p : m ≤ n) (q : n ≤ k)
  (x : D m A) → grade-change q (grade-change p x) ≡
  grade-change (≤-trans p q) x
grade-change-compose {zero} {zero} {zero} z≤n z≤n x = refl
grade-change-compose {zero} {zero} {suc k} z≤n z≤n x = refl
grade-change-compose {zero} {suc n} {suc k} z≤n (s≤s q) x = refl
grade-change-compose {suc m} {suc n} {suc k} (s≤s p) (s≤s q) x = refl

-- The construction does not depend on the chosen witness of an inequality.
grade-change-proof-independent : ∀ {m n A} (p q : m ≤ n)
  (x : D m A) → grade-change p x ≡ grade-change q x
grade-change-proof-independent {zero} {zero} p q x = refl
grade-change-proof-independent {zero} {suc n} p q x = refl
grade-change-proof-independent {suc m} {suc n} p q x = refl

grade-change-ε : ∀ {A} (x : D zero A) →
  ε (grade-change {zero} {zero} {A} ≤-refl x) ≡ ε x
grade-change-ε x = refl

grade-change-δ : ∀ {g g′ h h′ A} (p : g ≤ g′) (q : h ≤ h′)
  (x : D (g + h) A) →
  δ g′ h′ (grade-change (+-mono-≤ p q) x) ≡
  grade-change p (mapD g (grade-change q) (δ g h x))
grade-change-δ {zero} {zero} {zero} {zero} z≤n z≤n x = refl
grade-change-δ {zero} {zero} {zero} {suc h′} z≤n z≤n x = refl
grade-change-δ {zero} {zero} {suc h} {suc h′} z≤n (s≤s q) x = refl
grade-change-δ {zero} {suc g′} z≤n q x = refl
grade-change-δ {suc g} {suc g′} (s≤s p) q x = refl

-- The explicit loss map is itself a grade-change map out of grade zero.
erase-is-grade-change : ∀ n {A} (x : A) →
  erase n x ≡ grade-change {zero} {suc n} {A} z≤n x
erase-is-grade-change n x = refl
