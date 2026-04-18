{-# OPTIONS --safe --without-K #-}

module EchoCategorical where

open import Echo
open import EchoRelational using (EchoStep; RelMap; map-rel; map-rel-id; map-rel-comp)

open import Level using (Level; _⊔_)
open import Function.Base using (id; _∘_)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)

-- Phase D (part 1): slice-style packaging for deterministic maps.
record SliceHom
  {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  (f : A → B) (f' : A' → B) : Set (a ⊔ a' ⊔ b) where
  field
    arrow : A → A'
    commute : ∀ x → f' (arrow x) ≡ f x

open SliceHom public

slice-to-mapover :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  SliceHom f f' → MapOver f f'
slice-to-mapover h = arrow h , commute h

mapover-to-slice :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  MapOver f f' → SliceHom f f'
mapover-to-slice (u , c) = record { arrow = u ; commute = c }

slice-id :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
  SliceHom f f
slice-id f = record
  { arrow = id
  ; commute = λ _ → refl
  }

slice-comp :
  ∀ {a a' a'' b}
  {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
  {f : A → B} {f' : A' → B} {f'' : A'' → B} →
  SliceHom f f' → SliceHom f' f'' → SliceHom f f''
slice-comp h₁ h₂ = record
  { arrow = arrow h₂ ∘ arrow h₁
  ; commute = λ x → trans (commute h₂ (arrow h₁ x)) (commute h₁ x)
  }

slice-act :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  SliceHom f f' → ∀ {y : B} → Echo f y → Echo f' y
slice-act h = map-over (slice-to-mapover h)

slice-act-id :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} (e : Echo f y) →
  slice-act (slice-id f) e ≡ e
slice-act-id = map-over-id

slice-act-comp :
  ∀ {a a' a'' b}
  {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
  {f : A → B} {f' : A' → B} {f'' : A'' → B}
  (h₁ : SliceHom f f') (h₂ : SliceHom f' f'')
  {y : B} (e : Echo f y) →
  slice-act (slice-comp h₁ h₂) e ≡
  slice-act h₂ (slice-act h₁ e)
slice-act-comp h₁ h₂ = map-over-comp (arrow h₁) (commute h₁) (arrow h₂) (commute h₂)

-- Phase D (part 2): fibration-style packaging for relational semantics.
module Fibration {s o r} {S : Set s} {O : Set o} (Step : S → O → Set r) where

  Fiber : O → Set (s ⊔ r)
  Fiber = EchoStep Step

  Total : Set (s ⊔ o ⊔ r)
  Total = Σ O Fiber

  π : Total → O
  π = proj₁

  fiber-to-echo :
    ∀ {out : O} → Fiber out → Echo π out
  fiber-to-echo {out} e = (out , e) , refl

  echo-to-fiber :
    ∀ {out : O} → Echo π out → Fiber out
  echo-to-fiber ((out' , e) , p) = subst Fiber p e

  echo-to-fiber∘fiber-to-echo :
    ∀ {out : O} (e : Fiber out) →
    echo-to-fiber (fiber-to-echo e) ≡ e
  echo-to-fiber∘fiber-to-echo e = refl

  fiber-map :
    ∀ {s' r'} {S' : Set s'} {Step' : S' → O → Set r'} →
    RelMap Step Step' → ∀ {out : O} → Fiber out → EchoStep Step' out
  fiber-map = map-rel

  fiber-map-id :
    ∀ {out : O} (e : Fiber out) →
    fiber-map (id , (λ {st} {out} p → p)) e ≡ e
  fiber-map-id e = map-rel-id {Step = Step} e

  rel-fiber-map-comp :
    ∀ {s' s'' r' r''}
    {S' : Set s'} {S'' : Set s''}
    {Step' : S' → O → Set r'}
    {Step'' : S'' → O → Set r''}
    (u₁ : S → S') (pres₁ : ∀ {st out} → Step st out → Step' (u₁ st) out)
    (u₂ : S' → S'') (pres₂ : ∀ {st out} → Step' st out → Step'' (u₂ st) out)
    {out : O} (e : Fiber out) →
    map-rel {Step = Step} {Step' = Step''}
      (u₂ ∘ u₁ , λ p → pres₂ (pres₁ p)) e
    ≡ map-rel {Step = Step'} {Step' = Step''} (u₂ , pres₂)
        (map-rel {Step = Step} {Step' = Step'} (u₁ , pres₁) e)
  rel-fiber-map-comp {Step' = Step'} {Step'' = Step''} u₁ pres₁ u₂ pres₂ e =
    map-rel-comp {Step = Step} {Step' = Step'} {Step'' = Step''}
      u₁ pres₁ u₂ pres₂ e
