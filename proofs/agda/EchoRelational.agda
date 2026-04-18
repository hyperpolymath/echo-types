{-# OPTIONS --safe --without-K #-}

module EchoRelational where

open import Echo using (Echo)

open import Level using (Level; _⊔_)
open import Function.Base using (id; _∘_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

-- Phase C: relational/nondeterministic semantics.
EchoStep :
  ∀ {s o r} {S : Set s} {O : Set o} →
  (Step : S → O → Set r) → O → Set (s ⊔ r)
EchoStep {S = S} Step out = Σ S (λ st → Step st out)

step-intro :
  ∀ {s o r} {S : Set s} {O : Set o}
  {Step : S → O → Set r} {st : S} {out : O} →
  Step st out → EchoStep Step out
step-intro {st = st} p = st , p

RelMap :
  ∀ {s s' o r r'}
  {S : Set s} {S' : Set s'} {O : Set o} →
  (Step : S → O → Set r) → (Step' : S' → O → Set r') →
  Set (s ⊔ s' ⊔ o ⊔ r ⊔ r')
RelMap {S = S} {S' = S'} Step Step' =
  Σ (S → S') (λ u → ∀ {st out} → Step st out → Step' (u st) out)

map-rel :
  ∀ {s s' o r r'}
  {S : Set s} {S' : Set s'} {O : Set o}
  {Step : S → O → Set r} {Step' : S' → O → Set r'} →
  RelMap Step Step' → ∀ {out : O} → EchoStep Step out → EchoStep Step' out
map-rel (u , preserve) (st , p) = u st , preserve p

map-rel-id :
  ∀ {s o r}
  {S : Set s} {O : Set o} {Step : S → O → Set r}
  {out : O} (e : EchoStep Step out) →
  map-rel {Step = Step} {Step' = Step}
    (id , (λ {st} {out} p → p)) e ≡ e
map-rel-id (st , p) = refl

map-rel-comp :
  ∀ {s s' s'' o r r' r''}
  {S : Set s} {S' : Set s'} {S'' : Set s''} {O : Set o}
  {Step : S → O → Set r}
  {Step' : S' → O → Set r'}
  {Step'' : S'' → O → Set r''}
  (u₁ : S → S') (pres₁ : ∀ {st out} → Step st out → Step' (u₁ st) out)
  (u₂ : S' → S'') (pres₂ : ∀ {st out} → Step' st out → Step'' (u₂ st) out)
  {out : O} (e : EchoStep Step out) →
  map-rel {Step = Step} {Step' = Step''}
    (u₂ ∘ u₁ , λ p → pres₂ (pres₁ p)) e
  ≡ map-rel {Step = Step'} {Step' = Step''} (u₂ , pres₂)
      (map-rel {Step = Step} {Step' = Step'} (u₁ , pres₁) e)
map-rel-comp u₁ pres₁ u₂ pres₂ (st , p) = refl

map-rel-square :
  ∀ {s s' o o' r r'}
  {S : Set s} {S' : Set s'} {O : Set o} {O' : Set o'}
  (Step : S → O → Set r) (Step' : S' → O' → Set r')
  (u : S → S') (v : O → O')
  (square : ∀ {st out} → Step st out → Step' (u st) (v out))
  {out : O} →
  EchoStep Step out → EchoStep Step' (v out)
map-rel-square Step Step' u v square (st , p) = u st , square p

-- Deterministic functions embed as graph relations.
Graph :
  ∀ {s o} {S : Set s} {O : Set o} →
  (f : S → O) → S → O → Set o
Graph f st out = f st ≡ out

echo-to-graph :
  ∀ {s o} {S : Set s} {O : Set o}
  {f : S → O} {out : O} →
  Echo f out → EchoStep (Graph f) out
echo-to-graph (st , p) = st , p

graph-to-echo :
  ∀ {s o} {S : Set s} {O : Set o}
  {f : S → O} {out : O} →
  EchoStep (Graph f) out → Echo f out
graph-to-echo (st , p) = st , p

-- Nondeterministic example.
data StepND : Bool → Bool → Set where
  stay-true : StepND true true
  stay-false : StepND false false
  flip-to-true : StepND false true

true≢false : true ≢ false
true≢false ()

nd-echo-from-true : EchoStep StepND true
nd-echo-from-true = true , stay-true

nd-echo-from-false : EchoStep StepND true
nd-echo-from-false = false , flip-to-true

nd-echo-from-true≢nd-echo-from-false :
  nd-echo-from-true ≢ nd-echo-from-false
nd-echo-from-true≢nd-echo-from-false p = true≢false (cong proj₁ p)

nd-true-fiber-classification :
  ∀ (e : EchoStep StepND true) →
  proj₁ e ≡ true ⊎ proj₁ e ≡ false
nd-true-fiber-classification (true , stay-true) = inj₁ refl
nd-true-fiber-classification (false , flip-to-true) = inj₂ refl
