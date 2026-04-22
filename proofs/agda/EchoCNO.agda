{-# OPTIONS --safe --without-K #-}

module EchoCNO where

open import Level using (Level; _⊔_)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Echo

-- Import CNO concepts (simplified for bridging)
-- We'll model CNOs as programs that preserve state (identity function)

-- Program state as a simple model
ProgramState : Set
ProgramState = ℕ → ℕ  -- Simplified memory model

-- Identity program (CNO)
id-program : ProgramState → ProgramState
id-program = id

-- Echo type for CNO: fiber over identity function
-- Echo id-program s = Σ (s' : ProgramState) (λ _ → id-program s' ≡ s)
-- This simplifies to: Σ (s' : ProgramState) (λ _ → s' ≡ s)
-- Which is essentially the singleton fiber containing only s

-- CNO as echo: the fiber contains exactly the original state
CNO-Echo : (s : ProgramState) → Echo id-program s
CNO-Echo s = s , refl

-- CNO preservation: mapping over identity preserves the echo
cno-preservation : ∀ {s : ProgramState} → Echo id-program s → Echo id-program s
cno-preservation e = e

-- CNO composition: composing identity with itself preserves echoes
cno-composition : ∀ {s : ProgramState} (e : Echo id-program s) → 
                   map-over (id , (λ x → refl)) e ≡ e
cno-composition (s , p) = refl

-- Bridge theorem: CNOs are echoes over identity functions
-- This shows that CNOs can be formalized as a special case of echo types
-- where the computation is the identity function (no state change)
cno-as-echo-theorem : ∀ (s : ProgramState) → 
                      Echo id-program s → 
                      Σ (s' : ProgramState) (λ _ → s' ≡ s)
cno-as-echo-theorem s (s' , p) = s' , p

-- Reverse direction: echoes over identity are CNOs
echo-as-cno-theorem : ∀ (s : ProgramState) → 
                      Σ (s' : ProgramState) (λ _ → s' ≡ s) → 
                      Echo id-program s
echo-as-cno-theorem s (s' , p) = s' , p

-- Equivalence between CNOs and identity echoes
cno-echo-equivalence : ∀ (s : ProgramState) → 
                        Echo id-program s ≃ (Σ (s' : ProgramState) (λ _ → s' ≡ s))
cno-echo-equivalence s = 
  (λ e → cno-as-echo-theorem s e) , 
  (λ e' → echo-as-cno-theorem s e') , 
  (λ e → refl) , 
  (λ e' → refl)

where
  open import Function.Equivalence using (_≃_; module Equivalence)
  open import Data.Product using (∃-syntax)
  open import Relation.Binary.PropositionalEquality.TrustMe