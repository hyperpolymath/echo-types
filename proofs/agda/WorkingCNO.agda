{-# OPTIONS --safe --without-K #-}

module WorkingCNO where

open import Level using (Level; _⊔_)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Data.Nat using (ℕ)
open import Echo

-- Program state model
ProgramState : Set
ProgramState = ℕ → ℕ

-- Identity program (CNO)
id-program : ProgramState → ProgramState
id-program = id

-- CNO as echo: fiber over identity function
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
cno-as-echo-theorem : ∀ (s : ProgramState) → 
                      Echo id-program s → 
                      Σ ProgramState (λ s' → s' ≡ s)
cno-as-echo-theorem s (s' , p) = s' , p

-- Reverse direction: echoes over identity are CNOs
echo-as-cno-theorem : ∀ (s : ProgramState) → 
                      Σ ProgramState (λ s' → s' ≡ s) → 
                      Echo id-program s
echo-as-cno-theorem s (s' , p) = s' , p

-- Isomorphism between CNOs and identity echoes (simplified)
cno-echo-iso : ∀ (s : ProgramState) → 
                Echo id-program s → (Σ ProgramState (λ s' → s' ≡ s))
cno-echo-iso s e = cno-as-echo-theorem s e

cno-echo-iso-inverse : ∀ (s : ProgramState) → 
                       (Σ ProgramState (λ s' → s' ≡ s)) → Echo id-program s
cno-echo-iso-inverse s e' = echo-as-cno-theorem s e'

-- Core functionality complete
-- Export module removed to avoid name clashes