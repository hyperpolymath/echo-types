{-# OPTIONS --safe --without-K #-}

module MinimalCNO where

open import Level using (Level; _⊔_)
open import Function.Base using (id)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ)
open import Echo

-- Minimal ProgramState definition
ProgramState : Set
ProgramState = ℕ → ℕ

-- Identity program (CNO)
id-program : ProgramState → ProgramState
id-program = id

-- CNO as echo: fiber over identity
CNO-Echo : (s : ProgramState) → Echo id-program s
CNO-Echo s = s , refl

-- Test: CNO echo is well-formed
cno-echo-test : ∀ (s : ProgramState) → Echo id-program s
cno-echo-test s = CNO-Echo s

-- Proof assertion: CNO echo is correct
cno-echo-correct : ∀ (s : ProgramState) → proj₁ (cno-echo-test s) ≡ s
cno-echo-correct s = refl