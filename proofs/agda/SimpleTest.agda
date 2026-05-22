{-# OPTIONS --safe --without-K #-}

module SimpleTest where

open import Level using (Level; _⊔_)
open import Function.Base using (id)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Echo

-- Simple test to verify basic echo functionality
simple-echo-test : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → Echo f (f x)
simple-echo-test f x = echo-intro f x

-- Test that echo introduction works
simple-test-correct : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → 
                      proj₁ (simple-echo-test f x) ≡ x
simple-test-correct f x = refl

-- Proof assertion: Basic echo functionality is stable
basic-stability : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → 
                  simple-echo-test f x ≡ echo-intro f x
basic-stability f x = refl