{-# OPTIONS --safe --without-K #-}

module EchoJanusSimple where

open import Level using (Level; _⊔_)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool.Base using (Bool; true; false)
open import Data.String using (_≡ᵇ_)
open import Echo

-- Simple bridge between Echo Types and JanusKey's Reversible File Operations

-- File system state: mapping from paths to content
FilePath : Set
FilePath = String

FileContent : Set
FileContent = String

FileSystem : Set
FileSystem = FilePath → Maybe FileContent

-- Initial empty filesystem
empty-fs : FileSystem
empty-fs = λ _ → nothing

-- Delete file
delete-file : FileSystem → FilePath → FileSystem
delete-file fs path = λ p → if p ≡ᵇ path then nothing else fs p

-- JanusKey delete operation as a function
delete-op : FilePath → FileSystem → FileSystem
delete-op path = delete-file

-- Echo type for delete operation
EchoDelete : FilePath → FileSystem → Set
EchoDelete path fs' = Echo (delete-op path) fs'

-- Theorem: Delete operations are reversible via echo types
delete-reversible : ∀ {path : FilePath} {fs' : FileSystem} →
                      EchoDelete path fs' →
                      Sig (fs : FileSystem) (delete-op path fs ≡ fs')
delete-reversible {fs = fs} (fs , p) = fs , p
  where
  Sig = Σ

-- Example: Empty filesystem delete
empty-delete-example : EchoDelete "test.txt" empty-fs
empty-delete-example = empty-fs , refl