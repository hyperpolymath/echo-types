{-# OPTIONS --safe --without-K #-}

-- Dyadic Type Theory (E11) - Functional Core
--
-- Formalization of two-party protocol types with dual checking.
-- Simplified to focus on the core dyadic session type structure.

module Dyadic where

open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)

-- Party roles in dyadic protocols
data Party : Set where
  Alice : Party
  Bob   : Party

-- Dual party (protocol counterpart)
dual : Party → Party
dual Alice = Bob
dual Bob = Alice

-- Duality properties
dual-involutive : ∀ p → dual (dual p) ≡ p
dual-involutive Alice = refl
dual-involutive Bob = refl

-- Message types for communication
data Message : Set where
  UnitMsg : Message
  BoolMsg : Bool → Message
  NatMsg  : ℕ → Message

-- Dyadic session types (simplified structure)
data Session : Party → Set where
  -- End: protocol completion
  End : ∀ {p} → Session p
  
  -- Send: party p sends message, continues as S
  Send : ∀ {p} → Message → Session p → Session p
  
  -- Receive: party p receives message, continues as S
  Recv : ∀ {p} → Message → Session p → Session p
  
  -- Choice: party p offers external choice
  Choice : ∀ {p} → Session p → Session p → Session p
  
  -- Select: party p selects between choices
  Select : ∀ {p} → Session p → Session p → Session p

-- Basic session type examples

-- Alice sends UnitMsg, then ends
AliceSendsUnit : Session Alice
AliceSendsUnit = Send UnitMsg End

-- Bob receives UnitMsg, then ends
BobReceivesUnit : Session Bob
BobReceivesUnit = Recv UnitMsg End

-- Alice offers choice between two protocols
AliceChoice : Session Alice
AliceChoice = Choice (Send UnitMsg End) (Send (BoolMsg true) End)

-- Bob selects first option
BobSelectsFirst : Session Bob
BobSelectsFirst = Select (Recv UnitMsg End) (Recv (BoolMsg true) End)

-- Session type safety (simplified)
data Safe {p} : Session p → Set where
  safe-end : Safe End
  safe-send : ∀ {A} {S} → Safe S → Safe (Send A S)
  safe-recv : ∀ {A} {S} → Safe S → Safe (Recv A S)
  safe-choice : ∀ {S1} {S2} → Safe S1 → Safe S2 → Safe (Choice S1 S2)
  safe-select : ∀ {S1} {S2} → Safe S1 → Safe S2 → Safe (Select S1 S2)

-- Safety examples
AliceSendsUnit-safe : Safe AliceSendsUnit
AliceSendsUnit-safe = safe-send safe-end

BobReceivesUnit-safe : Safe BobReceivesUnit
BobReceivesUnit-safe = safe-recv safe-end

AliceChoice-safe : Safe AliceChoice
AliceChoice-safe = safe-choice (safe-send safe-end) (safe-send safe-end)

BobSelectsFirst-safe : Safe BobSelectsFirst
BobSelectsFirst-safe = safe-select (safe-recv safe-end) (safe-recv safe-end)

-- Protocol compatibility (simplified: same party, structural equivalence)
Compatible : ∀ {p} → Session p → Session p → Set
Compatible {p} S T = S ≡ T

-- Compatibility is reflexive
Compatible-refl : ∀ {p} {S : Session p} → Compatible S S
Compatible-refl = refl

-- Session type operations

-- Session concatenation
infixr 5 _>>=_
_>>=_ : ∀ {p} → Session p → Session p → Session p
End >>= S = S
(Send A S1) >>= S2 = Send A (S1 >>= S2)
(Recv A S1) >>= S2 = Recv A (S1 >>= S2)
(Choice S1 S2) >>= S3 = Choice (S1 >>= S3) (S2 >>= S3)
(Select S1 S2) >>= S3 = Select (S1 >>= S3) (S2 >>= S3)

-- Concatenation preserves safety
>>=-preserves-safe : ∀ {p} {S1 S2 : Session p} → Safe S1 → Safe S2 → Safe (S1 >>= S2)
>>=-preserves-safe safe-end safeS2 = safeS2
>>=-preserves-safe (safe-send safeS1) safeS2 = safe-send (>>=-preserves-safe safeS1 safeS2)
>>=-preserves-safe (safe-recv safeS1) safeS2 = safe-recv (>>=-preserves-safe safeS1 safeS2)
>>=-preserves-safe (safe-choice safeS1 safeS2) safeS3 =
  safe-choice (>>=-preserves-safe safeS1 safeS3) (>>=-preserves-safe safeS2 safeS3)
>>=-preserves-safe (safe-select safeS1 safeS2) safeS3 =
  safe-select (>>=-preserves-safe safeS1 safeS3) (>>=-preserves-safe safeS2 safeS3)

-- Example: Alice sends unit, then sends bool
AliceDoubleSend : Session Alice
AliceDoubleSend = Send UnitMsg (Send (BoolMsg true) End)

AliceDoubleSend-safe : Safe AliceDoubleSend
AliceDoubleSend-safe = safe-send (safe-send safe-end)

-- Dyadic protocol composition
AliceComplexProtocol : Session Alice
AliceComplexProtocol = Choice (Send UnitMsg End) (Send (NatMsg 42) End)

AliceComplexProtocol-safe : Safe AliceComplexProtocol
AliceComplexProtocol-safe = safe-choice (safe-send safe-end) (safe-send safe-end)

-- Note: Full duality theory would require more complex type structure
-- This implementation focuses on the core dyadic session type structure
-- that can be integrated with echo types for provenance tracking
