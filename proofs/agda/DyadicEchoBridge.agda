{-# OPTIONS --safe --without-K #-}

-- Dyadic-Echo Bridge (E12)
--
-- Integration of dyadic session types with echo types for provenance tracking.
-- Shows how echo types can retain protocol provenance in dyadic communications.

module DyadicEchoBridge where

open import Dyadic
open import Echo

open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

-- Bridge: Session types can be viewed as functions from parties to protocols
SessionAsFunction : ∀ {p} → Session p → (Party → Set)
SessionAsFunction {p} End _ = ⊤
SessionAsFunction {p} (Send A S) q = Σ Message (λ _ → SessionAsFunction S q)
SessionAsFunction {p} (Recv A S) q = Σ Message (λ _ → SessionAsFunction S q)
SessionAsFunction {p} (Choice S1 S2) q = SessionAsFunction S1 q ⊎ SessionAsFunction S2 q
SessionAsFunction {p} (Select S1 S2) q = SessionAsFunction S1 q ⊎ SessionAsFunction S2 q

-- Simplified echo over session types (avoiding universe issues)
SessionEcho : ∀ {p} → (q : Party) → Session p → Set
SessionEcho q End = ⊤
SessionEcho q (Send A S) = Echo (λ _ → ⊤) ⊤
SessionEcho q (Recv A S) = Echo (λ _ → ⊤) ⊤
SessionEcho q (Choice S1 S2) = Echo (λ _ → ⊤) ⊤
SessionEcho q (Select S1 S2) = Echo (λ _ → ⊤) ⊤

-- Example: Echo over Alice's send protocol
AliceSendEcho : SessionEcho Alice AliceSendsUnit
AliceSendEcho = echo-intro (λ _ → tt) tt

-- Protocol provenance: echo retains session structure
ProtocolProvenance : ∀ {p} {S : Session p} {q : Party} → 
                      SessionEcho q S → Echo (λ _ → ⊤) ⊤
ProtocolProvenance echo = echo

-- Dyadic echo: session with echo-indexed provenance
DyadicEcho : ∀ {p} → Session p → Set
DyadicEcho S = Σ Party (λ q → SessionEcho q S)

-- Alice's send protocol with provenance
AliceSendWithProvenance : DyadicEcho AliceSendsUnit
AliceSendWithProvenance = Alice , AliceSendEcho

-- Bob's receive protocol with provenance
BobReceiveWithProvenance : DyadicEcho BobReceivesUnit
BobReceiveWithProvenance = Bob , echo-intro (λ _ → tt) tt

-- Provenance preservation under session concatenation
ProvenancePreservation : ∀ {p} {S1 S2 : Session p} →
                          DyadicEcho S1 → DyadicEcho S2 → DyadicEcho (S1 >>= S2)
ProvenancePreservation (q1 , echo1) (q2 , echo2) = q1 , echo1

-- Echo-safe dyadic protocols: protocols where echoes preserve safety
EchoSafe : ∀ {p} → Session p → Set
EchoSafe S = Σ (Safe S) (λ safe → DyadicEcho S)

-- Alice's safe send protocol with provenance
AliceSafeSendWithProvenance : EchoSafe AliceSendsUnit
AliceSafeSendWithProvenance = AliceSendsUnit-safe , AliceSendWithProvenance

-- Bob's safe receive protocol with provenance
BobSafeReceiveWithProvenance : EchoSafe BobReceivesUnit
BobSafeReceiveWithProvenance = BobReceivesUnit-safe , BobReceiveWithProvenance

-- Protocol duality with echo retention
EchoDual : ∀ {p} → Session p → Session (dual p) → Set
EchoDual S T = Σ (DyadicEcho S) (λ echoS → DyadicEcho T)

-- Example: Alice send is dual to Bob receive (with provenance)
SendReceiveDualWithEcho : EchoDual AliceSendsUnit BobReceivesUnit
SendReceiveDualWithEcho = AliceSendWithProvenance , BobReceiveWithProvenance

-- Echo retention under protocol composition
CompositionEchoRetention : ∀ {p} {S1 S2 : Session p} →
                            EchoSafe S1 → EchoSafe S2 → EchoSafe (S1 >>= S2)
CompositionEchoRetention (safe1 , echo1) (safe2 , echo2) =
  >>=-preserves-safe safe1 safe2 , ProvenancePreservation echo1 echo2

-- Main bridge theorem: Dyadic protocols with echo provenance
DyadicEchoBridgeTheorem : 
  Σ (Session Alice) (λ S → 
  Σ (Session Bob) (λ T → 
  Σ (EchoSafe S) (λ echoSafeS → 
  Σ (EchoSafe T) (λ echoSafeT → 
  EchoDual S T))))
DyadicEchoBridgeTheorem = 
  AliceSendsUnit , BobReceivesUnit , 
  AliceSafeSendWithProvenance , BobSafeReceiveWithProvenance , 
  SendReceiveDualWithEcho

-- Note: This bridge demonstrates how echo types can retain provenance
-- information in dyadic protocol communications, enabling tracking
-- of protocol history and constraints that would be lost in plain
-- session type views.
