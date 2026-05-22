{-# OPTIONS --safe --without-K #-}

module EchoIntegration where

open import EchoChoreo
open import EchoEpistemic
open import EchoGraded
open import EchoCharacteristic using (echo-true; echo-false; echo-true≢echo-false)
open import EchoResidue using (no-section-collapse-to-residue)

open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

-- Choreographic observation-preserving steps preserve any epistemic predicate
-- that is stable under the hidden-state update.
knowledge-preserved-under-choreo :
  ∀ {y : Bool} {P : Global → Set} →
  (∀ g → P g → P (scramble-server g)) →
  Knows Client P y →
  ∀ e → P (proj₁ (client-stability e))
knowledge-preserved-under-choreo = knowledge-along-client-stability

-- Controlled degradation in graded echoes:
-- distinct keep-grade witnesses become identified at residue grade.
distinct-at-keep : echo-true ≢ echo-false
distinct-at-keep = echo-true≢echo-false

merged-at-residue :
  degrade keep≤residue echo-true ≡ degrade keep≤residue echo-false
merged-at-residue = refl

no-recovery-after-residue-degrade :
  ¬ (Σ (GEcho residue → GEcho keep)
       (λ raise → ∀ e → raise (degrade keep≤residue e) ≡ e))
no-recovery-after-residue-degrade = no-section-collapse-to-residue

-- Integration witness: choreography can preserve knowledge while graded
-- degradation still loses discriminating power in a controlled way.
knowledge-and-controlled-degradation :
  ∀ {y : Bool} {P : Global → Set} →
  (∀ g → P g → P (scramble-server g)) →
  Knows Client P y →
  (∀ e → P (proj₁ (client-stability e)))
  × (degrade keep≤residue echo-true ≡ degrade keep≤residue echo-false)
knowledge-and-controlled-degradation inv k =
  knowledge-preserved-under-choreo inv k , merged-at-residue
