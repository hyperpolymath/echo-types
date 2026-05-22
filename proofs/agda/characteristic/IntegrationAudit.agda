{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Gate 2 audit: IntegrationAudit
--
-- Sharpened-falsifier exhibit for nominee N3 —
-- `knowledge-and-controlled-degradation` from `EchoIntegration`,
-- listed in `roadmap-gates.adoc` as one of three candidate
-- "characteristic" theorems.
--
-- Claim: the named integration theorem is `_ × _` of two facts that
-- share no data:
--
--   * Conjunct 1: `∀ e → P (proj₁ (client-stability e))` is a property
--     of `Echo (obs Client)` over `Global = Bool × Bool`. It is the
--     existing `knowledge-along-client-stability` from EchoEpistemic.
--
--   * Conjunct 2: `degrade keep≤residue echo-true ≡ degrade keep≤residue
--     echo-false` is a property of `Echo collapse` over `Bool`, with
--     `collapse : Bool → ⊤`. It is the existing `merged-at-residue`,
--     proved by `refl`.
--
-- The two conjuncts are over *different functions*: `obs Client` (which
-- has type `Global → Bool`) and `collapse` (which has type `Bool → ⊤`).
-- They share no Echo, no domain type, no codomain type, no hypothesis
-- (the `inv` and `k` arguments are consumed only by conjunct 1).
--
-- The original proof is the literal pair, by definition. Therefore the
-- "integration" is `_×_` with no logical link between sides. The
-- single-framework restatement (split into two independent statements)
-- loses nothing — formalised below as `N3-is-product`.
--
-- Audit consequence: N3 fails the sharpened falsifier from
-- `docs/gate-2-characteristic.adoc` §6. The threshold is then carried
-- by N1' (`degrade-via-join`, replacement) and N2 (`degrade-compose`).
------------------------------------------------------------------------

module characteristic.IntegrationAudit where

open import Data.Bool.Base                        using (Bool)
open import Data.Product.Base                     using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EchoChoreo                            using
  ( Global
  ; Client
  ; RoleEcho
  ; client-stability
  ; scramble-server
  )
open import EchoEpistemic                         using (Knows)
open import EchoGraded                            using (degrade; keep≤residue)
open import EchoCharacteristic                    using (echo-true; echo-false)
open import EchoIntegration                       using
  ( knowledge-and-controlled-degradation
  ; knowledge-preserved-under-choreo
  ; merged-at-residue
  )

------------------------------------------------------------------------
-- Conjunct 1 in isolation: pure choreographic transport-of-knowledge,
-- no graded ingredient. Inputs and conclusion are entirely about
-- `RoleEcho Client` over `Global`. The graded layer does not appear.
------------------------------------------------------------------------

split-knowledge :
  ∀ {y : Bool} {P : Global → Set} →
  (∀ g → P g → P (scramble-server g)) →
  Knows Client P y →
  ∀ e → P (proj₁ (client-stability e))
split-knowledge = knowledge-preserved-under-choreo

------------------------------------------------------------------------
-- Conjunct 2 in isolation: pure graded-merging on `Echo collapse tt`,
-- no choreographic ingredient. Inputs are zero (nullary statement).
-- The choreographic layer does not appear.
------------------------------------------------------------------------

split-merging :
  degrade keep≤residue echo-true ≡ degrade keep≤residue echo-false
split-merging = merged-at-residue

------------------------------------------------------------------------
-- The integration witness: the original N3 theorem is the literal
-- pair of the two isolated conjuncts. Both components and proofs are
-- definitionally identical to the originals from EchoIntegration, so
-- the equation closes by `refl`.
--
-- This is the formal content of the sharpened falsifier: the
-- "integration" `knowledge-and-controlled-degradation` *is* the
-- `_×_` of two single-framework facts. No shared data, no shared
-- proof obligation, no compositional content.
------------------------------------------------------------------------

N3-is-product :
  ∀ {y : Bool} {P : Global → Set}
  (inv : ∀ g → P g → P (scramble-server g))
  (k : Knows Client P y) →
  knowledge-and-controlled-degradation inv k
  ≡ (split-knowledge inv k , split-merging)
N3-is-product inv k = refl

------------------------------------------------------------------------
-- A second observation: conjunct 2 does not depend on the hypotheses
-- `inv` and `k`. We can therefore prove it without ever consuming
-- them — confirming the claim that no shared data flows between the
-- two conjuncts.
------------------------------------------------------------------------

split-merging-uses-no-hypotheses :
  ∀ {y : Bool} {P : Global → Set}
  (inv : ∀ g → P g → P (scramble-server g))
  (k : Knows Client P y) →
  degrade keep≤residue echo-true ≡ degrade keep≤residue echo-false
split-merging-uses-no-hypotheses _ _ = split-merging

------------------------------------------------------------------------
-- Gate-2 consequence (prose; the formal content is above).
--
-- Per `docs/gate-2-characteristic.adoc` §6, the sharpened falsifier
-- for N3 is: "exhibit a single-framework restatement and check what
-- is lost." The two `split-*` functions above are the single-framework
-- restatements; the original theorem is their literal product
-- (`N3-is-product`); conjunct 2 ignores the hypotheses
-- (`split-merging-uses-no-hypotheses`). Nothing is lost.
--
-- N3 therefore fails the sharpened test. The lemma stays in
-- EchoIntegration.agda for whatever expository value it has, but it
-- does not earn a slot in the characteristic theorem family.
--
-- A genuine integration theorem — one in which a single Echo carries
-- both a role/choreographic decoration and a graded decoration, and
-- the conjunction's two facts share data — is now constructed in
-- `proofs/agda/characteristic/RoleGraded.agda` (theorem
-- `choreo-grade-commute`). The withdrawn nominee remains in
-- `EchoIntegration` for whatever expository value it carries.
------------------------------------------------------------------------
