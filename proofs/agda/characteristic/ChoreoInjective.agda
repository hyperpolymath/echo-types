{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- TERMINATION NOTICE (added at integration commit):
--
-- EI-2 has been *expressly terminated* with a negative verdict via
-- PATH B (see RecipeNonTriviality.agda header and docs/EI2_REPORT.adoc
-- for the full record). The integration recipe with the existing five
-- named axes does NOT carry substantive simultaneous cross-axis
-- content. This file's "EI-2 IS NOT TERMINATED" comments below are
-- preserved as the historical record of the investigation while it
-- was still open; the authoritative current verdict is at the top of
-- docs/EI2_REPORT.adoc.
--
-- Distinctness against neighbour frameworks rests on the truncation
-- argument (`echo-not-prop` family in proofs/agda/examples/) and the
-- 2-cell argument (Sophisticated submodules of EchoVsQuotient.agda
-- and EchoVsGalois.agda), not on the integration argument. The
-- integration recipe remains useful as organising vocabulary; it is
-- not the locus of distinctness.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- characteristic.ChoreoInjective — formal exhibit for the
-- non-loss-only criterion in EI-2.
--
-- The EI-2 progress report identified that the integration recipe's
-- non-trivial commutation content correlates with whether at least
-- one axis has a non-trivial information-preserving transport on at
-- least one of its strict (non-reflexive) steps. This file
-- formalises the certificate for Choreo's non-loss-only-ness:
--
--   `client-to-server` is injective on the first projection.
--
-- Specifically: distinct preimages give distinct images. This is
-- the cardinality-preservation property the criterion requires.
--
-- Why first-projection-injective and not full Σ-injective?
--
--   Under `--safe --without-K`, full Σ-injectivity for fibers
--   requires K-style reasoning on the second component (the
--   equality proof). First-projection-injectivity is the
--   constructively-defensible weakening that captures the
--   load-bearing claim ("distinct preimages give distinct images")
--   without invoking K.
--
--   For the EI-2 criterion, this is sufficient: the criterion is
--   about cardinality preservation, which lives at the
--   first-projection level.
--
-- Counterexample side: Mode's `weaken` and Grade's
-- `collapse-to-residue` are NOT first-projection-injective on
-- their respective domains. (Not formalised here; the failure is
-- evident from their definitions: weaken collapses
-- `Echo collapse tt` to `EchoR ⊤ TrivialCert tt`, identifying all
-- inhabitants of the source.)
--
-- ============================================================
-- EI-2 STATUS: still not terminated.
-- ============================================================
--
-- This file closes obligation 1 from EI2_REPORT.adoc (formalise
-- client-to-server-injective). The criterion is now formally
-- backed for Choreo. The remaining open obligations are:
--   2. Decide between READING 1 (gate-1 weakens) and READING 2
--      (recipe refines).
--   3. Build a fourth data point (requires a new non-loss-only
--      axis, not currently available).
--   4. Examine the n=3 case.
--   5. Write the recipe-non-triviality theorem.
------------------------------------------------------------------------

module characteristic.ChoreoInjective where

open import Data.Bool.Base                        using (Bool)
open import Data.Product.Base                     using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)

open import Echo                                  using (Echo)
open import EchoChoreo                            using
  ( Role
  ; Client
  ; Server
  ; Global
  ; obs
  ; RoleEcho
  ; client-to-server
  ; swap
  ; swap-square
  )

------------------------------------------------------------------------
-- Helper: swap is involutive.
--
-- This is the structural property that makes swap injective. It is
-- not in EchoChoreo as a named lemma, but is straightforward.
------------------------------------------------------------------------

swap-involutive : ∀ g → swap (swap g) ≡ g
swap-involutive (b1 , b2) = refl

------------------------------------------------------------------------
-- swap-injective: distinct globals give distinct swapped globals.
--
-- Standard derivation from involutivity: if swap g ≡ swap g', then
-- applying swap to both sides and using involutivity twice yields
-- g ≡ g'.
------------------------------------------------------------------------

swap-injective : ∀ {g g' : Global} → swap g ≡ swap g' → g ≡ g'
swap-injective {g} {g'} p =
  trans (sym (swap-involutive g))
        (trans (cong swap p)
               (swap-involutive g'))

------------------------------------------------------------------------
-- The headline result: client-to-server is injective on the first
-- projection.
--
-- If two echoes give equal images under client-to-server, their
-- underlying globals (the first projections of the input echoes)
-- are equal.
--
-- Proof sketch:
--   client-to-server (x, p) = (swap x, trans (swap-square x) p)
--   So proj₁ (client-to-server (x, p)) = swap x
--   If client-to-server (x₁, p₁) ≡ client-to-server (x₂, p₂),
--   then swap x₁ ≡ swap x₂ (by cong proj₁).
--   By swap-injective, x₁ ≡ x₂.
------------------------------------------------------------------------

client-to-server-injective-on-proj₁ :
  ∀ {y : Bool} (e₁ e₂ : RoleEcho Client y) →
  client-to-server e₁ ≡ client-to-server e₂ →
  proj₁ e₁ ≡ proj₁ e₂
client-to-server-injective-on-proj₁ (x₁ , p₁) (x₂ , p₂) eq =
  swap-injective (cong proj₁ eq)

------------------------------------------------------------------------
-- Corollary: client-to-server preserves multiplicity.
--
-- If two distinct globals (g₁ ≢ g₂ at the proj₁ level) are
-- represented by echoes e₁ and e₂, their client-to-server images
-- are also distinct.
--
-- This is the formal statement that client-to-server preserves the
-- "two distinguishable witnesses → two distinguishable images"
-- property.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

client-to-server-preserves-distinction :
  ∀ {y : Bool} (e₁ e₂ : RoleEcho Client y) →
  (proj₁ e₁ ≡ proj₁ e₂ → ⊥) →
  (client-to-server e₁ ≡ client-to-server e₂ → ⊥)
client-to-server-preserves-distinction e₁ e₂ distinct eq =
  distinct (client-to-server-injective-on-proj₁ e₁ e₂ eq)

------------------------------------------------------------------------
-- Corollary for the EI-2 non-loss-only criterion.
--
-- The criterion: an axis is non-loss-only iff at least one of its
-- strict transports preserves multiplicity (witnesses to the
-- multi-element-ness of the Echo type are not collapsed).
--
-- For Choreo:
--   * The strict step c⊑s in the role-reachability order has
--     transport `client-to-server`.
--   * `client-to-server-preserves-distinction` (above) is the
--     formal certificate that this transport preserves
--     multiplicity.
--
-- Therefore: Choreo satisfies the non-loss-only criterion. This
-- is the first formally-certified instance of the criterion.
--
-- For Mode and Grade, the analogous property would be
-- `weaken-injective-on-proj₁` and `collapse-to-residue-injective-
-- on-proj₁`. Both are FALSE: weaken and collapse-to-residue
-- identify multiple distinct globals at the residue level. (Not
-- formalised here as positive evidence; the failure is structural,
-- visible from the definitions.)
--
-- The pattern observed in EI2_REPORT.adoc is therefore consistent
-- with the formal criterion: only Choreo certificate-passes among
-- the existing axes.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Note on the boundary of this file's contribution.
--
-- This file FORMALISES the criterion for one axis (Choreo). It does
-- NOT:
--   * Formalise the criterion-failing cases (Mode, Grade) as
--     negative evidence. The failure is structural (the relevant
--     transports collapse witnesses to the residue/⊤ types, which
--     have fewer distinguishable inhabitants).
--   * Prove the recipe-non-triviality theorem (obligation 5 in
--     EI2_REPORT). That requires generalising over arbitrary axis
--     pairs and showing the bidirectional implication
--     (non-loss-only ↔ non-trivial commutation cells).
--   * Resolve the READING 1 vs READING 2 question (obligation 2).
--     That is a documentation decision, not a formal one.
--
-- Status: EI-2 obligation 1 closed. EI-2 not terminated.
------------------------------------------------------------------------
