{-# OPTIONS --safe --without-K #-}

-- EchoSecurity: the audience-facing region-exit / capability-flow
-- audit theorem at full generality. Generalises the existing
-- `tutorial/region_exit_audit/RegionExitAudit.agda` (a concrete
-- 2-region `LEcho linear → LEcho affine` walkthrough) from a
-- single Bool-indexed instance into an abstract `Security` record,
-- with the audit guarantee proved parametric in the resource type,
-- the receipt type, the region indexing, and a constructive
-- distinguishability witness.
--
-- !! HONEST BOUND, STATED UP FRONT !!
--
-- This module is a TYPE-LEVEL guarantee that no pure Agda function
-- reconstructs a consumed resource from its audit receipt alone
-- (`audit-no-recovery-at`, factored through
-- `EchoNoSectionGeneric.no-section-of-collapsing-map`).
--
-- It is NOT:
--   * `bytes-zeroed` — a runtime claim about memory contents;
--   * `side-channel-safe` — a claim about timing / speculative
--     leaks;
--   * `tamper-evident` — a claim about cryptographic
--     authentication of the receipt;
--   * `oracle-recovery` — a claim about adversaries with access
--     to additional live resources outside the model.
--
-- Conflating any of these four with `audit-no-recovery-at` is a
-- category error the matched-negative block at the bottom of this
-- module exists to head off. The same honest-bound discipline as
-- `RegionExitAudit.agda` (per R-2026-05-18).
--
-- *Audience.* Capability-flow / region-typed-systems / linear-
-- region-discipline (ephapax-L3-style) practitioners. The
-- structural content is:
--
--   For ANY resource type `Resource`, ANY receipt type `Receipt`,
--   ANY region-indexing `RegionId`, and ANY pair of constructively
--   distinguishable resources `res₁ ≢ res₂` collapsing under
--   `exit` (`exit r (res₁ r) ≡ exit r (res₂ r)`), the audit
--   boundary `exit` admits no section — no pure recovery function.
--
-- That's the structural fact. The linear-mode-tagged `LEcho`
-- walkthrough is one instance; cryptographic-erasure framings,
-- region-discipline systems, capability-revocation models are all
-- instances of the same shape: a collapsing exit boundary with a
-- distinguishability witness.
--
-- *Closes Tier 3 second audience move per the GPT-recommended
-- order.* The existing `RegionExitAudit.agda` walkthrough becomes
-- a worked Bool-region instance; the abstract module sits beside
-- it, with the `region-exit-audit-instance` instantiation pinned.
--
-- *Echo-specific properties used.* This module leans on:
--
--   * `EchoNoSectionGeneric.no-section-of-collapsing-map` —
--     the lifted structural no-section theorem that bridges
--     the abstract `Security` setup to the audit guarantee.
--   * `EchoLinear.weaken` (in the worked instance) — the
--     load-bearing audit-collapse map.
--
-- The headline `audit-no-recovery-at` is a Σ-quantified negation
-- statement that uses `no-section-of-collapsing-map` directly;
-- replacing this with generic `Σ` + `_≡_` would lose the
-- residue/witness/no-section content the proof carries. Falsifier
-- explicitly documented in the companion-remark.
--
-- Headlines (pinned in Smoke.agda):
--
--   * Security                          -- the abstract setup record
--   * module SecurityTheorems            -- parametric in S : Security
--   * exit-collapses-at                  -- per-region collapse witness
--   * audit-no-recovery-at               -- the per-region audit guarantee
--   * TwoRegion                          -- the instance's region type
--   * region-exit-audit-instance         -- the worked Bool-region instance
--
-- Scope guardrail (Echo-vs-Σ clearance + honest-bound).
-- `audit-no-recovery-at` is the no-section lemma instantiated at
-- the abstract security setup. It uses
-- `EchoNoSectionGeneric.no-section-of-collapsing-map` directly,
-- whose three-line `trans/sym/cong` proof is the canonical
-- non-trivial Echo-typed content. The audience-facing rephrasing
-- packages this content under capability-flow names; the matched-
-- negative `NotProved-*` aliases pin the honest scope.

module EchoSecurity where

open import EchoNoSectionGeneric using (no-section-of-collapsing-map)

open import Data.Product.Base using (Σ; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

----------------------------------------------------------------------
-- The abstract security setup.
--
-- A `Security` is the data of a region indexing, a per-region
-- resource type + receipt type, an exit boundary, and a pair of
-- per-region distinguishable resources that collapse under exit
-- (the audit witness).
----------------------------------------------------------------------

record Security : Set₁ where
  field
    RegionId       : Set
    Resource       : RegionId → Set
    Receipt        : RegionId → Set
    exit           : (r : RegionId) → Resource r → Receipt r
    res₁           : (r : RegionId) → Resource r
    res₂           : (r : RegionId) → Resource r
    res-distinct   : (r : RegionId) → res₁ r ≢ res₂ r
    exit-collapses : (r : RegionId) → exit r (res₁ r) ≡ exit r (res₂ r)

----------------------------------------------------------------------
-- The two headline theorems, parametric in the security setup.
--
-- Each module-`_ (S : Security)` field becomes a per-instance
-- function. Consumers instantiate with a concrete `Security` (see
-- `region-exit-audit-instance` below for the worked example).
----------------------------------------------------------------------

module SecurityTheorems (S : Security) where
  open Security S

  ----------------------------------------------------------------------
  -- Headline 1: per-region exit collapses distinct resources.
  --
  -- The audit boundary collapses per-resource distinctions into the
  -- per-region receipt. Without this non-injectivity, exit would be
  -- a renamed identity and the audit would carry no information-loss
  -- content. Re-export of the record's `exit-collapses` field.
  ----------------------------------------------------------------------

  exit-collapses-at :
    (r : RegionId) → exit r (res₁ r) ≡ exit r (res₂ r)
  exit-collapses-at = exit-collapses

  ----------------------------------------------------------------------
  -- Headline 2 (the audit guarantee): no pure function reconstructs
  -- the resource from the receipt alone.
  --
  -- Per-region instantiation of `no-section-of-collapsing-map`.
  -- This is the load-bearing audit claim: a post-exit caller,
  -- holding only the receipt, cannot type-check a function that
  -- returns the consumed resource. Pure Agda has no escape hatches
  -- (`--safe --without-K`), so no postulate-based recovery exists
  -- either.
  ----------------------------------------------------------------------

  audit-no-recovery-at :
    (r : RegionId) →
    ¬ Σ (Receipt r → Resource r)
        (λ recover → ∀ res → recover (exit r res) ≡ res)
  audit-no-recovery-at r =
    no-section-of-collapsing-map
      (exit r)
      (res₁ r) (res₂ r)
      (res-distinct r)
      (exit-collapses r)

----------------------------------------------------------------------
-- Worked concrete instance: the RegionExitAudit walkthrough's
-- 2-region `LEcho linear → LEcho affine` setup, packaged as a
-- `Security` inhabitant.
--
-- `TwoRegion` is the same 2-element region enumeration as the
-- walkthrough's `RegionId`. `Resource` is `LEcho linear`
-- (= `Echo collapse tt`) and `Receipt` is `LEcho affine`
-- (= `EchoR ⊤ TrivialCert tt`), both region-constant. The
-- distinguishability witness is `EchoCharacteristic.echo-true
-- ≢ echo-false`, and the collapse witness is
-- `EchoLinear.weaken-collapses-distinction`.
----------------------------------------------------------------------

open import EchoLinear         using (LEcho; linear; affine; weaken; weaken-collapses-distinction)
open import EchoCharacteristic using (echo-true; echo-false; echo-true≢echo-false)

data TwoRegion : Set where
  r0 r1 : TwoRegion

region-exit-audit-instance : Security
region-exit-audit-instance = record
  { RegionId       = TwoRegion
  ; Resource       = λ _ → LEcho linear
  ; Receipt        = λ _ → LEcho affine
  ; exit           = λ _ → weaken
  ; res₁           = λ _ → echo-true
  ; res₂           = λ _ → echo-false
  ; res-distinct   = λ _ → echo-true≢echo-false
  ; exit-collapses = λ _ → weaken-collapses-distinction
  }

----------------------------------------------------------------------
-- Matched-negative block (HONEST BOUND, per R-2026-05-18 discipline).
--
-- The properties below are deliberately NOT proved by this module.
-- They are `⊤`-aliased so `grep NotProved` in this file catches
-- them; reading the file should make the audit scope explicit.
--
-- A consumer of `EchoSecurity` who cites `audit-no-recovery-at`
-- as a security claim BEYOND these scopes is making a category
-- error. The audit guarantee is exactly: no pure Agda function
-- reconstructs the resource from the receipt alone, inside this
-- model. Real-world security claims (bytes zeroed, side-channel
-- safe, tamper-evident, oracle-secure) require additional
-- structure beyond the type-level no-section property.
----------------------------------------------------------------------

NotProved-bytes-zeroed : Set
NotProved-bytes-zeroed = ⊤

NotProved-side-channel-safe : Set
NotProved-side-channel-safe = ⊤

NotProved-tamper-evident : Set
NotProved-tamper-evident = ⊤

NotProved-oracle-recovery : Set
NotProved-oracle-recovery = ⊤

----------------------------------------------------------------------
-- Companion remark.
--
-- The two headlines of `SecurityTheorems` capture the structural
-- fact of audit-boundary information loss at the audience level:
--
--   1. The exit boundary is non-injective on distinguishable
--      resources (otherwise it would be a renamed identity).
--   2. No pure function recovers the resource from the receipt
--      alone, per-region.
--
-- This is the abstract content of "the audit boundary type-level
-- forbids resource recovery"; cryptographic-erasure protocols,
-- capability-revocation models, region-discipline type systems,
-- and use-after-free prevention layers are all instances of
-- `Security` with a specific `Resource`, `Receipt`, `RegionId`,
-- and constructive distinguishability witness.
--
-- The abstract setup does NOT bake in any cryptographic structure,
-- noise model, or adversary capability — the headline theorems
-- use only the distinguishability + collapse witnesses, mirroring
-- the existing `RegionExitAudit` walkthrough's honest-bound
-- discipline. Future audience-extensions (e.g.
-- `EchoSecurityCrypto.agda` adding ROM-style assumptions, or
-- `EchoSecurityCounterfactual.agda` adding oracle access) can
-- layer additional theorems on top, with `Security` as the
-- minimum-fact baseline.
--
-- The next audience-facing module per the GPT-recommended order
-- is `EchoProbabilisticSupport.agda` (sampling / support-tracking
-- — independent of EchoSecurity).
----------------------------------------------------------------------
