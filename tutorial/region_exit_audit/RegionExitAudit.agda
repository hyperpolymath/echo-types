{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Lane 5 Walkthrough 1: certified region-exit audit
--
-- !! HONEST BOUND, STATED UP FRONT !!
--
-- This walkthrough is NOT a claim that in-memory bytes of the
-- exiting region's data have been zeroed. It is a *type-level*
-- guarantee that no pure Agda function reconstructs the live region
-- handle from the audit receipt alone (`audit-no-recovery`, factored
-- through `EchoLinear.no-section-weaken`).
--
-- Conflating these two is a category error a sceptic will catch.
-- See docs/retractions.adoc R-2026-05-18 for the discipline behind
-- this disclosure; the same narrowing pattern applies.
--
-- The walkthrough models an ephapax-L3-style region as a Mode-indexed
-- `LEcho` where `live = linear` and `exited = affine`. Real ephapax
-- region discipline is enforced in the language's type system; we
-- mirror the type-level audit guarantee here without modelling the
-- full linear language.
------------------------------------------------------------------------

module tutorial.region_exit_audit.RegionExitAudit where

open import EchoLinear
  using ( Mode
        ; linear
        ; affine
        ; LEcho
        ; weaken
        ; no-section-weaken
        ; weaken-collapses-distinction
        )
open import EchoCharacteristic
  using (echo-true; echo-false; echo-true≢echo-false)

open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Region model

-- A region id is just a label distinguishing several regions. Two is
-- enough to make the per-region quantifier non-vacuous; the
-- walkthrough generalises to any inductive `RegionId` set.
data RegionId : Set where
  r0 r1 : RegionId

-- A live region handle at region `r` is content at linear mode.
-- Region tracking lives in the index; the carrier is mode-graded.
LiveHandle : RegionId → Set
LiveHandle _ = LEcho linear

-- An audit receipt at region `r` is the same content at affine mode.
-- Two distinct live handles (within a region) exit to the same
-- receipt — that is the audit boundary.
AuditReceipt : RegionId → Set
AuditReceipt _ = LEcho affine

-- Exit produces the receipt from the live handle. Per-region.
-- Aliased from `EchoLinear.weaken` so the audit-boundary role is
-- explicit at the call site.
exit : ∀ r → LiveHandle r → AuditReceipt r
exit _ = weaken

------------------------------------------------------------------------
-- Two concrete live handles

-- We reuse the `EchoCharacteristic` non-injectivity witnesses as
-- concrete live handles. They are genuinely distinct (the
-- `handles-genuinely-distinct` lemma below).
handle-true : ∀ {r} → LiveHandle r
handle-true = echo-true

handle-false : ∀ {r} → LiveHandle r
handle-false = echo-false

handles-genuinely-distinct :
  handle-true {r0} ≢ handle-false {r0}
handles-genuinely-distinct = echo-true≢echo-false

------------------------------------------------------------------------
-- Headline lemmas

-- Headline 1. Exit collapses two distinct live handles to the same
-- receipt. This is the audit boundary collapsing per-handle
-- distinctions into the per-region receipt — non-injectivity is the
-- whole point. Without it, exit would be a renamed identity and the
-- audit would carry no useful information-loss content.
exit-collapses-handles :
  ∀ r → exit r (handle-true {r}) ≡ exit r (handle-false {r})
exit-collapses-handles _ = weaken-collapses-distinction

-- Headline 2 (the audit guarantee).  NO pure function reconstructs
-- the live region handle from the audit receipt alone, within any
-- region. This is `EchoLinear.no-section-weaken` instantiated
-- per-region, aliased so the audit-boundary role is explicit.
--
-- This is the load-bearing audit claim. Read it as: a post-exit
-- caller, holding only the receipt, cannot type-check a function
-- that returns the live handle. Pure Agda has no escape hatches
-- (`--safe --without-K`), so no postulate-based recovery exists
-- either.
audit-no-recovery :
  ∀ r →
  ¬ (Σ (AuditReceipt r → LiveHandle r)
       (λ recover → ∀ h → recover (exit r h) ≡ h))
audit-no-recovery _ = no-section-weaken

------------------------------------------------------------------------
-- Per-region instances (for explicit-region sceptic reads)

-- The guarantee at region r0, written without the universal
-- quantifier. Useful to cite when discussing a specific region.
audit-no-recovery-r0 :
  ¬ (Σ (AuditReceipt r0 → LiveHandle r0)
       (λ recover → ∀ h → recover (exit r0 h) ≡ h))
audit-no-recovery-r0 = audit-no-recovery r0

audit-no-recovery-r1 :
  ¬ (Σ (AuditReceipt r1 → LiveHandle r1)
       (λ recover → ∀ h → recover (exit r1 h) ≡ h))
audit-no-recovery-r1 = audit-no-recovery r1

------------------------------------------------------------------------
-- What this walkthrough does NOT prove (the matched negative)

-- We deliberately do not state, and do not prove, any of:
--
--   * `bytes-zeroed` (a runtime claim about memory contents);
--   * `secure-against-side-channels` (a claim about timing /
--     speculative-execution leaks);
--   * `audit-is-tamper-evident` (a claim about the receipt being
--     cryptographically authenticated);
--   * `no-recovery-given-an-oracle` (a claim about adversaries with
--     access to *additional* live handles outside the model).
--
-- These are real properties one might want, but they are not what
-- `audit-no-recovery` gives. The honest scope is: a type-level
-- guarantee inside `--safe --without-K` Agda, for a pure function
-- with only the receipt as input. Citations of this walkthrough
-- elsewhere should preserve that scope; conflating it with any of
-- the four bullets above is the category error this walkthrough
-- exists to head off.
