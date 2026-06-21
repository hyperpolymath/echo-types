{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoTransaction: SQL transaction rollback safety as an instance of the
-- generic no-section theorem. Closes echo-types#174 (consumer:
-- affinescript db-theory #2, `stdlib/Transaction.affine`,
-- `docs/academic/proofs/db-theory-2-transaction-safety.md` #DB-2.1).
--
-- !! HONEST BOUND, STATED UP FRONT !!
--
-- `rollback-discards-writes` is a TYPE-LEVEL guarantee that no pure Agda
-- function reconstructs a discarded write-set from the rollback receipt
-- alone (factored through
-- `EchoNoSectionGeneric.no-section-of-collapsing-map`). It is NOT:
--   * `durability`       — a claim about writes surviving a crash;
--   * `isolation`        — a claim about concurrent-transaction visibility;
--   * `commit-semantics` — #DB-2.2 commit-promotes-writes is the DUAL
--                          (commit PRESERVES writes, so it is not a
--                          no-section statement at all);
--   * `savepoint-locality` — #DB-2.3 is a structural/runtime nesting
--                          claim outside this carrier;
--   * `runtime-memory-zeroed` — a claim about physical memory contents.
-- Conflating any of these with `rollback-discards-writes` is the category
-- error the matched-negative block at the bottom heads off. Same
-- honest-bound discipline as `EchoSecurity` / `RegionExitAudit`
-- (R-2026-05-18).
--
-- *Structural content (#DB-2.1).* A transaction's staged-but-uncommitted
-- writes are an affine resource; `rollback` consumes that resource and
-- emits a receipt that records only THAT a rollback occurred, never which
-- writes were discarded. Two distinct write-sets therefore collapse to
-- the same receipt, so `rollback` admits no section: a post-rollback
-- caller holding only the receipt cannot type-check a function returning
-- the discarded write-set. This is precisely "the one consumption that
-- discards is observationally equivalent to never having started".
--
-- This is the first `Security` instance outside the original region-exit
-- audit setting (`EchoSecurity.region-exit-audit-instance`), establishing
-- that any bracketed-mutation resource — transactions, scoped
-- capabilities, scoped logs — reduces to the same generic lemma.
--
-- Headlines (pinned in Smoke.agda):
--
--   * Mutation / WriteSet / RollbackLog  -- the carrier types
--   * rollback                           -- the collapsing audit boundary
--   * rollback-discards-writes           -- #DB-2.1, direct no-section
--   * transaction-security               -- the `Security` instance
--   * rollback-no-recovery               -- #DB-2.1 via the abstract theorem
--
-- Scope guardrail (Echo-vs-Σ clearance). `rollback-discards-writes` uses
-- `no-section-of-collapsing-map` directly, whose three-line trans/sym/cong
-- proof is the canonical non-trivial Echo-typed content; replacing it with
-- a bare `Σ` + `_≡_` would lose the collapse/no-section content. The
-- `NotProved-*` aliases pin the honest scope.

module EchoTransaction where

open import EchoNoSectionGeneric using (no-section-of-collapsing-map)
open import EchoSecurity         using (Security; module SecurityTheorems)

open import Data.Nat.Base   using (ℕ)
open import Data.List.Base  using (List; []; _∷_)
open import Data.Product.Base using (Σ)
open import Data.Unit.Base  using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

----------------------------------------------------------------------
-- The carrier.
--
-- A `Mutation` is an opaque cell-write (address, value); a `WriteSet` is
-- the ordered list a transaction has staged but not committed. The
-- `RollbackLog` receipt is information-free: it records only that a
-- rollback happened.
----------------------------------------------------------------------

data Mutation : Set where
  set-cell : ℕ → ℕ → Mutation

WriteSet : Set
WriteSet = List Mutation

data RollbackLog : Set where
  rolled-back : RollbackLog

-- The audit boundary: rollback collapses every write-set to the single
-- receipt, discarding the staged mutations.
rollback : WriteSet → RollbackLog
rollback _ = rolled-back

----------------------------------------------------------------------
-- The audit witnesses: two distinct write-sets that collapse identically.
----------------------------------------------------------------------

ws₁ ws₂ : WriteSet
ws₁ = []
ws₂ = set-cell 0 1 ∷ []

ws₁≢ws₂ : ws₁ ≢ ws₂
ws₁≢ws₂ ()

rollback-collapses : rollback ws₁ ≡ rollback ws₂
rollback-collapses = refl

----------------------------------------------------------------------
-- #DB-2.1 rollback-discards-writes (headline): no pure function
-- reconstructs a discarded write-set from the rollback receipt alone.
----------------------------------------------------------------------

rollback-discards-writes :
  ¬ Σ (RollbackLog → WriteSet) (λ recover → ∀ ws → recover (rollback ws) ≡ ws)
rollback-discards-writes =
  no-section-of-collapsing-map rollback ws₁ ws₂ ws₁≢ws₂ rollback-collapses

----------------------------------------------------------------------
-- The same guarantee as a `Security` instance, so the transaction
-- carrier joins the EchoSecurity audience family. A single transaction
-- scope is the (trivial) `RegionId`; `audit-no-recovery-at` re-derives
-- #DB-2.1 through the abstract theorem, witnessing that the instance is
-- real (not merely structurally similar).
----------------------------------------------------------------------

transaction-security : Security
transaction-security = record
  { RegionId       = ⊤
  ; Resource       = λ _ → WriteSet
  ; Receipt        = λ _ → RollbackLog
  ; exit           = λ _ → rollback
  ; res₁           = λ _ → ws₁
  ; res₂           = λ _ → ws₂
  ; res-distinct   = λ _ → ws₁≢ws₂
  ; exit-collapses = λ _ → rollback-collapses
  }

rollback-no-recovery :
  (r : ⊤) →
  ¬ Σ (RollbackLog → WriteSet) (λ recover → ∀ ws → recover (rollback ws) ≡ ws)
rollback-no-recovery = SecurityTheorems.audit-no-recovery-at transaction-security

----------------------------------------------------------------------
-- Matched-negative block (HONEST BOUND, per R-2026-05-18 discipline).
--
-- `⊤`-aliased so `grep NotProved` catches them. A consumer citing
-- `rollback-discards-writes` beyond these scopes is making a category
-- error: the guarantee is exactly "no pure Agda function reconstructs
-- the discarded write-set from the receipt alone, inside this model".
----------------------------------------------------------------------

NotProved-durability : Set
NotProved-durability = ⊤

NotProved-isolation : Set
NotProved-isolation = ⊤

NotProved-commit-semantics : Set      -- #DB-2.2 is the dual, not a no-section
NotProved-commit-semantics = ⊤

NotProved-savepoint-locality : Set    -- #DB-2.3 is structural/runtime
NotProved-savepoint-locality = ⊤

NotProved-runtime-memory-zeroed : Set
NotProved-runtime-memory-zeroed = ⊤

----------------------------------------------------------------------
-- Companion remark.
--
-- #DB-2.2 (commit-promotes-writes) is the dual of #DB-2.1: commit
-- PRESERVES the write-set, so it is an equality/section statement, not a
-- no-section one — it belongs in a separate carrier and is deliberately
-- not modelled here. #DB-2.3 (savepoint-locality) is a nesting/structural
-- property of the transaction tree; it too is out of scope for this
-- minimal rollback-safety carrier. The `Mutation` / `RollbackLog` types
-- are placeholders chosen for inhabitability + a clean distinctness
-- witness; the proof goes through for any carrier with two distinct
-- write-sets collapsing to the same receipt.
----------------------------------------------------------------------
