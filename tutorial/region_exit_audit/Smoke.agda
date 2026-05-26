{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Per-walkthrough Smoke gate for Lane 5 Walkthrough 1.
--
-- Pins the load-bearing names of `RegionExitAudit.agda` so a silent
-- rename or deletion fails CI fast, mirroring the discipline of the
-- top-level `proofs/agda/Smoke.agda`.
--
-- Build:
--   agda --library-file=/tmp/agda-libs -i . -i proofs/agda \
--        tutorial/region_exit_audit/Smoke.agda
--
-- Exits 0 under --safe --without-K, zero postulates.
------------------------------------------------------------------------

module tutorial.region_exit_audit.Smoke where

open import tutorial.region_exit_audit.RegionExitAudit using
  ( RegionId
  ; r0
  ; r1
  ; LiveHandle
  ; AuditReceipt
  ; exit
  ; handle-true
  ; handle-false
  ; handles-genuinely-distinct
  ; exit-collapses-handles
  ; audit-no-recovery
  ; audit-no-recovery-r0
  ; audit-no-recovery-r1
  )
