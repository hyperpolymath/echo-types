{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Per-walkthrough Smoke gate for Lane 5 Walkthrough 3.
--
-- Pins the load-bearing names of `ProvenanceDebugging.agda` so a silent
-- rename or deletion fails CI fast, mirroring the discipline of the
-- top-level `proofs/agda/Smoke.agda` and the Walkthrough 1/2 Smokes.
--
-- Build:
--   agda --library-file=/tmp/agda-libs -i . -i proofs/agda \
--        tutorial/provenance_debugging/Smoke.agda
--
-- Exits 0 under --safe --without-K, zero postulates.
------------------------------------------------------------------------

module tutorial.provenance_debugging.Smoke where

open import tutorial.provenance_debugging.ProvenanceDebugging using
  ( State
  ; pp
  ; pn
  ; np
  ; nn
  ; firstSign
  ; secondSign
  ; echo-pp
  ; echo-pn
  ; pp≢pn
  ; states-distinct-at-true
  ; ClassCert
  ; class-kappa
  ; class-sound
  ; state-to-class
  ; class-pp
  ; class-pn
  ; classes-remain-distinct
  ; recover-from-class
  ; recover-section-at-layer-1
  ; recover-section-package
  ; TrivialCert'
  ; triv-kappa
  ; triv-sound
  ; state-to-trivial
  ; triv-pp
  ; triv-pn
  ; trivials-collapse
  ; no-recovery-from-trivial
  ; provenance-walk-contrast
  ; NotProved-runtimeDebugger
  ; NotProved-stateReconstructionInGeneral
  ; NotProved-completenessAcrossClasses
  ; NotProved-recoveryUnderSideInformation
  )
