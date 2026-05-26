{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Per-walkthrough Smoke gate for Lane 5 Walkthrough 2.
--
-- Pins the load-bearing names of `EpistemicErasure.agda` so a silent
-- rename or deletion fails CI fast, mirroring the discipline of the
-- top-level `proofs/agda/Smoke.agda` and Walkthrough 1's Smoke.
--
-- Build:
--   agda --library-file=/tmp/agda-libs -i . -i proofs/agda \
--        tutorial/epistemic_erasure/Smoke.agda
--
-- Exits 0 under --safe --without-K, zero postulates.
------------------------------------------------------------------------

module tutorial.epistemic_erasure.Smoke where

open import tutorial.epistemic_erasure.EpistemicErasure using
  ( Seed
  ; s00
  ; s01
  ; s10
  ; s11
  ; Key
  ; k0
  ; k1
  ; kdf
  ; seed-s00
  ; seed-s10
  ; s00≢s10
  ; seeds-distinct-at-k0
  ; key→bool
  ; seed→bool
  ; kdf-commutes
  ; kdf-to-residue
  ; no-recovery-from-residue
  ; NotProved-byteZeroing
  ; NotProved-cryptographicOneWayness
  ; NotProved-collisionResistance
  ; NotProved-seedDistribution
  )
