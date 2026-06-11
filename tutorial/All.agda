{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

------------------------------------------------------------------------
-- Tutorial-track aggregator. Mirrors `proofs/agda/All.agda` for the
-- Lane 5 walkthrough track.
--
-- Walkthroughs 1 (`tutorial.region_exit_audit`), 2
-- (`tutorial.epistemic_erasure`), and 3
-- (`tutorial.provenance_debugging`) are all realised in Agda as of
-- 2026-05-27. The originally-scaffolded triplet from
-- `tutorial/README.adoc` is complete.
--
-- Build:
--   agda --library-file=/tmp/agda-libs -i . -i proofs/agda \
--        tutorial/All.agda
------------------------------------------------------------------------

module tutorial.All where

import tutorial.region_exit_audit.All
import tutorial.epistemic_erasure.All
import tutorial.provenance_debugging.All
