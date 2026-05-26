{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Tutorial-track aggregator. Mirrors `proofs/agda/All.agda` for the
-- Lane 5 walkthrough track.
--
-- Walkthroughs 1 (`tutorial.region_exit_audit`) and 2
-- (`tutorial.epistemic_erasure`) are currently realised in Agda.
-- Walkthrough 3 (provenance / debugging) remains at scaffold/
-- design-doc level per `tutorial/README.adoc` — it should be
-- registered here when it lands.
--
-- Build:
--   agda --library-file=/tmp/agda-libs -i . -i proofs/agda \
--        tutorial/All.agda
------------------------------------------------------------------------

module tutorial.All where

import tutorial.region_exit_audit.All
import tutorial.epistemic_erasure.All
