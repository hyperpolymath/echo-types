{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Tutorial-track aggregator. Mirrors `proofs/agda/All.agda` for the
-- Lane 5 walkthrough track.
--
-- Only Walkthrough 1 (`tutorial.region_exit_audit`) is currently
-- realised in Agda. Walkthroughs 2 (epistemic erasure) and 3
-- (provenance / debugging) remain at scaffold/design-doc level per
-- `tutorial/README.adoc` — they should be registered here when they
-- land.
--
-- Build:
--   agda --library-file=/tmp/agda-libs -i . -i proofs/agda \
--        tutorial/All.agda
------------------------------------------------------------------------

module tutorial.All where

import tutorial.region_exit_audit.All
