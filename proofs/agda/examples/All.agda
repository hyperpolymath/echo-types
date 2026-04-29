{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Aggregator for the Gate #3 canonical examples.  Compile with:
--
--   agda -i proofs/agda proofs/agda/examples/All.agda
--
-- This does not duplicate any aggregation done by an existing
-- proofs/agda/All.agda; it is scoped to the examples lane only.
------------------------------------------------------------------------

module examples.All where

import examples.TropicalArgmin
import examples.EpistemicUpdate
import examples.LinearErasure
