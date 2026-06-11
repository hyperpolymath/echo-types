{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

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
import examples.Transport
import examples.EchoVsSigma
