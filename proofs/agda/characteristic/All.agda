{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

------------------------------------------------------------------------
-- Aggregator for the Gate #2 characteristic-lane modules.  Compile with:
--
--   agda -i proofs/agda proofs/agda/characteristic/All.agda
--
-- Forces every characteristic-lane module through the typechecker so CI
-- can catch breakage. Mirrors `proofs/agda/examples/All.agda` for the
-- gate-3 lane. The top-level `proofs/agda/All.agda` does not import
-- these modules; this file is the CI seam for the lane.
--
-- New characteristic modules should register here.
--
-- PROMOTION 2026-05-27: `characteristic.N5Falsifier` is now imported
-- here. The 2026-05-18 broken status (unsolved metas around
-- `EchoChoreo.obs` reindex) was resolved 2026-05-27 by making the
-- `applyRole` / `applyGrade` Role + Grade parameters explicit at the
-- four call sites — the unsolved metas were not a content blocker
-- but an inference blocker (Agda cannot recover the role from
-- `RoleGEcho r keep = Echo (obs r) true` because `obs` is not
-- injective). See N5Falsifier.agda's preamble banner for the
-- pre-promotion record and `docs/characteristic.adoc` Revision 5
-- §"Evidence reviewed" item 3 for the audit note.
------------------------------------------------------------------------

module characteristic.All where

import characteristic.ChoreoInjective
import characteristic.IntegrationAudit
import characteristic.InteractionTest
import characteristic.ModeGraded
import characteristic.N5Falsifier
import characteristic.NonTruncatable
import characteristic.RecipeNonTriviality
import characteristic.RecipeSpec
import characteristic.RecipeTheorem
import characteristic.RoleGraded
import characteristic.RoleMode
import characteristic.RoleModeGrade
import characteristic.RoleRole
import characteristic.VisibleConstraintAudit
