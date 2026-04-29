{-# OPTIONS --safe --without-K #-}

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
------------------------------------------------------------------------

module characteristic.All where

import characteristic.ChoreoInjective
import characteristic.IntegrationAudit
import characteristic.InteractionTest
import characteristic.ModeGraded
import characteristic.RecipeNonTriviality
import characteristic.RecipeSpec
import characteristic.RecipeTheorem
import characteristic.RoleGraded
import characteristic.RoleMode
import characteristic.RoleModeGrade
import characteristic.RoleRole
import characteristic.VisibleConstraintAudit
