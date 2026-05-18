{-# OPTIONS --safe --without-K #-}

module All where

open import Echo
open import EchoCharacteristic
open import EchoResidue
open import EchoExamples

open import EchoChoreo
open import EchoEpistemic
open import EchoLinear
open import EchoGraded
open import EchoTropical
open import EchoIntegration
open import EchoCNOBridge

open import EchoApprox
open import EchoIndexed
open import EchoDecidable
open import EchoFiberCount
open import EchoEpistemicResidue
open import EchoRelational
open import EchoCategorical
open import EchoScope
open import EchoOrdinal
open import EchoJanusBridge
open import Dyadic
open import DyadicEchoBridge
open import EchoThermodynamics
open import EchoThermodynamicsFinite
open import EchoThermodynamicsArbitrary
open import EchoThermoCollapseImpossible
open import EchoStabilityTests
open import VecRotation

-- Establishment-plan pillars (docs/echo-types/establishment-plan.adoc).
-- A is a real bridge; B–D are doc-only scaffolds (no declarations,
-- typecheck under --safe --without-K, tracked here per policy).
open import EchoFiberBridge     -- Pillar A (landed)
open import EchoPullback        -- Pillar B (scaffold)
open import EchoGradedComonad   -- Pillar B (scaffold)
open import EchoSeparating      -- Pillar C (scaffold)
open import EchoRelModel        -- Pillar D (scaffold)

-- Pillar F earn-back (docs/echo-types/earn-back-plan.adoc). Wired in
-- on the gate passing (Sequencing pt 4); see docs/retractions.adoc
-- follow-up F-2026-05-18a.
open import EchoPullbackUnivF4  -- Gate F4 PASSED (funext-qualified UP)
open import EchoStepNDModelF2   -- Gate F2 PASSED (StepND second model)

-- Foundation P1: external-fibre triangulation. Echo agrees with the
-- standard library's OWN independently-authored notions
-- (Function.Definitions / Function.Bundles), removing the
-- same-module self-reference flagged by R-2026-05-18 finding 5.
open import EchoFiberTriangulation

open import Ordinal.Base
open import Ordinal.Closure
open import Ordinal.CNF
open import Ordinal.PsiSimple
open import Ordinal.OmegaMarkers
open import Ordinal.Brouwer
open import Ordinal.Brouwer.Arithmetic
open import Ordinal.Brouwer.Phase13
open import Ordinal.Buchholz.Syntax
open import Ordinal.Buchholz.Closure
open import Ordinal.Buchholz.Order
open import Ordinal.Buchholz.OrderExtended
open import Ordinal.Buchholz.Psi
open import Ordinal.Buchholz.Examples
open import Ordinal.Buchholz.WellFormed
open import Ordinal.Buchholz.WellFounded
open import Ordinal.Buchholz.VeblenInterface
open import Ordinal.Buchholz.VeblenIdentityModel
open import Ordinal.Buchholz.VeblenMeasureTarget
open import Ordinal.Buchholz.VeblenProjectionMeasure
open import Ordinal.Buchholz.VeblenComparisonTarget
open import Ordinal.Buchholz.VeblenComparisonModel
open import Ordinal.Buchholz.ExtendedOrder
open import Ordinal.Buchholz.LiftedExtendedOrder
open import Ordinal.Buchholz.IteratedExtendedOrder
open import Ordinal.Buchholz.RankBrouwer
open import Ordinal.Buchholz.RecursiveSurfaceOrder
open import Ordinal.Buchholz.RecursiveSurfaceBudget
open import Ordinal.Buchholz.SurfaceOrder
open import Ordinal.Buchholz.VeblenObligations
open import Ordinal.Buchholz.Smoke

open import Smoke
