{-# OPTIONS --safe --without-K #-}

module All where

open import Echo.Core
open import Echo.Bridges.AntiEcho
open import EchoKernel
open import Echo.Characteristic
open import Echo.Residue
open import Echo.Examples.EchoExampleAbsInt
open import Echo.Examples.EchoExampleParser
open import Echo.Examples.EchoExampleProvenance
open import Echo.Examples.EchoExamples

open import Echo.Bridges.EchoChoreo
open import Echo.Bridges.EchoEpistemic
open import EchoLinear
open import Echo.Bridges.EchoGraded
open import Echo.Bridges.EchoTropical
open import Echo.Bridges.AntiEchoTropical
open import Echo.Bridges.AntiEchoTropicalGeneric
open import Echo.Bridges.EchoIntegration
open import Echo.Bridges.EchoCNOBridge

open import Echo.Bridges.EchoApprox
open import Echo.Bridges.EchoApproxInstance
open import Echo.Bridges.EchoCost
open import Echo.Bridges.EchoCostInstance
open import Echo.Bridges.EchoIndexed
open import Echo.Bridges.EchoDecidable
open import Echo.Bridges.EchoSearch
open import Echo.Bridges.EchoSearchInstance
open import Echo.Bridges.EchoAccess
open import Echo.Bridges.EchoFiberCount
open import Echo.Bridges.EchoEpistemicResidue
open import Echo.Bridges.EchoRelational
open import Echo.Bridges.EchoCategorical
open import Echo.Bridges.EchoScope
open import Echo.Bridges.EchoOrdinal
open import Echo.Bridges.EchoJanusBridge
open import Echo.Bridges.Dyadic
open import Echo.Bridges.DyadicEchoBridge
open import Echo.Bridges.EchoThermodynamics
open import Echo.Bridges.EchoThermodynamicsFinite
open import Echo.Bridges.EchoThermodynamicsArbitrary
open import Echo.Bridges.EchoThermoCollapseImpossible
open import Echo.Bridges.EchoStabilityTests
open import VecRotation

-- Establishment-plan pillars (docs/echo-types/establishment-plan.adoc).
-- A is a real bridge; B–D are doc-only scaffolds (no declarations,
-- typecheck under --safe --without-K, tracked here per policy).
open import Echo.Bridges.EchoFiberBridge     -- Pillar A (landed)
open import Echo.Bridges.EchoPullback        -- Pillar B (scaffold)
open import Echo.Bridges.EchoGradedComonad   -- Pillar B (scaffold)
open import Echo.Bridges.EchoSeparating      -- Pillar C (scaffold)
open import Echo.Bridges.EchoRelModel        -- Pillar D (scaffold)

-- Pillar F earn-back (docs/echo-types/earn-back-plan.adoc). Wired in
-- on the gate passing (Sequencing pt 4); see docs/retractions.adoc
-- follow-up F-2026-05-18a.
open import Echo.Bridges.EchoPullbackUnivF4  -- Gate F4 PASSED (funext-qualified UP)
open import Echo.Bridges.EchoStepNDModelF2   -- Gate F2 PASSED (StepND second model)
open import Echo.Bridges.EchoGradedComonadF1 -- Gate F1 PASSED (graded comonad on iterated-residue)
open import Echo.Bridges.EchoGradedComonadInterface -- Gate F3 abstract record
open import Echo.Bridges.EchoGradedComonadInstance1 -- Gate F3 instance 1 (F1 at (ℕ, +, 0))
open import Echo.Bridges.EchoGradedComonadInstance2 -- Gate F3 PASSED — instance 2 at (List Tag, ++, [])

-- Foundation P1: external-fibre triangulation. Echo agrees with the
-- standard library's OWN independently-authored notions
-- (Function.Definitions / Function.Bundles), removing the
-- same-module self-reference flagged by R-2026-05-18 finding 5.
open import Echo.Bridges.EchoFiberTriangulation

open import Ordinal.Base
open import Ordinal.Closure
open import Ordinal.CNF
open import Ordinal.PsiSimple
open import Ordinal.OmegaMarkers
open import Ordinal.Brouwer
open import Ordinal.Brouwer.Arithmetic
open import Ordinal.Brouwer.Phase13
open import Ordinal.Brouwer.OmegaPow
open import Ordinal.Buchholz.Syntax
open import Ordinal.Buchholz.Closure
open import Ordinal.Buchholz.Order
open import Ordinal.Buchholz.OrderExtended
open import Ordinal.Buchholz.OrderExtendedBudget
open import Ordinal.Buchholz.Psi
open import Ordinal.Buchholz.Examples
open import Ordinal.Buchholz.WellFormed
open import Ordinal.Buchholz.WellFormedCNF
open import Ordinal.Buchholz.WellFormedAdmissible
open import Ordinal.Buchholz.WellFounded
open import Ordinal.Buchholz.OrderRestricted
open import Ordinal.Buchholz.VeblenInterface
open import Ordinal.Buchholz.VeblenIdentityModel
open import Ordinal.Buchholz.VeblenMeasureTarget
open import Ordinal.Buchholz.VeblenProjectionMeasure
open import Ordinal.Buchholz.VeblenComparisonTarget
open import Ordinal.Buchholz.VeblenComparisonModel
open import Ordinal.Buchholz.ExtendedOrder
open import Ordinal.Buchholz.OrderExtendedDirect
open import Ordinal.Buchholz.LiftedExtendedOrder
open import Ordinal.Buchholz.IteratedExtendedOrder
open import Ordinal.Buchholz.RankBrouwer
open import Ordinal.Buchholz.RankPartial
open import Ordinal.Buchholz.RankPow
open import Ordinal.Buchholz.RankMonoUmbrella
open import Ordinal.Buchholz.RecursiveSurfaceOrder
open import Ordinal.Buchholz.RecursiveSurfaceBudget
open import Ordinal.Buchholz.SurfaceOrder
open import Ordinal.Buchholz.VeblenObligations
open import Ordinal.Buchholz.Smoke

open import Smoke
