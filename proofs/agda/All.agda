{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module All where

open import Echo
open import EchoDisplayed
open import EchoTotalCompletion
open import EchoOrthogonalFactorizationSystem
open import EchoImageFactorization
open import EchoImageFactorizationProp
open import EchoNoSectionGeneric
open import EchoAggregation
open import EchoLossTaxonomy
open import EchoResidueTaxonomy
open import EchoDecorationStructure
open import EchoObservationalEquivalence
open import AntiEcho
open import EchoKernel
open import EchoCharacteristic
open import EchoResidue
open import EchoExampleAbsInt
open import EchoExampleParser
open import EchoExampleProvenance
open import EchoExamples

open import EchoChoreo
open import EchoEpistemic
open import EchoLinear
open import EchoAbstractionBarrier
open import EchoLLEncoding
open import EchoGraded
open import EchoTropical
open import AntiEchoTropical
open import AntiEchoTropicalGeneric
open import EchoIntegration
open import EchoCNOBridge
open import EchoReversibilityBridge
open import EchoResidueCell

open import EchoApprox
open import EchoApproxInstance
open import EchoCost
open import EchoCostInstance
open import EchoIndexed
open import EchoDecidable
open import EchoSearch
open import EchoSearchInstance
open import EchoAccess
open import EchoFiberCount
open import EchoEpistemicResidue
open import EchoRelational
open import EchoCategorical
open import EchoScope
open import EchoOrdinal
open import EchoJanusBridge
open import EchoEphapaxBridge
open import Dyadic
open import DyadicEchoBridge
open import EchoThermodynamics
open import EchoEntropy
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
open import EchoOFSUnivF5       -- Gate F5-1 PARTIAL (funext-qualified factorisation triangle)
open import EchoOFSUnivF5Diag   -- Gate F5-2 (funext-qualified diagonal lifting)
open import EchoOFSUnivF5Iso    -- Gate F5-3 (funext-qualified factorisation uniqueness up to iso) — F5 FULL PASS

-- Audience moves (Tier 3, per GPT-recommended order). Audience-facing
-- abstract modules — each generalises one concrete example into the
-- shape the audience speaks in.
open import EchoProvenance       -- Provenance loss (generalises EchoExampleProvenance)
open import EchoSecurity         -- Region-exit audit (generalises RegionExitAudit walkthrough)
open import EchoProbabilisticSupport  -- Support tracking (audience-facing sampling)
open import EchoDifferential     -- Perturbation tracking (audience-facing sensitivity)

-- Deniability (2026-06-13). Formalises residue deniability as a
-- first-class property: the collapse/no-section story (perfect case)
-- and the injective/section-exists story (partial case), with the
-- IsConstantOpener boundary tying deniability to the affine mode.
open import EchoDeniability
open import EchoTransaction      -- Transaction rollback safety (issue #174; Security instance)
open import EchoSelectiveProjection  -- σ–π commutativity (issue #176; relational-algebra carrier)

-- Narrative deliverable: curated index of "why Echo deserves a name".
open import EchoCanonicalIdentitySuite
open import EchoStepNDModelF2   -- Gate F2 PASSED (StepND second model)
open import EchoGradedComonadF1 -- Gate F1 PASSED (graded comonad on iterated-residue)
open import EchoGradedComonadInterface -- Gate F3 abstract record
open import EchoGradedComonadInstance1 -- Gate F3 instance 1 (F1 at (ℕ, +, 0))
open import EchoGradedComonadInstance2 -- Gate F3 PASSED — instance 2 at (List Tag, ++, [])
open import EchoVariance         -- variance verdict: monad (accumulation) + fibre adjunction, NOT comonad

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
open import Ordinal.Brouwer.OmegaPow
open import Ordinal.Brouwer.OrdinalExp
open import Ordinal.Brouwer.VeblenPhi
open import Ordinal.Brouwer.VeblenPhiNormal -- φ₁ a normal function; next-ε β LEAST ε-number above β
open import Ordinal.Brouwer.VeblenBinary    -- binary Veblen φ_α(β) + the diagonal Γ₀
open import Ordinal.Brouwer.VeblenBinaryNormal -- every φ_α a normal function; φ_{α+1} enumerates fixed points of φ_α
open import Ordinal.Brouwer.VeblenBinaryMono -- first-arg monotonicity; Γ₀ ≤′ φ_Γ₀(0) (diagonal pre-fixed point)
open import Ordinal.Brouwer.VeblenBinaryLeast -- nextFix is the LEAST pre-fixed point; reverse-Γ₀ reduced to one closure
open import Ordinal.Brouwer.VeblenBinaryMonoG -- the engine is monotone in its iterated function (deriv/nextFix mono in g)
open import Ordinal.Brouwer.StrictLeftMonoRefuted
open import Ordinal.Brouwer.AdditivePrincipalGenericRefuted
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
open import Ordinal.Buchholz.RankAdm
open import Ordinal.Buchholz.RankLex
open import Ordinal.Buchholz.RankLexSlice3
open import Ordinal.Buchholz.RankLexJointBplus
open import Ordinal.Buchholz.HeadOmega
open import Ordinal.Buchholz.HeadOmegaInversion
open import Ordinal.Buchholz.RankPowDomination
open import Ordinal.Buchholz.RankPowSlice3
open import Ordinal.Buchholz.RankPowSlice3Headline
open import Ordinal.Buchholz.RankPowMonoRefuted
open import Ordinal.Buchholz.RankDoubledLadder
open import Ordinal.Buchholz.RankDoubledLadderMono
open import Ordinal.Buchholz.RankDoubledLadderMonoPlus
open import Ordinal.Buchholz.RankDoubledLadderAddPrincipal
open import Ordinal.Buchholz.RankDoubledLadderMonoPlus2
open import Ordinal.Buchholz.RankDoubledLadderUmbrella
open import Ordinal.Buchholz.BHTarget
open import Ordinal.Buchholz.RankMonoUmbrella
open import Ordinal.Buchholz.RankMonoUmbrellaSlice3
open import Ordinal.Buchholz.RankMonoUmbrellaSlice4
open import Ordinal.Buchholz.RankMonoSameLeft
open import Ordinal.Buchholz.RankMonoUnion
open import Ordinal.Buchholz.RankMonoUnionWF
open import Ordinal.Buchholz.RankMonoUnionWfCNF
open import Ordinal.Buchholz.RecursiveSurfaceOrder
open import Ordinal.Buchholz.RecursiveSurfaceSound
open import Ordinal.Buchholz.OrderExtendedSound
open import Ordinal.Buchholz.RecursiveSurfaceBudget
open import Ordinal.Buchholz.SurfaceOrder
open import Ordinal.Buchholz.VeblenObligations
open import Ordinal.Buchholz.Smoke

-- Foundation contract surface (FOUNDATION_CONTRACT.md): the curated,
-- stable `Echo.*` public interface exported to downstream languages.
-- Index + modality are measure-independent; the measure seam may
-- observe residues but never defines Echo (Echo IS-NOT a resource
-- instance). See docs/echo-types/echo-kernel-note.adoc.
open import Echo.Index.ThinPoset
open import Echo.Modality.Interface
open import Echo.Modality.Core
open import Echo.Separation.NotResourceInstance
open import Echo.Measure.Interface
open import Echo.Measure.Examples

open import Smoke
