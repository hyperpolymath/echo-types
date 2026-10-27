{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

------------------------------------------------------------------------
-- TERMINATION NOTICE (added at integration commit):
--
-- EI-2 has been *expressly terminated* with a negative verdict via
-- PATH B (see RecipeNonTriviality.agda header and docs/EI2_REPORT.adoc
-- for the full record). The integration recipe with the existing five
-- named axes does NOT carry substantive simultaneous cross-axis
-- content. This file's "EI-2 IS NOT TERMINATED" comments below are
-- preserved as the historical record of the investigation while it
-- was still open; the authoritative current verdict is at the top of
-- docs/EI2_REPORT.adoc.
--
-- Distinctness against neighbour frameworks rests on the truncation
-- argument (`echo-not-prop` family in proofs/agda/examples/) and the
-- 2-cell argument (Sophisticated submodules of EchoVsQuotient.agda
-- and EchoVsGalois.agda), not on the integration argument. The
-- integration recipe remains useful as organising vocabulary; it is
-- not the locus of distinctness.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- characteristic.RoleGraded
--
-- Genuine cross-decoration integration: a 2D echo-indexed family
-- carrying *both* a role decoration (from EchoChoreo) and a grade
-- decoration (from EchoGraded), with two independent actions that
-- commute.
--
-- This module addresses the open recommendation flagged in
-- `docs/gate-2-handoff.adoc` Observation E:
--
--   "A genuine integration theorem — one in which a single Echo
--    carries both a role/choreographic decoration and a graded
--    decoration, and the two conjuncts share data — is not currently
--    in the repository. Building one is open work."
--
-- Per Observation E, a genuine integration must satisfy three tests:
--
--   1. A single echo-indexed family on which both decorations act.
--   2. A single conclusion in which a single application of an action
--      consumes both decoration witnesses.
--   3. The "same data" test: both sides of the conclusion mention
--      both decoration witnesses.
--
-- The withdrawn `EchoIntegration.knowledge-and-controlled-degradation`
-- failed test 3: its two conjuncts were over different functions and
-- shared no data. The construction below passes all three tests.
--
-- The headline theorem `choreo-grade-commute` says: the two actions
-- (role transport `applyRole` and grade degradation `applyGrade`)
-- commute on RoleGEcho. Both decorations appear on both sides of the
-- equation.
--
-- The theorem closes by `refl` in every case once the constructors of
-- the two propositional orders are pattern-matched. This is structural
-- echo-shape, not generic Σ machinery.
--
-- Honest qualification (tracked as EI-2 in `docs/next-questions.adoc`):
-- of the 18 cases, exactly one carries non-trivial content
-- (`(c⊑s, keep≤keep)`, reducing to `client-to-server e`). The other 17
-- close trivially because residue/forget grades collapse RoleGEcho to
-- ⊤ (12 cases) or because role-reachability constructors are
-- reflexive (5 cases). The 2D family is asymmetric: the role
-- parameter is only live at keep grade.
--
-- This is a *protocol-correct* closure of EI-1 (the Observation-E
-- hole identified in `gate-2-handoff.adoc`). It is *substantively
-- narrow*: the load-bearing cross-decoration content lives at one
-- cell. EI-2 asks whether the recipe is robust across other 2D
-- combinations (Role × Mode, Mode × Grade, etc.) or whether
-- RoleGraded benefited from a fortunate axis pair.
------------------------------------------------------------------------

module characteristic.RoleGraded where

open import Data.Bool.Base                        using (Bool; true)
open import Data.Unit.Base                        using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EchoChoreo                            using
  ( Role
  ; Client
  ; Server
  ; RoleEcho
  ; client-to-server
  ; _⊑c_
  ; c⊑c
  ; c⊑s
  ; s⊑s
  )
open import EchoGraded                            using
  ( Grade
  ; keep
  ; residue
  ; forget
  ; _≤g_
  ; keep≤keep
  ; keep≤residue
  ; keep≤forget
  ; residue≤residue
  ; residue≤forget
  ; forget≤forget
  )

------------------------------------------------------------------------
-- The 2D family
--
-- At keep grade: a full role-projected echo at the fixed visible value
-- `true`. Role information is live; the type genuinely varies with the
-- role parameter (RoleEcho Client ≠ RoleEcho Server).
--
-- At residue and forget grades: ⊤. The role information is gone
-- because the witness is gone — this is the standard structured-loss
-- pattern from EchoGraded.GEcho.
--
-- The choice to fix the visible value at `true` is a presentation
-- choice. Generalising to an arbitrary Bool (or a fully parametric
-- Y) is straightforward and would not change the theorem; it would
-- only widen the indexing.
------------------------------------------------------------------------

RoleGEcho : Role → Grade → Set
RoleGEcho r keep    = RoleEcho r true
RoleGEcho _ residue = ⊤
RoleGEcho _ forget  = ⊤

------------------------------------------------------------------------
-- Two independent actions on the 2D family
--
-- `applyRole` lifts an echo along the role-reachability order. At keep
-- grade it does real work (`client-to-server` for the strict step `c⊑s`).
-- At residue/forget it is the identity on ⊤ — once the witness is
-- gone, choreographic transport has nothing to do.
--
-- `applyGrade` degrades an echo along the loss-grade order. The keep →
-- {residue, forget} steps drop the witness; the residue → forget step
-- is identity on ⊤; the reflexive cases are identity.
--
-- Both actions are role-aware (resp. grade-aware) only at the keep
-- end of the grade lattice. Past that boundary, the type collapses
-- to ⊤ and both actions become trivial. This is the *standard*
-- structured-loss pattern, mirrored in EchoGraded and EchoLinear.
------------------------------------------------------------------------

applyRole :
  ∀ {r1 r2 g} → r1 ⊑c r2 → RoleGEcho r1 g → RoleGEcho r2 g
applyRole {g = keep}    c⊑c e = e
applyRole {g = keep}    c⊑s e = client-to-server e
applyRole {g = keep}    s⊑s e = e
applyRole {g = residue} _   _ = tt
applyRole {g = forget}  _   _ = tt

applyGrade :
  ∀ {r g1 g2} → g1 ≤g g2 → RoleGEcho r g1 → RoleGEcho r g2
applyGrade keep≤keep        e = e
applyGrade keep≤residue     _ = tt
applyGrade keep≤forget      _ = tt
applyGrade residue≤residue  e = e
applyGrade residue≤forget   _ = tt
applyGrade forget≤forget    e = e

------------------------------------------------------------------------
-- The headline integration theorem
--
-- The role action and the grade action commute: applying them in
-- either order on a RoleGEcho yields the same result.
--
-- Per Observation E, this passes the "same data" test: both `rp`
-- (role witness) and `gp` (grade witness) appear on *both* sides of
-- the equation, and `e` (the data) is consumed once on each side.
-- There is no decomposition into two separate facts; the equation
-- is a genuine constraint on the joint action.
--
-- Eighteen cases (3 role-order constructors × 6 grade-order
-- constructors). All close by `refl` after pattern matching, because
-- the residue/forget collapse to ⊤ and the reflexive grade step is
-- identity by definition.
--
-- The non-trivial case is (rp, gp) = (c⊑s, keep≤keep), where both
-- sides reduce to `client-to-server e`. The remaining cases are
-- trivial collapses to either `e` (reflexive) or `tt` (degenerate).
-- The theorem holds because the two actions never collide
-- non-trivially: at keep grade the grade action either keeps things
-- at keep (where role action is the only operation) or moves them
-- past keep (where role action becomes trivial).
------------------------------------------------------------------------

choreo-grade-commute :
  ∀ {r1 r2 g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2)
  (e : RoleGEcho r1 g1) →
  applyGrade gp (applyRole rp e) ≡ applyRole rp (applyGrade gp e)
choreo-grade-commute c⊑c keep≤keep       e = refl
choreo-grade-commute c⊑c keep≤residue    e = refl
choreo-grade-commute c⊑c keep≤forget     e = refl
choreo-grade-commute c⊑c residue≤residue e = refl
choreo-grade-commute c⊑c residue≤forget  e = refl
choreo-grade-commute c⊑c forget≤forget   e = refl
choreo-grade-commute c⊑s keep≤keep       e = refl
choreo-grade-commute c⊑s keep≤residue    e = refl
choreo-grade-commute c⊑s keep≤forget     e = refl
choreo-grade-commute c⊑s residue≤residue e = refl
choreo-grade-commute c⊑s residue≤forget  e = refl
choreo-grade-commute c⊑s forget≤forget   e = refl
choreo-grade-commute s⊑s keep≤keep       e = refl
choreo-grade-commute s⊑s keep≤residue    e = refl
choreo-grade-commute s⊑s keep≤forget     e = refl
choreo-grade-commute s⊑s residue≤residue e = refl
choreo-grade-commute s⊑s residue≤forget  e = refl
choreo-grade-commute s⊑s forget≤forget   e = refl

------------------------------------------------------------------------
-- The combined two-decoration action
--
-- Either ordering of the two actions can be used to define the
-- combined action `applyBoth`. The two definitions agree
-- (definitionally on each side, propositionally on each other via
-- `choreo-grade-commute`).
------------------------------------------------------------------------

applyBoth :
  ∀ {r1 r2 g1 g2} →
  r1 ⊑c r2 → g1 ≤g g2 → RoleGEcho r1 g1 → RoleGEcho r2 g2
applyBoth rp gp e = applyGrade gp (applyRole rp e)

applyBoth-via-other-order :
  ∀ {r1 r2 g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2) (e : RoleGEcho r1 g1) →
  applyBoth rp gp e ≡ applyRole rp (applyGrade gp e)
applyBoth-via-other-order rp gp e = choreo-grade-commute rp gp e

------------------------------------------------------------------------
-- Audit consequence (prose; the formal content is above)
--
-- The construction satisfies all three tests from
-- `docs/gate-2-handoff.adoc` Observation E:
--
--   1. *Single 2D family.* `RoleGEcho : Role → Grade → Set`
--      varies non-trivially in both axes (`RoleEcho Client true`
--      vs `RoleEcho Server true` at keep grade).
--   2. *Single combined action.* `applyBoth` consumes both decoration
--      witnesses (`rp` and `gp`) in one step.
--   3. *Same-data test.* Both sides of `choreo-grade-commute`'s
--      conclusion mention both `rp` and `gp` and consume the same
--      `e`. There is no split into independent conjuncts.
--
-- This is what the withdrawn `knowledge-and-controlled-degradation`
-- nominee was *trying* to be but was not. The withdrawn theorem's
-- conjuncts were over different functions; this theorem's two sides
-- are over the same data with both decorations applied.
--
-- The theorem `choreo-grade-commute` is a candidate Gate 2 nominee
-- (would be N5 if `roadmap-gates.adoc` is amended to include it).
-- The audit doc `docs/gate-2-characteristic.adoc` flags it as such.
-- Whether to add it is left to the integrator; the construction
-- itself stands regardless of nomination.
------------------------------------------------------------------------
