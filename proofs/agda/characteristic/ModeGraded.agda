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
-- characteristic.ModeGraded
--
-- Phase 2 of EI-2 (`docs/next-questions.adoc`): the second sibling
-- integration construction. Mode × Grade as a 2D family with two
-- independent actions and a commutation theorem.
--
-- Built to test EI-2's robustness question: "is the integration recipe
-- robust across other 2D combinations, or did `RoleGraded` benefit
-- from a fortunate axis pair?"
--
-- Structure mirrors `characteristic.RoleGraded` precisely:
--
--   * 2D family `MGEcho : Mode → Grade → Set`.
--   * Two independent actions (`applyMode`, `applyGrade`).
--   * Commutation theorem `mode-grade-commute` (the headline).
--   * Combined two-decoration action `applyBoth`.
--
-- Trivial-case ratio measurement is the load-bearing observation here.
-- See the "EI-2 measurement" block at the end of this file for the
-- count and the per-cell verdict.
--
-- Status of EI-2 after this construction: NOT TERMINATED. EI-2
-- remains open until either (a) all sibling constructions show
-- non-trivial multi-cell content, terminating positively, or (b) the
-- pattern of trivial-case dominance is uniform across all sibling
-- constructions, terminating negatively. With one sibling so far,
-- neither condition is met.
------------------------------------------------------------------------

module characteristic.ModeGraded where

open import Data.Unit.Base                        using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EchoLinear                            using
  ( Mode
  ; linear
  ; affine
  ; LEcho
  ; weaken
  ; _≤m_
  ; linear≤linear
  ; linear≤affine
  ; affine≤affine
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
-- At (linear, keep): a full LEcho carrying the linearity-mode witness.
-- At all other cells: collapsed to ⊤.
--
-- Note (EI-2 measurement): of the 6 cells in the 2D index space
-- (Mode × Grade = 2 × 3), only ONE cell is non-trivially live —
-- (linear, keep). The other 5 cells are all ⊤.
--
-- This is a *worse* collapse pattern than `RoleGraded` had, where
-- 3 of 6 grade-keep cells were live (one per role constructor).
-- Here, both axes' "dead" positions collapse together: affine kills
-- the live structure same as residue/forget do.
------------------------------------------------------------------------

MGEcho : Mode → Grade → Set
MGEcho linear keep    = LEcho linear
MGEcho linear residue = ⊤
MGEcho linear forget  = ⊤
MGEcho affine  _      = ⊤

------------------------------------------------------------------------
-- Two independent actions on the 2D family
--
-- `applyMode` lifts an LEcho along the mode order.
-- `applyGrade` degrades an LEcho along the grade order.
--
-- Both actions degenerate to `tt` away from (linear, keep). The single
-- non-trivial action site is (linear, keep) → (affine, keep), which
-- becomes (linear, keep) → ⊤ via the asymmetric collapse — i.e., even
-- the one live cell's outgoing actions immediately leave the live
-- region.
------------------------------------------------------------------------

applyMode :
  ∀ {m1 m2 g} → m1 ≤m m2 → MGEcho m1 g → MGEcho m2 g
applyMode {g = keep}    linear≤linear e = e
applyMode {g = keep}    linear≤affine _ = tt    -- live → dead
applyMode {g = keep}    affine≤affine e = e
applyMode {g = residue} linear≤linear _ = tt
applyMode {g = residue} linear≤affine _ = tt
applyMode {g = residue} affine≤affine _ = tt
applyMode {g = forget}  linear≤linear _ = tt
applyMode {g = forget}  linear≤affine _ = tt
applyMode {g = forget}  affine≤affine _ = tt

applyGrade :
  ∀ {m g1 g2} → g1 ≤g g2 → MGEcho m g1 → MGEcho m g2
applyGrade {m = linear} keep≤keep        e = e
applyGrade {m = linear} keep≤residue     _ = tt
applyGrade {m = linear} keep≤forget      _ = tt
applyGrade {m = linear} residue≤residue  e = e
applyGrade {m = linear} residue≤forget   _ = tt
applyGrade {m = linear} forget≤forget    e = e
applyGrade {m = affine} keep≤keep        e = e
applyGrade {m = affine} keep≤residue     _ = tt
applyGrade {m = affine} keep≤forget      _ = tt
applyGrade {m = affine} residue≤residue  e = e
applyGrade {m = affine} residue≤forget   _ = tt
applyGrade {m = affine} forget≤forget    e = e

------------------------------------------------------------------------
-- The headline integration theorem
--
-- The mode action and the grade action commute on MGEcho.
--
-- Cases: 3 mode-order constructors × 6 grade-order constructors
--      = 18 cases.
--
-- All cases close by `refl`. Per the EI-2 measurement at the
-- bottom of this file, the count of non-trivial cases (where
-- both sides involve a non-trivial reduction) is ZERO. Every
-- case is either a reflexive identity or a degenerate ⊤ collapse.
--
-- This is a *strictly weaker* result than `RoleGraded`'s
-- `choreo-grade-commute`, which had ONE non-trivial case
-- (`(c⊑s, keep≤keep)` reducing to `client-to-server e`).
-- ModeGraded has NONE.
--
-- This is a real result, not an artefact: there is no analogue of
-- `client-to-server` for the mode axis, because the only Mode
-- constructor that does work (`linear≤affine`) lands in the dead
-- region (affine), not in another live cell. The mode lattice is
-- *too small* to exhibit non-trivial cross-axis interaction in 2D.
------------------------------------------------------------------------

mode-grade-commute :
  ∀ {m1 m2 g1 g2}
  (mp : m1 ≤m m2) (gp : g1 ≤g g2)
  (e : MGEcho m1 g1) →
  applyGrade {m = m2} gp (applyMode {g = g1} mp e) ≡ applyMode {g = g2} mp (applyGrade {m = m1} gp e)
mode-grade-commute linear≤linear keep≤keep       e = refl
mode-grade-commute linear≤linear keep≤residue    e = refl
mode-grade-commute linear≤linear keep≤forget     e = refl
mode-grade-commute linear≤linear residue≤residue e = refl
mode-grade-commute linear≤linear residue≤forget  e = refl
mode-grade-commute linear≤linear forget≤forget   e = refl
mode-grade-commute linear≤affine keep≤keep       e = refl
mode-grade-commute linear≤affine keep≤residue    e = refl
mode-grade-commute linear≤affine keep≤forget     e = refl
mode-grade-commute linear≤affine residue≤residue e = refl
mode-grade-commute linear≤affine residue≤forget  e = refl
mode-grade-commute linear≤affine forget≤forget   e = refl
mode-grade-commute affine≤affine keep≤keep       e = refl
mode-grade-commute affine≤affine keep≤residue    e = refl
mode-grade-commute affine≤affine keep≤forget     e = refl
mode-grade-commute affine≤affine residue≤residue e = refl
mode-grade-commute affine≤affine residue≤forget  e = refl
mode-grade-commute affine≤affine forget≤forget   e = refl

------------------------------------------------------------------------
-- The combined two-decoration action
------------------------------------------------------------------------

applyBoth :
  ∀ {m1 m2 g1 g2} →
  m1 ≤m m2 → g1 ≤g g2 → MGEcho m1 g1 → MGEcho m2 g2
applyBoth {m2 = m2} mp gp e = applyGrade {m = m2} gp (applyMode {g = _} mp e)

applyBoth-via-other-order :
  ∀ {m1 m2 g1 g2}
  (mp : m1 ≤m m2) (gp : g1 ≤g g2) (e : MGEcho m1 g1) →
  applyBoth mp gp e ≡ applyMode {g = g2} mp (applyGrade {m = m1} gp e)
applyBoth-via-other-order mp gp e = mode-grade-commute mp gp e

------------------------------------------------------------------------
-- EI-2 MEASUREMENT
--
-- Per the EI-2 attack plan, this construction is being measured against
-- `RoleGraded` for trivial-case dominance. The metric: of the N cases
-- in the commutation theorem, how many carry non-trivial cross-axis
-- content (i.e., both sides involve a non-trivial reduction that
-- isn't `e = e` by reflexivity or `tt = tt` by ⊤-degeneracy)?
--
-- Cell-by-cell verdict for `mode-grade-commute`:
--
-- (linear≤linear, *)        — 6 cases. Mode action is identity; reduces
--                              to applyGrade gp e on both sides.
--                              TRIVIAL: identity-on-mode collapse.
--
-- (linear≤affine, keep≤keep) — 1 case. Mode action takes (linear, keep)
--                              to ⊤ (the dead region). Both sides
--                              reduce to tt.
--                              TRIVIAL: live → dead degeneracy.
--
-- (linear≤affine, residue≤residue, residue≤forget, forget≤forget,
--  keep≤residue, keep≤forget) — 5 cases. All grade actions land in
--                              dead positions; all mode actions land
--                              in dead positions. Both sides tt.
--                              TRIVIAL: dead-everywhere.
--
-- (affine≤affine, *)        — 6 cases. Mode action is identity on
--                              MGEcho affine = ⊤. Both sides reduce
--                              to tt or e.
--                              TRIVIAL: dead-region identity.
--
-- TOTAL: 0 non-trivial cells of 18.
--
-- COMPARISON WITH ROLEGRADED:
--   RoleGraded: 1 non-trivial cell of 18 (`(c⊑s, keep≤keep)`)
--   ModeGraded: 0 non-trivial cells of 18
--
-- ModeGraded is *strictly weaker* than RoleGraded on the EI-2 metric.
-- The construction satisfies the protocol (it is a 2D family with two
-- actions that commute) but provides ZERO substantive cross-axis
-- content.
--
-- WHY: the mode lattice has only one non-reflexive constructor
-- (`linear≤affine`), and that constructor's target is the dead region
-- (affine = ⊤). There is no analogue of `client-to-server` because
-- there is no live target for the mode action to land in. The Mode
-- axis is "too thin" for 2D recipe instantiation.
--
-- IMPLICATIONS FOR EI-2:
--
-- 1. NEGATIVE-TERMINATION RISK INCREASES. Two of two constructions
--    so far show 1-or-fewer non-trivial cells. If the third sibling
--    (`RoleMode`) also shows ≤1 non-trivial cells, the negative-
--    termination criterion in EI-2's stopping rules is approached.
--
-- 2. THE ASYMMETRIC COLLAPSE IS STRUCTURAL TO THE AXES, NOT TO
--    THE PAIRINGS. Mode and Grade both have the property that their
--    "non-keep / non-linear" positions collapse to ⊤. This is not a
--    bug in `RoleGraded`'s construction — it's a feature of the axes
--    themselves. Any 2D pairing of Mode and Grade (or pairings
--    involving either) inherits the collapse.
--
-- 3. THE LIVE-CELL COUNT FOR ROLEGRADED COMES FROM ROLE BEING
--    NON-COLLAPSING. `RoleGraded` gets its 1-of-18 because Role's
--    constructors don't collapse to ⊤ at any role. The single
--    non-trivial cell in `RoleGraded` corresponds to the single
--    non-reflexive role-order constructor (`c⊑s`) at the live grade
--    cell (keep). If the third sibling (`RoleMode`) has Mode
--    collapsing while Role doesn't, expected non-trivial cell count
--    is 1 (from `c⊑s`), matching `RoleGraded`.
--
-- EI-2 is NOT TERMINATED. Two sibling constructions complete; one
-- more (RoleMode) needed to test the prediction in (3) and confirm
-- or refute the negative-termination trajectory.
------------------------------------------------------------------------
