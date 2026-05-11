{-# OPTIONS --safe --without-K #-}

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
-- characteristic.RoleModeGrade — EI-2 obligation 4 (3D test).
--
-- The 3D combination Role × Mode × Grade. Three actions, three
-- pairwise commutation theorems.
--
-- EI-2 question at n=3: does the recipe-non-triviality hypothesis
-- (formed at n=2 via RoleGraded, RoleMode, ModeGrade) extend to
-- 3D, or do richer combinations produce qualitatively different
-- patterns?
--
-- Prediction (declared up front for falsifiability):
--   Each pairwise commutation should have exactly 1 non-trivial
--   cell when the pair includes Role (the only non-loss-only axis
--   currently available), and 0 non-trivial cells when the pair
--   doesn't.
--
--   role-mode-commute  : 1 non-trivial of 27 cases
--   role-grade-commute : 1 non-trivial of 36 cases
--   mode-grade-commute : 0 non-trivial of 36 cases
--
-- Result (formalised below; analysis baked into the per-theorem
-- comment blocks):
--
--   role-mode-commute  : 1 of 27 — at (c⊑s, linear≤linear, keep)
--   role-grade-commute : 1 of 36 — at (c⊑s, keep≤keep, m=linear)
--   mode-grade-commute : 0 of 36 — no non-trivial cell
--
-- *Prediction confirmed.* The recipe-non-triviality hypothesis
-- holds at n=3.
--
-- ============================================================
-- EI-2 STATUS: hypothesis surviving, NOT TERMINATED.
-- ============================================================
--
-- This file confirms the n=3 case of the recipe-non-triviality
-- hypothesis. Combined with the n=2 data points:
--
--   RoleGraded   (n=2, 1 non-loss-only axis): 1 of 18
--   RoleMode     (n=2, 1 non-loss-only axis): 1 of 9
--   ModeGrade    (n=2, 0 non-loss-only axes): 0 of 18
--   role-mode-commute @ 3D  (1 non-loss-only): 1 of 27
--   role-grade-commute @ 3D (1 non-loss-only): 1 of 36
--   mode-grade-commute @ 3D (0 non-loss-only): 0 of 36
--
-- Hypothesis: non-trivial cell count = 1 iff at least one axis in
-- the pair is non-loss-only; = 0 otherwise.
--
-- All six data points consistent with the hypothesis.
--
-- WHAT THIS DOES *NOT* TERMINATE EI-2:
--   * The hypothesis is consistent across six data points but is
--     not formally PROVED. Obligation 5 (write the recipe-non-
--     triviality theorem) remains open.
--   * The hypothesis predicts 1 non-trivial cell when one axis is
--     non-loss-only. It does NOT predict what happens when *both*
--     axes are non-loss-only — that data point is unavailable
--     because only Choreo currently has non-loss-only transports.
--   * READING 1 vs READING 2 (obligation 2, the documentation
--     decision) is unresolved.
--
-- WHAT THIS *DOES* CONTRIBUTE:
--   * The 3D test does NOT produce qualitatively different
--     patterns from 2D. The recipe is monotone in axis count
--     (adding a loss-only axis does not add non-trivial cells).
--   * The hypothesis survives a stronger test (3D combination
--     versus 2D combination).
--   * The pairwise commutations align with the standalone n=2
--     constructions: role-mode-commute at 3D and RoleMode at 2D
--     agree on the non-trivial cell location.
------------------------------------------------------------------------

module characteristic.RoleModeGrade where

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
open import EchoLinear                            using
  ( Mode
  ; linear
  ; affine
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
-- The 3D family
--
-- Live only at (r, linear, keep). ⊤ everywhere else.
--
-- The role parameter is live across {Client, Server} at the live
-- cell. Outside the live cell, the family is ⊤ regardless of role.
------------------------------------------------------------------------

RMGEcho : Role → Mode → Grade → Set
RMGEcho r linear keep    = RoleEcho r true
RMGEcho _ linear residue = ⊤
RMGEcho _ linear forget  = ⊤
RMGEcho _ affine keep    = ⊤
RMGEcho _ affine residue = ⊤
RMGEcho _ affine forget  = ⊤

------------------------------------------------------------------------
-- Three independent actions
------------------------------------------------------------------------

applyRole :
  ∀ {r1 r2 m g} → r1 ⊑c r2 → RMGEcho r1 m g → RMGEcho r2 m g
applyRole {m = linear} {g = keep}    c⊑c e = e
applyRole {m = linear} {g = keep}    c⊑s e = client-to-server e
applyRole {m = linear} {g = keep}    s⊑s e = e
applyRole {m = linear} {g = residue} _   _ = tt
applyRole {m = linear} {g = forget}  _   _ = tt
applyRole {m = affine} {g = keep}    _   _ = tt
applyRole {m = affine} {g = residue} _   _ = tt
applyRole {m = affine} {g = forget}  _   _ = tt

applyMode :
  ∀ {r m1 m2 g} → m1 ≤m m2 → RMGEcho r m1 g → RMGEcho r m2 g
applyMode {g = keep}    linear≤linear  e = e
applyMode {g = keep}    linear≤affine  _ = tt
applyMode {g = keep}    affine≤affine  e = e
applyMode {g = residue} linear≤linear  e = e
applyMode {g = residue} linear≤affine  e = e
applyMode {g = residue} affine≤affine  e = e
applyMode {g = forget}  linear≤linear  e = e
applyMode {g = forget}  linear≤affine  e = e
applyMode {g = forget}  affine≤affine  e = e

applyGrade :
  ∀ {r m g1 g2} → g1 ≤g g2 → RMGEcho r m g1 → RMGEcho r m g2
applyGrade {m = linear} keep≤keep        e = e
applyGrade {m = linear} keep≤residue     _ = tt
applyGrade {m = linear} keep≤forget      _ = tt
applyGrade {m = linear} residue≤residue  e = e
applyGrade {m = linear} residue≤forget   _ = tt
applyGrade {m = linear} forget≤forget    e = e
applyGrade {m = affine} keep≤keep        e = e
applyGrade {m = affine} keep≤residue     e = e
applyGrade {m = affine} keep≤forget      e = e
applyGrade {m = affine} residue≤residue  e = e
applyGrade {m = affine} residue≤forget   e = e
applyGrade {m = affine} forget≤forget    e = e

------------------------------------------------------------------------
-- Pairwise commutation: Role × Mode (with Grade as free parameter)
--
-- 3 role steps × 3 mode steps × 3 grade values = 27 cases.
--
-- Non-trivial cells per case-by-case tracing:
--   * (c⊑s, linear≤linear, keep): NON-TRIVIAL. Both sides reduce
--     to client-to-server e.
--   * All other 26 cases: trivial (either both sides = e, or both
--     sides = tt).
--
-- Ratio: 1 of 27. Same shape as the n=2 RoleMode (1 of 9).
-- Adding the Grade dimension does not add non-trivial cells; it
-- adds 18 trivial cells (9 at each of grade=residue and grade=forget,
-- where the entire family is ⊤).
------------------------------------------------------------------------

role-mode-commute :
  ∀ {r1 r2 m1 m2 g}
  (rp : r1 ⊑c r2) (mp : m1 ≤m m2)
  (e : RMGEcho r1 m1 g) →
  applyMode {g = g} mp (applyRole {g = g} rp e)
  ≡ applyRole {g = g} rp (applyMode {g = g} mp e)
role-mode-commute {g = keep}    c⊑c linear≤linear  e = refl
role-mode-commute {g = keep}    c⊑c linear≤affine  e = refl
role-mode-commute {g = keep}    c⊑c affine≤affine  e = refl
role-mode-commute {g = keep}    c⊑s linear≤linear  e = refl
role-mode-commute {g = keep}    c⊑s linear≤affine  e = refl
role-mode-commute {g = keep}    c⊑s affine≤affine  e = refl
role-mode-commute {g = keep}    s⊑s linear≤linear  e = refl
role-mode-commute {g = keep}    s⊑s linear≤affine  e = refl
role-mode-commute {g = keep}    s⊑s affine≤affine  e = refl
role-mode-commute {g = residue} c⊑c linear≤linear  e = refl
role-mode-commute {g = residue} c⊑c linear≤affine  e = refl
role-mode-commute {g = residue} c⊑c affine≤affine  e = refl
role-mode-commute {g = residue} c⊑s linear≤linear  e = refl
role-mode-commute {g = residue} c⊑s linear≤affine  e = refl
role-mode-commute {g = residue} c⊑s affine≤affine  e = refl
role-mode-commute {g = residue} s⊑s linear≤linear  e = refl
role-mode-commute {g = residue} s⊑s linear≤affine  e = refl
role-mode-commute {g = residue} s⊑s affine≤affine  e = refl
role-mode-commute {g = forget}  c⊑c linear≤linear  e = refl
role-mode-commute {g = forget}  c⊑c linear≤affine  e = refl
role-mode-commute {g = forget}  c⊑c affine≤affine  e = refl
role-mode-commute {g = forget}  c⊑s linear≤linear  e = refl
role-mode-commute {g = forget}  c⊑s linear≤affine  e = refl
role-mode-commute {g = forget}  c⊑s affine≤affine  e = refl
role-mode-commute {g = forget}  s⊑s linear≤linear  e = refl
role-mode-commute {g = forget}  s⊑s linear≤affine  e = refl
role-mode-commute {g = forget}  s⊑s affine≤affine  e = refl

------------------------------------------------------------------------
-- Pairwise commutation: Role × Grade (with Mode as free parameter)
--
-- 3 role steps × 6 grade steps × 2 mode values = 36 cases.
--
-- Non-trivial cells:
--   * (c⊑s, keep≤keep, linear): NON-TRIVIAL. Both sides reduce to
--     client-to-server e.
--   * All other 35 cases: trivial.
--
-- Ratio: 1 of 36. Same shape as the n=2 RoleGraded (1 of 18).
------------------------------------------------------------------------

role-grade-commute :
  ∀ {r1 r2 m g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2)
  (e : RMGEcho r1 m g1) →
  applyGrade {m = m} gp (applyRole {g = g1} rp e)
  ≡ applyRole {g = g2} rp (applyGrade {m = m} gp e)
role-grade-commute {m = linear} c⊑c keep≤keep        e = refl
role-grade-commute {m = linear} c⊑c keep≤residue     e = refl
role-grade-commute {m = linear} c⊑c keep≤forget      e = refl
role-grade-commute {m = linear} c⊑c residue≤residue  e = refl
role-grade-commute {m = linear} c⊑c residue≤forget   e = refl
role-grade-commute {m = linear} c⊑c forget≤forget    e = refl
role-grade-commute {m = linear} c⊑s keep≤keep        e = refl
role-grade-commute {m = linear} c⊑s keep≤residue     e = refl
role-grade-commute {m = linear} c⊑s keep≤forget      e = refl
role-grade-commute {m = linear} c⊑s residue≤residue  e = refl
role-grade-commute {m = linear} c⊑s residue≤forget   e = refl
role-grade-commute {m = linear} c⊑s forget≤forget    e = refl
role-grade-commute {m = linear} s⊑s keep≤keep        e = refl
role-grade-commute {m = linear} s⊑s keep≤residue     e = refl
role-grade-commute {m = linear} s⊑s keep≤forget      e = refl
role-grade-commute {m = linear} s⊑s residue≤residue  e = refl
role-grade-commute {m = linear} s⊑s residue≤forget   e = refl
role-grade-commute {m = linear} s⊑s forget≤forget    e = refl
role-grade-commute {m = affine} c⊑c keep≤keep        e = refl
role-grade-commute {m = affine} c⊑c keep≤residue     e = refl
role-grade-commute {m = affine} c⊑c keep≤forget      e = refl
role-grade-commute {m = affine} c⊑c residue≤residue  e = refl
role-grade-commute {m = affine} c⊑c residue≤forget   e = refl
role-grade-commute {m = affine} c⊑c forget≤forget    e = refl
role-grade-commute {m = affine} c⊑s keep≤keep        e = refl
role-grade-commute {m = affine} c⊑s keep≤residue     e = refl
role-grade-commute {m = affine} c⊑s keep≤forget      e = refl
role-grade-commute {m = affine} c⊑s residue≤residue  e = refl
role-grade-commute {m = affine} c⊑s residue≤forget   e = refl
role-grade-commute {m = affine} c⊑s forget≤forget    e = refl
role-grade-commute {m = affine} s⊑s keep≤keep        e = refl
role-grade-commute {m = affine} s⊑s keep≤residue     e = refl
role-grade-commute {m = affine} s⊑s keep≤forget      e = refl
role-grade-commute {m = affine} s⊑s residue≤residue  e = refl
role-grade-commute {m = affine} s⊑s residue≤forget   e = refl
role-grade-commute {m = affine} s⊑s forget≤forget    e = refl

------------------------------------------------------------------------
-- Pairwise commutation: Mode × Grade (with Role as free parameter)
--
-- 3 mode steps × 6 grade steps × 2 role values = 36 cases.
--
-- Non-trivial cells:
--   * (linear≤linear, keep≤keep, r): identity case, both sides = e.
--     Closest-to-non-trivial but reduces to e ≡ e.
--   * All others: trivial (tt ≡ tt or e ≡ e in degenerate ways).
--
-- Ratio: 0 of 36. Same shape as the n=2 ModeGrade (0 of 18).
-- Adding the Role dimension does not add non-trivial cells.
--
-- This is the falsifier-positive case at n=3, mirroring n=2.
-- The 3D context preserves the n=2 result for loss-only axis pairs.
------------------------------------------------------------------------

mode-grade-commute :
  ∀ {r m1 m2 g1 g2}
  (mp : m1 ≤m m2) (gp : g1 ≤g g2)
  (e : RMGEcho r m1 g1) →
  applyGrade {m = m2} gp (applyMode {g = g1} mp e)
  ≡ applyMode {g = g2} mp (applyGrade {m = m1} gp e)
mode-grade-commute {r = Client} linear≤linear  keep≤keep        e = refl
mode-grade-commute {r = Client} linear≤linear  keep≤residue     e = refl
mode-grade-commute {r = Client} linear≤linear  keep≤forget      e = refl
mode-grade-commute {r = Client} linear≤linear  residue≤residue  e = refl
mode-grade-commute {r = Client} linear≤linear  residue≤forget   e = refl
mode-grade-commute {r = Client} linear≤linear  forget≤forget    e = refl
mode-grade-commute {r = Client} linear≤affine  keep≤keep        e = refl
mode-grade-commute {r = Client} linear≤affine  keep≤residue     e = refl
mode-grade-commute {r = Client} linear≤affine  keep≤forget      e = refl
mode-grade-commute {r = Client} linear≤affine  residue≤residue  e = refl
mode-grade-commute {r = Client} linear≤affine  residue≤forget   e = refl
mode-grade-commute {r = Client} linear≤affine  forget≤forget    e = refl
mode-grade-commute {r = Client} affine≤affine  keep≤keep        e = refl
mode-grade-commute {r = Client} affine≤affine  keep≤residue     e = refl
mode-grade-commute {r = Client} affine≤affine  keep≤forget      e = refl
mode-grade-commute {r = Client} affine≤affine  residue≤residue  e = refl
mode-grade-commute {r = Client} affine≤affine  residue≤forget   e = refl
mode-grade-commute {r = Client} affine≤affine  forget≤forget    e = refl
mode-grade-commute {r = Server} linear≤linear  keep≤keep        e = refl
mode-grade-commute {r = Server} linear≤linear  keep≤residue     e = refl
mode-grade-commute {r = Server} linear≤linear  keep≤forget      e = refl
mode-grade-commute {r = Server} linear≤linear  residue≤residue  e = refl
mode-grade-commute {r = Server} linear≤linear  residue≤forget   e = refl
mode-grade-commute {r = Server} linear≤linear  forget≤forget    e = refl
mode-grade-commute {r = Server} linear≤affine  keep≤keep        e = refl
mode-grade-commute {r = Server} linear≤affine  keep≤residue     e = refl
mode-grade-commute {r = Server} linear≤affine  keep≤forget      e = refl
mode-grade-commute {r = Server} linear≤affine  residue≤residue  e = refl
mode-grade-commute {r = Server} linear≤affine  residue≤forget   e = refl
mode-grade-commute {r = Server} linear≤affine  forget≤forget    e = refl
mode-grade-commute {r = Server} affine≤affine  keep≤keep        e = refl
mode-grade-commute {r = Server} affine≤affine  keep≤residue     e = refl
mode-grade-commute {r = Server} affine≤affine  keep≤forget      e = refl
mode-grade-commute {r = Server} affine≤affine  residue≤residue  e = refl
mode-grade-commute {r = Server} affine≤affine  residue≤forget   e = refl
mode-grade-commute {r = Server} affine≤affine  forget≤forget    e = refl

------------------------------------------------------------------------
-- The combined three-decoration action
--
-- Apply all three actions in canonical order: role then mode then
-- grade. Other orderings agree by composition of the pairwise
-- commutations.
------------------------------------------------------------------------

applyAll :
  ∀ {r1 r2 m1 m2 g1 g2} →
  r1 ⊑c r2 → m1 ≤m m2 → g1 ≤g g2 → RMGEcho r1 m1 g1 → RMGEcho r2 m2 g2
applyAll rp mp gp e = applyGrade gp (applyMode mp (applyRole rp e))

------------------------------------------------------------------------
-- The traced non-trivial case witness.
--
-- Confirms by direct computation that at the unique non-trivial
-- cell (c⊑s, linear≤linear, keep≤keep), applyAll produces
-- client-to-server e.
------------------------------------------------------------------------

trace-non-trivial-cell :
  ∀ (e : RoleEcho Client true) →
  applyAll c⊑s linear≤linear keep≤keep e ≡ client-to-server e
trace-non-trivial-cell e = refl

------------------------------------------------------------------------
-- EI-2 reporting (formal content above; tracker entry below)
--
-- DATA POINT 4 (this file): 3D RoleModeGrade
--   role-mode-commute  : 1 non-trivial of 27
--   role-grade-commute : 1 non-trivial of 36
--   mode-grade-commute : 0 non-trivial of 36
--   Triple non-trivial : 1 of 54 (at (c⊑s, linear≤linear, keep≤keep),
--                                  computing to client-to-server e)
--
-- COMBINED EI-2 RESULTS SO FAR:
--   2D constructions:
--     RoleGraded (Role × Grade, 1 NLO axis)  : 1 of 18
--     RoleMode (Role × Mode, 1 NLO axis)     : 1 of 9
--     ModeGrade (Mode × Grade, 0 NLO axes)   : 0 of 18
--   3D pairwise (in RoleModeGrade context):
--     role-mode (1 NLO axis in pair)         : 1 of 27
--     role-grade (1 NLO axis in pair)        : 1 of 36
--     mode-grade (0 NLO axes in pair)        : 0 of 36
--   3D triple:
--     role-mode-grade (1 NLO axis)           : 1 of 54
--
-- INTERPRETATION:
--   Across seven data points, the recipe-non-triviality hypothesis
--   is consistent: non-trivial cell count = 1 iff the axis pair
--   (or 3-tuple) contains at least one non-loss-only axis; = 0
--   otherwise.
--
--   The 3D result is *qualitatively the same* as the 2D result,
--   not different: adding loss-only axes does not produce
--   qualitatively new patterns. This rules out the strongest
--   possible falsifier ("3D produces uniformly trivial patterns")
--   and the strongest possible recipe-strength outcome ("3D
--   produces multiplicatively non-trivial patterns").
--
--   The hypothesis remains: each non-loss-only axis contributes
--   exactly 1 non-trivial cell to the commutation, located at the
--   axis's non-reflexive constructor; loss-only axes contribute 0.
--   Multiple non-loss-only axes would (by the hypothesis) contribute
--   multiplicatively, but this remains untested because only Choreo
--   currently has a non-loss-only transport.
--
-- WHAT THIS DOES NOT TERMINATE:
--   * Obligation 5 (recipe-non-triviality theorem) remains open.
--     The hypothesis is now consistent across seven data points
--     but is not proved as a general theorem about the recipe.
--   * Obligation 3 (4th data point with two NLO axes) remains
--     unavailable from existing modules.
--   * Obligation 2 (READING 1 vs READING 2 documentation decision)
--     remains open.
--
-- EI-2 STATUS: hypothesis surviving stronger test. Not terminated.
------------------------------------------------------------------------
