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
-- characteristic.RoleMode — EI-2 sibling construction to RoleGraded.
--
-- The second 2D combination in the integration recipe: Role × Mode.
-- This is the most directly comparable construction to RoleGraded
-- (which is Role × Grade) because Role appears in both, isolating
-- the question of whether the second axis (Grade vs Mode) drives the
-- trivial-case dominance pattern.
--
-- EI-2 question: did RoleGraded benefit from a fortunate choice of
-- second axis, or does the recipe produce a similar 1-of-N
-- non-trivial-case pattern across other 2D combinations?
--
-- This file's contribution to that question:
--
--   * Builds RoleMEcho : Role → Mode → Set following the same
--     structural pattern as RoleGEcho.
--   * Builds the two independent actions applyRole and applyMode.
--   * Builds the analogous integration theorem
--     `choreo-mode-commute`.
--   * Reports the trivial:non-trivial ratio for direct comparison.
--
-- Result (declared up front for the EI-2 tracker):
--   * 9 cases (3 role constructors × 3 mode constructors)
--   * Of these, 1 is non-trivial: (c⊑s, linear≤linear), reducing
--     to client-to-server e.
--   * 8 trivial: 6 from mode-residue collapse to ⊤ at affine grade
--     (c⊑c at affine, c⊑s at linear≤affine, c⊑s at affine≤affine,
--     s⊑s at affine, etc.) and 2 from reflexive role constructors
--     at linear (c⊑c at linear≤linear, s⊑s at linear≤linear).
--
-- Ratio: 1:8. Same shape as RoleGraded's 1:17. Per-cell density of
-- non-trivial content is comparable; both have exactly one cell
-- where role transport does meaningful work.
--
-- Structural reading: the recipe produces ONE non-trivial cell per
-- 2D combination, located at (non-reflexive role transport, live
-- second-axis cell). The denominator scales with the size of the
-- second axis's order. RoleGraded's 1:17 and RoleMode's 1:8 both
-- exhibit this; RoleMode confirms RoleGraded was not a fortunate
-- choice.
--
-- This is partial evidence for EI-2 but not a closure. The
-- pattern needs to hold for at least one more pair (Mode × Grade,
-- where neither axis is the choreographic Role) before EI-2 can
-- be declared substantively closed. See ModeGrade.agda (next).
------------------------------------------------------------------------

module characteristic.RoleMode where

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

------------------------------------------------------------------------
-- The 2D family
--
-- At linear mode: a role-projected echo at the fixed visible value
-- `true`. Role information is live; the type genuinely varies with
-- the role parameter.
--
-- At affine mode: ⊤. The role information is gone — the affine
-- weakening collapses the type. This mirrors RoleGEcho's
-- residue/forget collapse to ⊤.
--
-- Note on the asymmetry: as in RoleGraded, the role parameter is
-- only live at one end of the second-axis order (linear here, keep
-- there). This is the structural pattern EI-2 is interrogating.
------------------------------------------------------------------------

RoleMEcho : Role → Mode → Set
RoleMEcho r linear = RoleEcho r true
RoleMEcho _ affine = ⊤

------------------------------------------------------------------------
-- Two independent actions on the 2D family
--
-- `applyRole` lifts an echo along the role-reachability order. At
-- linear mode it does real work (`client-to-server` for the strict
-- step `c⊑s`). At affine mode it is the identity on ⊤.
--
-- `applyMode` weakens an echo along the linearity order. The strict
-- `linear → affine` step drops the witness (collapses to ⊤); the
-- reflexive cases are identity.
--
-- The role action is role-aware only at the linear end of the
-- mode lattice. Past that boundary, the type collapses to ⊤ and
-- both actions become trivial. Same pattern as RoleGEcho.
------------------------------------------------------------------------

applyRole :
  ∀ {r1 r2 m} → r1 ⊑c r2 → RoleMEcho r1 m → RoleMEcho r2 m
applyRole {m = linear} c⊑c e = e
applyRole {m = linear} c⊑s e = client-to-server e
applyRole {m = linear} s⊑s e = e
applyRole {m = affine} _   _ = tt

applyMode :
  ∀ {r m1 m2} → m1 ≤m m2 → RoleMEcho r m1 → RoleMEcho r m2
applyMode linear≤linear  e = e
applyMode linear≤affine  _ = tt
applyMode affine≤affine  e = e

------------------------------------------------------------------------
-- The headline integration theorem
--
-- The role action and the mode action commute on RoleMEcho.
--
-- Per Observation E (the criterion EI-1 was held to), this passes
-- the same-data test: both `rp` (role witness) and `mp` (mode
-- witness) appear on both sides of the equation.
--
-- 9 cases (3 role-order constructors × 3 mode-order constructors).
-- Pattern of triviality:
--
--   Case                          | Closes by | Why
--   ------------------------------+-----------+----------------------
--   (c⊑c, linear≤linear)          | refl      | both reflexive
--   (c⊑c, linear≤affine)          | refl      | mode-collapse to ⊤
--   (c⊑c, affine≤affine)          | refl      | mode = ⊤ both sides
--   (c⊑s, linear≤linear)          | refl      | NON-TRIVIAL: both
--                                 |           |  sides reduce to
--                                 |           |  client-to-server e
--   (c⊑s, linear≤affine)          | refl      | mode-collapse to ⊤
--   (c⊑s, affine≤affine)          | refl      | mode = ⊤ both sides
--   (s⊑s, linear≤linear)          | refl      | both reflexive
--   (s⊑s, linear≤affine)          | refl      | mode-collapse to ⊤
--   (s⊑s, affine≤affine)          | refl      | mode = ⊤ both sides
--
-- 1 non-trivial cell of 9. Ratio matches RoleGraded's 1 of 18 in
-- structural shape (one (non-reflexive role, live mode) cell).
------------------------------------------------------------------------

choreo-mode-commute :
  ∀ {r1 r2 m1 m2}
  (rp : r1 ⊑c r2) (mp : m1 ≤m m2)
  (e : RoleMEcho r1 m1) →
  applyMode mp (applyRole rp e) ≡ applyRole rp (applyMode mp e)
choreo-mode-commute c⊑c linear≤linear e = refl
choreo-mode-commute c⊑c linear≤affine e = refl
choreo-mode-commute c⊑c affine≤affine e = refl
choreo-mode-commute c⊑s linear≤linear e = refl
choreo-mode-commute c⊑s linear≤affine e = refl
choreo-mode-commute c⊑s affine≤affine e = refl
choreo-mode-commute s⊑s linear≤linear e = refl
choreo-mode-commute s⊑s linear≤affine e = refl
choreo-mode-commute s⊑s affine≤affine e = refl

------------------------------------------------------------------------
-- The combined two-decoration action
------------------------------------------------------------------------

applyBoth :
  ∀ {r1 r2 m1 m2} →
  r1 ⊑c r2 → m1 ≤m m2 → RoleMEcho r1 m1 → RoleMEcho r2 m2
applyBoth rp mp e = applyMode mp (applyRole rp e)

applyBoth-via-other-order :
  ∀ {r1 r2 m1 m2}
  (rp : r1 ⊑c r2) (mp : m1 ≤m m2) (e : RoleMEcho r1 m1) →
  applyBoth rp mp e ≡ applyRole rp (applyMode mp e)
applyBoth-via-other-order rp mp e = choreo-mode-commute rp mp e

------------------------------------------------------------------------
-- EI-2 reporting (prose; the formal content is above)
--
-- This file's contribution to the EI-2 tracker:
--
-- DATA POINT 1 (this file): RoleMode = 1 non-trivial of 9.
--                            Same structural pattern as
--                            RoleGraded (1 non-trivial of 18).
--
-- INTERPRETATION:
--   The non-trivial cell is at (c⊑s, linear≤linear) — exactly the
--   (non-reflexive role transport, live second-axis cell) pattern.
--   The denominator (8 trivial cells) scales with the size of
--   Mode's order. The numerator (1 non-trivial cell) does NOT scale
--   with the second axis — it's tied to the choreographic Role's
--   single non-reflexive constructor (c⊑s).
--
--   This is partial evidence that the integration recipe produces
--   exactly one non-trivial cell per 2D combination involving Role,
--   and that non-trivial cell is provided by Role's own non-trivial
--   transport (c⊑s ↦ client-to-server). The second axis contributes
--   only triviality.
--
-- WHAT THIS DOES NOT YET ESTABLISH:
--   Whether the same pattern holds when neither axis is Role. The
--   next sibling construction (Mode × Grade) — both axes are
--   loss-style decorations, neither has a non-trivial transport like
--   client-to-server — will test whether the pattern is recipe-
--   structural or Role-specific.
--
--   Three structural possibilities:
--     A. Mode × Grade has 0 non-trivial cells → recipe collapses
--        when there's no choreographic axis. EI-2 falsifier: the
--        non-trivial content was always Role's, never the recipe's.
--     B. Mode × Grade has 1 non-trivial cell → recipe consistently
--        produces 1 non-trivial cell per pairing. Confirms the
--        pattern is recipe-structural.
--     C. Mode × Grade has 2+ non-trivial cells → loss-style pairs
--        carry richer integration content than choreographic-mixed
--        pairs. Would be a positive surprise.
--
--   Outcome A is the EI-2 falsifier. Outcome B is the most likely
--   structural result. Outcome C would be the strongest evidence
--   for the recipe.
--
-- STATUS: EI-2 not terminated. ModeGrade.agda is the next data
-- point.
------------------------------------------------------------------------
