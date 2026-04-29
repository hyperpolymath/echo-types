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
-- characteristic.RecipeTheorem — EI-2 obligation 5 (partial).
--
-- Generic formalisation of the recipe-non-triviality hypothesis
-- introduced in EI2_REPORT.adoc:
--
--   The integration recipe produces non-trivial commutation content
--   iff at least one of the two axes has a non-trivial information-
--   preserving transport on at least one strict step.
--
-- Status: PARTIAL formalisation. Both directions of the iff are
-- proved as per-axis lemmas. The full 2D iff theorem is not
-- formalised because the 2D combination is not a single uniform
-- construction across the existing axes (each construction makes
-- pattern-match-on-data choices that don't lift to a generic
-- record framework).
--
-- What this file establishes:
--
--   1. RECIPE STRUCTURE: two record types, CarrierAxis and
--      CollapsingAxis, capturing the two structural shapes the
--      existing axes exhibit.
--
--   2. CarrierNLO: the formal property of "non-loss-only" on a
--      carrier axis.
--
--   3. THEOREM 1 (forward direction): NLO transports preserve
--      distinguishability when lifted into a 2D combination at the
--      live row d_B = top_B. This is what makes RoleGraded's
--      (c⊑s, keep≤keep) cell non-trivial — the role transport's
--      NLO survives the 2D embedding.
--
--   4. THEOREM 2 (backward direction): collapsing axes are loss-only
--      at every strict step — strict transports send everything to
--      the same value in the collapsed codomain. This is what
--      makes ModeGrade's commutation 0-non-trivial — neither axis's
--      strict steps can distinguish anything.
--
-- What this file does NOT establish:
--
--   The full 2D iff theorem. To state it generically would require
--   either (a) a uniform 2D combination construction lifting both
--   axes simultaneously, or (b) a per-cell injectivity criterion
--   that meta-quantifies over all cells of the commutation theorem.
--   Both paths require structure beyond what RecipeAxis bundles
--   (specifically, decidable equality and "F collapses to ⊤"
--   axioms that hold for the existing axes by construction but
--   need explicit fields generically).
--
--   Even with those fields added, the `with`-abstraction in
--   F12 d_A d_B = (if d_B = top_B then F_A d_A else ⊤) blocks
--   reduction in dependent positions, making proofs about specific
--   cells require manual rewriting that defeats the generic
--   intent.
--
--   The honest conclusion: the recipe-non-triviality hypothesis is
--   provable per-axis but not as a single 2D iff theorem in safe
--   Agda without postulates. The seven data points in EI2_REPORT
--   establish it as an empirical finding; the per-axis lemmas
--   below establish each direction structurally.
--
-- ============================================================
-- EI-2 STATUS after this file: NOT TERMINATED.
-- ============================================================
--
-- This file closes obligation 5 in its *partial* form: both
-- directions are proved per-axis, the full 2D iff is documented as
-- not formalisable in safe Agda without further structural axioms.
--
-- The remaining obligations:
--   * Obligation 2 (READING 1 vs READING 2 documentation decision):
--     still open. The partial theorem here informs the decision but
--     does not settle it.
--   * Obligation 3 (fourth data point with two NLO axes): still
--     unavailable from existing modules.
--
-- EI-2 termination requires either:
--   (a) Building a new non-loss-only axis to test the unobserved
--       2-NLO case (obligation 3).
--   (b) Making the documentation decision (obligation 2) and
--       writing it up as gate-1 weakening or recipe refinement.
--   (c) Strengthening this file's partial theorem to a full 2D iff
--       by adding the structural axioms (decidable equality + F-
--       collapses) and accepting the with-abstraction friction.
--
-- None of these is required for v0.1.1; all are open work.
------------------------------------------------------------------------

module characteristic.RecipeTheorem where

open import Data.Unit                             using (⊤; tt)
open import Data.Empty                            using (⊥; ⊥-elim)
open import Data.Product                          using (_×_; _,_; proj₁; proj₂)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

------------------------------------------------------------------------
-- Decidable equality, used by collapsing axes to distinguish the
-- live point from non-live points.
------------------------------------------------------------------------

DecEq : Set → Set
DecEq D = (d1 d2 : D) → (d1 ≡ d2) ⊎ (d1 ≡ d2 → ⊥)

------------------------------------------------------------------------
-- Carrier axis: F is "live" at every D-value.
--
-- The shape of Role in EchoChoreo: RoleEcho Client true and
-- RoleEcho Server true are both inhabited multi-element types.
--
-- A carrier axis can have a non-loss-only transport, where some
-- strict step preserves distinguishability between source values.
------------------------------------------------------------------------

record CarrierAxis : Set₁ where
  field
    D         : Set
    _≤_       : D → D → Set
    F         : D → Set
    t         : ∀ {d1 d2} → d1 ≤ d2 → F d1 → F d2
    refl-step : ∀ d → d ≤ d
    t-refl    : ∀ {d} (e : F d) → t (refl-step d) e ≡ e

------------------------------------------------------------------------
-- Collapsing axis: F is live only at one designated `top` point;
-- F d for d ≠ top contains essentially one inhabitant (collapses to
-- ⊤ semantically, witnessed by F-collapses).
--
-- The shape of Mode in EchoLinear (live at linear, ⊤ at affine) and
-- Grade in EchoGraded (live at keep, ⊤ at residue and forget).
--
-- A collapsing axis cannot be non-loss-only because all its strict
-- transports have collapsed codomains — see `collapsing-loss-only`
-- below.
------------------------------------------------------------------------

record CollapsingAxis : Set₁ where
  field
    D            : Set
    _≤_          : D → D → Set
    F            : D → Set
    t            : ∀ {d1 d2} → d1 ≤ d2 → F d1 → F d2
    refl-step    : ∀ d → d ≤ d
    t-refl       : ∀ {d} (e : F d) → t (refl-step d) e ≡ e
    top          : D
    decD         : DecEq D
    -- The collapse axiom: F d has at most one inhabitant for d ≠ top.
    F-collapses  : ∀ {d} → (d ≡ top → ⊥) → (e1 e2 : F d) → e1 ≡ e2

------------------------------------------------------------------------
-- The "non-loss-only" property on a carrier axis.
--
-- Witnessed by: a strict transport step plus two source values
-- whose images under the transport are distinct.
--
-- Choreo satisfies this via `client-to-server`. See
-- `ChoreoInjective.agda` for the concrete instance.
------------------------------------------------------------------------

record CarrierNLO (A : CarrierAxis) : Set where
  open CarrierAxis A
  field
    nlo-d1                 : D
    nlo-d2                 : D
    nlo-step               : nlo-d1 ≤ nlo-d2
    nlo-x1                 : F nlo-d1
    nlo-x2                 : F nlo-d1
    nlo-distinguish-source : nlo-x1 ≡ nlo-x2 → ⊥
    nlo-distinguish-image  : t nlo-step nlo-x1 ≡ t nlo-step nlo-x2 → ⊥

------------------------------------------------------------------------
-- THEOREM 1 (backward direction, simpler half).
--
-- Every collapsing axis is loss-only at its strict steps: any
-- transport into a non-top point sends all source values to the
-- same value.
--
-- This is the formal certificate for "Mode and Grade can never
-- contribute non-trivial content to the commutation theorem in the
-- 2D combination" — the fact behind ModeGrade's 0-of-18 result.
------------------------------------------------------------------------

collapsing-loss-only :
  ∀ (B : CollapsingAxis) →
  let open CollapsingAxis B in
  ∀ {d1 d2} (step : d1 ≤ d2) →
  (d2 ≡ top → ⊥) →
  (x1 x2 : F d1) →
  t step x1 ≡ t step x2
collapsing-loss-only B step d2≠top x1 x2 =
  CollapsingAxis.F-collapses B d2≠top _ _

------------------------------------------------------------------------
-- THEOREM 2 (forward direction, lifted NLO).
--
-- A CarrierAxis with NLO has a strict step whose transport
-- distinguishes between specific witness pairs. This property
-- *survives* embedding into a 2D combination at the live row
-- d_B = top_B, because at the live row the family is F_A d_A
-- unchanged.
--
-- The theorem statement is essentially a re-export of
-- `nlo-distinguish-image`, but it is the formal content the
-- non-trivial commutation cell relies on.
------------------------------------------------------------------------

carrier-NLO-distinguishes :
  ∀ {A : CarrierAxis} (nlo : CarrierNLO A) →
  let open CarrierAxis A; open CarrierNLO nlo
  in t nlo-step nlo-x1 ≡ t nlo-step nlo-x2 → ⊥
carrier-NLO-distinguishes nlo = CarrierNLO.nlo-distinguish-image nlo

------------------------------------------------------------------------
-- COROLLARY (combining the two theorems).
--
-- In a 2D combination of a CarrierAxis A with a CollapsingAxis B,
-- considering only the "live row" d_B = top_B (where the 2D family
-- F12 d_A top_B = F_A d_A):
--
--   * If A has NLO, the cell at (NLO-step in A, refl_top in B) is
--     non-trivial: A.t (NLO-step) sends nlo-x1 and nlo-x2 to
--     distinct values, and applyB at refl_top is identity.
--     The composite is A.t (NLO-step), which preserves
--     distinguishability.
--
--   * If A has no NLO, then no transport in A preserves
--     distinguishability. The composite is identity-on-data or
--     constant. No non-trivial cell.
--
--   * If B has no NLO (it's a CollapsingAxis, so by Theorem 1 it's
--     loss-only at strict steps), then any cell with strict step
--     in B reduces to ⊤ on the codomain side. No non-trivial cell
--     at strict-B-step cells.
--
-- This is the per-cell formal core of the recipe-non-triviality
-- hypothesis. The "non-trivial cell exists iff at least one axis
-- has NLO" iff theorem follows by combining these per-cell facts
-- with case analysis over the cells of the commutation theorem.
--
-- The full 2D theorem is not stated here because the 2D combination
-- is not a single uniform construction. See the file header for
-- the obstruction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A schematic statement of the conjectured full theorem.
--
-- This is a Set₁-level proposition. It is NOT proved here; it is
-- recorded as the formal target for future work (after building a
-- uniform 2D combination construction or accepting decidable
-- equality and collapse axioms across all axes).
------------------------------------------------------------------------

-- The conjectured iff is parameterised over a 2D combination
-- construction `Combine A B`, the actions on it, and a notion of
-- "non-trivial cell". For brevity, we sketch the type but do not
-- attempt to prove it.

-- Conjecture (not formalised):
--   For all A : CarrierAxis, B : CollapsingAxis (or vice versa),
--   the 2D commutation theorem on the natural Combine A B has at
--   least one non-trivial cell iff CarrierNLO A is inhabited.

------------------------------------------------------------------------
-- Concrete instances (informal).
--
-- The data points in EI2_REPORT.adoc instantiate the theorems as
-- follows:
--
--   * RoleGraded: A = Role (carrier), B = Grade (collapsing).
--     CarrierNLO Role is witnessed by `client-to-server` at step
--     c⊑s. Theorem 2 says the (c⊑s, *) row preserves
--     distinguishability at d_B = top_B = keep. This is the
--     non-trivial cell.
--
--   * RoleMode: A = Role (carrier), B = Mode (collapsing). Same
--     structure as RoleGraded. Non-trivial cell at (c⊑s,
--     linear≤linear).
--
--   * ModeGrade: A = Mode (collapsing), B = Grade (collapsing).
--     No CarrierNLO available (both are CollapsingAxis). By
--     Theorem 1 applied to both, all strict-step cells are
--     trivial. Reflexive cells are identity. 0 non-trivial cells.
--
-- The 3D RoleModeGrade pairwise commutations specialise the same
-- analysis.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Final note on EI-2 status.
--
-- This file establishes the per-axis content of the recipe-non-
-- triviality hypothesis in formal Agda. It does NOT establish the
-- full 2D iff theorem. The hypothesis is therefore:
--
--   * Empirically verified: seven data points (n=2 standalones, n=3
--     pairwise + triple) consistent with the hypothesis.
--   * Per-axis structurally certified: this file's Theorem 1 and
--     Theorem 2.
--   * Globally unproved: the 2D iff is conjectured but not
--     formalised.
--
-- EI-2 STATUS: not terminated. Obligation 5 is *partially* closed
-- by this file. Full closure of obligation 5 requires either
-- formalising the conjectured 2D iff (which has the structural
-- obstructions documented in the header) or declaring partial
-- closure acceptable and turning attention to obligations 2 and 3.
--
-- The recommendation is the former for technical completeness,
-- the latter for v0.1.1 release.
------------------------------------------------------------------------
