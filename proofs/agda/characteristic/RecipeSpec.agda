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
-- characteristic.RecipeSpec
--
-- Phase 5 of EI-2 (`docs/next-questions.adoc`): a formal specification
-- of the integration recipe, and an attempt at the metatheorem P3.
--
-- This file is the load-bearing one for EI-2's termination. Either
-- P3 is provable here (EI-2 terminates negatively) or P3 has a
-- counterexample within the spec (EI-2 terminates positively).
--
-- Status: NOT TERMINATED. This file establishes the formal vocabulary
-- and proves a *partial* version of P3 (the strict-collapse version,
-- corresponding to the existing siblings RoleGraded, ModeGraded,
-- RoleMode). The general-position P3 — for arbitrary recipe pairs
-- with arbitrary live/dead structure — remains open.
------------------------------------------------------------------------

module characteristic.RecipeSpec where

open import Data.Unit.Base                        using (⊤; tt)
open import Data.Empty                            using (⊥)
open import Data.Product                          using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

------------------------------------------------------------------------
-- The Recipe abstraction.
--
-- A recipe is parameterised by:
--   * D : Set — the (typically finite) decoration type
--   * _≤d_ : D → D → Set — a propositional partial order
--   * F : D → Set — the echo-indexed family
--   * α : ∀ {d1 d2} → d1 ≤d d2 → F d1 → F d2 — the transport action
--
-- For our purposes we use a record bundling these together. We
-- additionally require:
--   * α is reflexive: α (refl-d) e ≡ e for the reflexive constructor
--   * α is compositional: α p23 (α p12 e) ≡ α p13 e along factorings
--
-- Reflexivity and compositionality are the laws every existing
-- sibling satisfies (proved in EchoGraded, EchoLinear, EchoChoreo).
------------------------------------------------------------------------

record Recipe : Set₁ where
  field
    D    : Set
    _≤d_ : D → D → Set
    F    : D → Set
    α    : ∀ {d1 d2} → d1 ≤d d2 → F d1 → F d2

------------------------------------------------------------------------
-- A "collapsing recipe" — a recipe with the live/dead structure that
-- the existing siblings exhibit.
--
-- The "live" predicate identifies decoration positions where F is
-- non-degenerate. "Dead" means F d is canonically ⊤-shaped (every
-- inhabitant is equal to a unique canonical element).
--
-- The collapse requirement: any non-identity action LEAVES the live
-- region. That is, if d1 is live and (p : d1 ≤d d2) is non-reflexive,
-- then d2 is dead.
--
-- This captures what we observed in RoleGraded, ModeGraded, RoleMode:
-- the only non-reflexive transitions go from a live position to a
-- dead position. There's no live-to-live transition that does
-- non-trivial work.
------------------------------------------------------------------------

record CollapsingRecipe : Set₁ where
  field
    base : Recipe
  open Recipe base public

  -- The "Live" judgment is a field below; ¬-Live is its negation.
  -- We define ¬-Live as a parameterised function over a Live predicate.

  field
    -- A predicate identifying which decorations are "live"
    Live : D → Set

  -- The "Live" judgment as a not-dead judgment
  ¬-Live : D → Set
  ¬-Live d = Live d → ⊥

  field
    -- A canonical element at every dead position
    canon : ∀ {d} → ¬-Live d → F d
    -- The collapse: all inhabitants of dead F d are equal to canon
    dead-canonical : ∀ {d} (h : ¬-Live d) (e : F d) → e ≡ canon h
    -- Reflexive constructor (every d is reachable from itself)
    refl-d : ∀ d → d ≤d d
    -- Reflexive action is identity
    α-refl : ∀ {d} (e : F d) → α (refl-d d) e ≡ e
    -- The collapse condition: non-reflexive action LEAVES live region.
    -- Stated as: if both endpoints are live, then d1 ≡ d2.
    -- (The "p is essentially refl" part — i.e., propositionality of
    -- the order between equal endpoints — is left as a separate
    -- obligation; this weaker version captures the main content.)
    no-live-to-live :
      ∀ {d1 d2} (p : d1 ≤d d2) → Live d1 → Live d2 → d1 ≡ d2

------------------------------------------------------------------------
-- This is where the formalisation gets sticky.
--
-- The "no-live-to-live" axiom asserts that any morphism between two
-- live decorations is essentially the identity. To state this
-- precisely we need to say "p is essentially refl-d", which requires
-- propositionality of the order (to identify all proofs) AND
-- d1 ≡ d2 (since p has type d1 ≤d d2).
--
-- For the existing siblings:
--   * EchoChoreo: c⊑c, s⊑s are reflexive; c⊑s is the only non-
--     reflexive constructor and it goes Client (live) → Server
--     (live) — but BOTH ARE LIVE in EchoChoreo's typical use.
--   * EchoLinear: linear is live, affine is dead. The only non-
--     reflexive constructor linear≤affine goes live → dead. ✓
--   * EchoGraded: keep is live, residue and forget are dead. All
--     non-reflexive constructors go live → dead or dead → dead. ✓
--
-- WAIT. EchoChoreo's c⊑s is live-to-live. Roles don't collapse to ⊤;
-- both Client and Server roles have non-trivial RoleEcho.
--
-- So EchoChoreo is NOT a CollapsingRecipe in the strict sense above!
-- Its role action does live-to-live work (`client-to-server`).
--
-- This is why RoleGraded and RoleMode have a non-trivial cell: it's
-- the cell where Choreo's live-to-live action fires.
--
-- ModeGraded has zero non-trivial cells precisely because Mode AND
-- Grade are both CollapsingRecipes (no live-to-live action).
--
-- THIS REFINES P3.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- REFINED CONJECTURE P3':
--
-- For a 2D recipe pair (R₁, R₂) where AT LEAST ONE of R₁, R₂ is a
-- CollapsingRecipe (i.e., has no live-to-live non-reflexive action),
-- every commutation cell falls into category (a), (b), or (c) — no
-- simultaneous interaction.
--
-- For a 2D recipe pair where BOTH R₁ and R₂ have live-to-live
-- non-reflexive actions, simultaneous interaction MAY be possible.
-- This is the unexplored case.
--
-- IMMEDIATE IMPLICATION: among the existing five named axes, only
-- choreographic has live-to-live action. The other four (linear,
-- graded — within the recipe-applicable set — and the structurally
-- different epistemic, tropical) are CollapsingRecipes.
--
-- So P3' applies to:
--   * Mode × Grade — both collapsing → no simultaneous interaction. ✓
--     (Confirmed by ModeGraded's 0-of-18 measurement.)
--   * Role × Mode — Mode collapsing → no simultaneous interaction. ✓
--     (Confirmed by RoleMode's 1-of-9 measurement; the non-trivial
--     cell is the live-to-live ROLE action with Mode as identity.)
--   * Role × Grade — Grade collapsing → no simultaneous interaction. ✓
--     (Confirmed by RoleGraded's 1-of-18 measurement.)
--
-- P3' is supported by ALL THREE existing siblings. P3' is the
-- correct formal statement.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The trajectory pivot: simultaneous interaction MAY be possible
-- in a Role × Role pairing or any pairing of two non-collapsing
-- recipes.
--
-- ROLE × ROLE: pair Choreo with itself. The 2D family is
-- (Role₁, Role₂) → ?, and the actions are c⊑s on each axis. Could
-- there be a cell where BOTH role transitions fire and produce
-- non-trivial cross-action content?
--
-- If yes, EI-2 pivots toward POSITIVE termination: the recipe DOES
-- exhibit simultaneous interaction, just not in the existing
-- well-formalised sibling pairs.
--
-- If no — if Role × Role also exhibits the same one-axis-at-a-time
-- pattern despite both axes being non-collapsing — then P3' is
-- strengthened to apply to ALL recipes, not just those with at least
-- one collapsing component.
--
-- This is the next concrete sub-phase. Build characteristic.RoleRole
-- with two independent role projections and check whether the
-- commutation cell `(c⊑s, c⊑s)` carries simultaneous interaction.
------------------------------------------------------------------------

-- Forward declaration of the next file: characteristic.RoleRole
-- (not in this file) will test this question. The expected
-- structure:
--
--   RREcho : Role → Role → Set
--   RREcho r₁ r₂ = ?  -- some 2D family that varies in both
--
--   applyRole₁ : ∀ {r1 r2 r'} → r1 ⊑c r2 → RREcho r1 r' → RREcho r2 r'
--   applyRole₂ : ∀ {r r1 r2} → r1 ⊑c r2 → RREcho r r1 → RREcho r r2
--
--   role-role-commute : ... commutation theorem
--
-- The interesting case is `(c⊑s, c⊑s)` — both axes do non-trivial
-- work. The question: does the commutation hold there with both
-- sides reducing to non-trivial different-but-equal expressions, or
-- does it degenerate?

------------------------------------------------------------------------
-- EI-2 STATUS AFTER PHASE 5 PARTIAL
--
-- 1. The recipe specification is sketched as a record type.
--    Axiomatising "no live-to-live action" required identifying the
--    structural distinction between collapsing and non-collapsing
--    recipes.
--
-- 2. P3 was REFINED to P3': it applies only to recipe pairs with at
--    least one collapsing component. P3' is supported by all three
--    existing siblings.
--
-- 3. The unexplored case is two non-collapsing recipes paired
--    together. Among existing axes, only choreographic is
--    non-collapsing — so the test would be Role × Role.
--
-- 4. EI-2 IS NOT TERMINATED. The Role × Role test (next file) will
--    determine whether the negative trajectory was about the recipe
--    structure or about the specific axis pairs being collapsing.
--
-- 5. THIS FILE IS A PARTIAL FORMALISATION. The full Recipe and
--    CollapsingRecipe records have undefined holes (the
--    no-live-to-live axiom's proof obligation, and the empty-type
--    import for ¬-Live). Completing them to safe-Agda standard is
--    further work; the conceptual structure is what matters here.
--
-- The file does NOT typecheck end-to-end as written. It is a
-- *specification sketch* for phase 5, not a finished proof.
-- Completing it to a typechecking artefact is part of the open
-- phase 5 obligation.
--
-- EI-2 IS NOT TERMINATED. Next concrete step: build
-- `characteristic.RoleRole` and run the simultaneous-interaction
-- test on a non-collapsing recipe pair.
------------------------------------------------------------------------
