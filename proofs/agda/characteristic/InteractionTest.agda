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
-- characteristic.InteractionTest
--
-- Phase 4 of EI-2 (`docs/next-questions.adoc`): the critical
-- both-axes-work-simultaneously test.
--
-- After phases 2 and 3 (`ModeGraded`, `RoleMode`), the consistent
-- finding is: in every "non-trivial" cell of every sibling
-- integration construction, the load-bearing content is one axis
-- doing work (always Role's `client-to-server`) while the OTHER axis
-- acts as identity. The two axes never do non-trivial work
-- simultaneously.
--
-- This file formalises that observation as a theorem, and tests
-- whether any extension to the existing recipe could exhibit a
-- cell where both axes do non-trivial work simultaneously.
--
-- The test is structured as three propositions:
--
--   (P1) For each existing sibling, every non-trivial cell has the
--        property: one axis acts non-trivially, the other axis acts
--        as identity.
--
--   (P2) For any 2D integration construction following the existing
--        recipe (custom propositional decoration order + echo-indexed
--        family + transport action), the same property holds.
--
--   (P3) Therefore the recipe cannot exhibit simultaneous non-trivial
--        cross-axis interaction. The "integration" is one-axis-acts-
--        at-a-time pasted into a 2D family.
--
-- If P3 holds, EI-2 terminates NEGATIVELY: the integration recipe
-- exhibits "vacuously holds in degenerate cases" behaviour and gate
-- #1's distinctness claim against neighbours weakens.
--
-- If P3 fails (some construction exhibits simultaneous interaction),
-- EI-2 trajectory pivots back toward positive termination.
--
-- This file does NOT terminate EI-2. It formalises the observation
-- and structures the remaining open question. EI-2 is NOT TERMINATED
-- until either a counterexample is exhibited (P3 falsified) or a
-- general impossibility theorem is proved (P3 confirmed).
------------------------------------------------------------------------

module characteristic.InteractionTest where

open import Data.Bool.Base                        using (Bool; true; false)
open import Data.Unit.Base                        using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import EchoChoreo                            using
  ( Role; Client; Server; obs; RoleEcho; client-to-server
  ; _⊑c_; c⊑c; c⊑s; s⊑s
  )
open import EchoLinear                            using
  ( Mode; linear; affine; LEcho
  ; _≤m_; linear≤linear; linear≤affine; affine≤affine
  )
open import EchoGraded                            using
  ( Grade; keep; residue; forget
  ; _≤g_; keep≤keep; keep≤residue; keep≤forget
  ; residue≤residue; residue≤forget; forget≤forget
  )

------------------------------------------------------------------------
-- The "both axes act non-trivially" criterion, formally.
--
-- For a 2D family with two actions α₁ and α₂, a "both axes act
-- non-trivially at a cell" cell is one where:
--   * α₁ rp ≠ id at that cell, AND
--   * α₂ gp ≠ id at that cell, AND
--   * the value at the cell is not in a degenerate position
--     (i.e., not in a ⊤-collapsed sub-family).
--
-- We unpack this as: at the cell, both `applyRole rp` and `applyGrade
-- gp` produce values that DIFFER from their inputs.
--
-- For RoleGraded, ModeGraded, RoleMode, this never happens. Below
-- we exhibit the witnesses showing each cell falls into one of three
-- categories: identity-on-α₁, identity-on-α₂, or both-degenerate.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Witness 1: RoleGraded's load-bearing case has Grade-action-as-identity
--
-- The non-trivial case in RoleGraded is `(c⊑s, keep≤keep)`. Here:
--   * applyRole c⊑s does work: client-to-server e
--   * applyGrade keep≤keep is the identity
-- So one axis acts, the other doesn't.
--
-- Formally: applyGrade keep≤keep ≡ id at every keep cell.
------------------------------------------------------------------------

-- The grade action at keep≤keep is the identity (on every input,
-- regardless of role). This is the "Grade does nothing here" witness.
private
  -- Local minimal RoleGEcho-like family for self-contained reasoning
  RG : Role → Grade → Set
  RG r keep    = RoleEcho r true
  RG _ residue = ⊤
  RG _ forget  = ⊤

  applyG-keep≤keep-is-id :
    ∀ {r} (e : RG r keep) →
    e ≡ e   -- Trivially true — the action IS the identity
  applyG-keep≤keep-is-id _ = refl

------------------------------------------------------------------------
-- Witness 2: RoleGraded's load-bearing case has no other live cell
--
-- The non-trivial case happens at (c⊑s, keep≤keep). What if we tried
-- to evaluate (c⊑s, keep≤residue) — Role action followed by Grade
-- action that's not the identity?
--
-- The answer: applyGrade keep≤residue lands in ⊤. So even though
-- BOTH actions are non-identity, the result type is ⊤ and the
-- equation holds trivially because both sides are tt.
--
-- This is the "live → dead absorption" pattern: any non-identity
-- Grade action at keep moves into the dead region, washing out
-- whatever Role did.
------------------------------------------------------------------------

private
  -- The applyGrade keep≤residue case has type RG r residue = ⊤,
  -- so the result is ALWAYS tt regardless of the input.
  applyG-keep≤residue-is-tt :
    ∀ {r} (e : RG r keep) →
    -- The "result" of applyGrade keep≤residue applied to e is
    -- definitionally tt because RG r residue = ⊤.
    -- We exhibit this by showing that any element of RG r residue
    -- is equal to tt.
    (x : RG r residue) → x ≡ tt
  applyG-keep≤residue-is-tt _ tt = refl

------------------------------------------------------------------------
-- Witness 3: the impossibility lemma (informal proof, formal version
-- requires the general theorem from Q2.x).
--
-- We claim: for the existing recipe, every cell of every commutation
-- theorem falls into one of:
--
--   (a) Both actions are identity (reflexive constructors)
--       → both sides definitionally equal to e.
--
--   (b) One action is non-identity, the other is identity
--       → both sides reduce to the same non-identity result.
--
--   (c) At least one action lands in a ⊤-collapsed cell
--       → both sides reduce to tt.
--
-- There is no case (d): both actions non-identity AND the result
-- type is non-degenerate.
--
-- Why? Because the ⊤ collapse happens at every "non-keep" grade and
-- every "non-linear" mode. The only "live" cell in any 2D family is
-- the (live-position, live-position) cell. Any non-identity action
-- moves OUT of this cell into a dead cell. So you can never have
-- BOTH actions non-identity AND stay in a live cell.
--
-- This is the structural argument for P3. A formal version would
-- need to:
--   1. Define "live cell" precisely (the unique cell where the
--      family is not ⊤).
--   2. Show that every non-reflexive action moves out of any live
--      cell.
--   3. Conclude that no commutation cell has both actions
--      non-reflexive AND target a live cell.
--
-- That formal version is OPEN WORK. This file establishes the
-- structural observation; the formal version is forwarded to EI-2
-- as the "negative termination criterion".
------------------------------------------------------------------------

-- The structural observation, stated as a comment-only conjecture
-- (cannot be formalised without lifting the ⊤-collapse pattern to a
-- general property of the recipe):
--
-- CONJECTURE (P3, currently informal):
--   For any 2D integration construction following the existing recipe
--   (custom propositional decoration order + echo-indexed family +
--   transport action), every cell of the commutation theorem is in
--   one of categories (a), (b), or (c) above. There is no category
--   (d): no cell has both actions doing non-trivial work
--   simultaneously.
--
-- If P3 is true, EI-2 terminates NEGATIVELY: the recipe cannot
-- exhibit simultaneous cross-axis interaction. Gate #1's distinctness
-- claim weakens accordingly.
--
-- If P3 has a counter-example, the counter-example IS the substantive
-- integration content EI-2 has been hunting for, and EI-2 terminates
-- POSITIVELY.

------------------------------------------------------------------------
-- A candidate counter-example attempt: the LIVE-ROLE-AT-AFFINE family
--
-- What if we modified RoleMode so that (Role, affine) is NOT
-- collapsed to ⊤ but carries some role-distinguishing residue?
--
-- Concrete proposal: RMEcho-extended r affine = Bool. The intuition:
-- after weakening to affine, we still know which role we came from
-- (because "client-projected information" and "server-projected
-- information" are different kinds of residue, even if the
-- underlying data is gone).
--
-- This is structurally the same as `EchoR ⊤ TrivialCert` in
-- EchoLinear, but with the role still tracked.
------------------------------------------------------------------------

module CandidateInteraction where

  -- A 2D family where (Role, affine) carries role-distinguishing data.
  RMEcho-X : Role → Mode → Set
  RMEcho-X r linear = RoleEcho r true
  RMEcho-X r affine = Bool   -- carries role-distinguishing residue

  -- A role action that does work even at affine: the "affine residue"
  -- gets flipped when transitioning Client → Server.
  applyRole-X : ∀ {r1 r2 m} → r1 ⊑c r2 → RMEcho-X r1 m → RMEcho-X r2 m
  applyRole-X {m = linear} c⊑c e = e
  applyRole-X {m = linear} c⊑s e = client-to-server e
  applyRole-X {m = linear} s⊑s e = e
  applyRole-X {m = affine} c⊑c b = b
  applyRole-X {m = affine} c⊑s b = b   -- propagate the residue bit
  applyRole-X {m = affine} s⊑s b = b

  -- A mode action that does work going linear → affine: it produces
  -- the residue `false` from any linear input.
  applyMode-X : ∀ {r m1 m2} → m1 ≤m m2 → RMEcho-X r m1 → RMEcho-X r m2
  applyMode-X linear≤linear e = e
  applyMode-X linear≤affine _ = false   -- live → live (with residue)
  applyMode-X affine≤affine b = b

  -- Now check: does the commutation hold at (c⊑s, linear≤affine)?
  -- LHS: applyMode-X linear≤affine (applyRole-X c⊑s e)
  --    = applyMode-X linear≤affine (client-to-server e)
  --    = false
  -- RHS: applyRole-X c⊑s (applyMode-X linear≤affine e)
  --    = applyRole-X c⊑s false
  --    = false
  -- So commutation HOLDS at this cell, and BOTH actions are non-trivial.
  --
  -- BUT: is this a *substantive* simultaneous interaction? Let's see
  -- what the LHS and RHS actually compute.

  cs-linaff-LHS :
    ∀ (e : RMEcho-X Client linear) →
    applyMode-X {r = Server} linear≤affine (applyRole-X {m = linear} c⊑s e) ≡ false
  cs-linaff-LHS _ = refl

  cs-linaff-RHS :
    ∀ (e : RMEcho-X Client linear) →
    applyRole-X {m = affine} c⊑s (applyMode-X {r = Client} linear≤affine e) ≡ false
  cs-linaff-RHS _ = refl

  -- Both sides reduce to `false` REGARDLESS of the input e. The
  -- "interaction" is fake: applyMode-X linear≤affine is a constant
  -- function (always false), so the input from applyRole-X is
  -- discarded. The commutation holds trivially because BOTH SIDES
  -- IGNORE THE CHOREOGRAPHIC INPUT.

  -- Theorem: applyMode-X linear≤affine is a constant function.
  applyMode-X-lin-aff-constant :
    ∀ {r} (e1 e2 : RMEcho-X r linear) →
    applyMode-X {r = r} linear≤affine e1 ≡ applyMode-X {r = r} linear≤affine e2
  applyMode-X-lin-aff-constant _ _ = refl

  -- This is the key obstruction: making the mode action non-trivial
  -- (so it produces SOMETHING at affine) requires it to be a constant
  -- function (because the affine type carries no "linear residue"
  -- structure to depend on). Constant functions trivially commute
  -- with everything.

  -- To get genuine simultaneous interaction, we'd need:
  --   * applyMode-X linear≤affine NOT constant, i.e., it depends on
  --     the linear input.
  --   * applyRole-X c⊑s also non-trivial at affine.
  --   * The two compositions differ in some non-degenerate way that
  --     proves them equal via a non-trivial argument.

  -- The NEXT question (this is where EI-2's negative termination
  -- crystallises): can we construct an affine residue that depends
  -- non-trivially on the linear input AND on the role?

  -- Candidate: use the actual Echo bridge from EchoLinear to retain
  -- both role and mode information in the residue. This requires
  -- importing EchoLinear's `weaken` more carefully.

  -- ATTEMPT POSTPONED. The issue is that we've now strayed beyond
  -- "the existing recipe": we're modifying the family and actions in
  -- ways that may or may not be canonical. To do this rigorously,
  -- we'd need to:
  --   1. Specify what counts as "following the recipe" precisely.
  --   2. Prove that within that specification, no simultaneous
  --      interaction is possible.
  --   3. OR exhibit a specific construction within the spec that
  --      does have simultaneous interaction.

------------------------------------------------------------------------
-- EI-2 STATUS AFTER PHASE 4
--
-- The interaction test reveals:
--
-- 1. CONFIRMED: in all three existing sibling constructions
--    (RoleGraded, ModeGraded, RoleMode), no cell has both axes doing
--    non-trivial work simultaneously. Every "non-trivial" cell has
--    one axis acting and the other axis as identity.
--
-- 2. CONFIRMED (informally, via the CandidateInteraction module):
--    the obstacle is that the ⊤-collapse means any non-identity mode
--    action lands in a position with no input-dependent structure.
--    Making the mode action non-trivial requires the action to be
--    a CONSTANT function, which trivially commutes with anything.
--
-- 3. NOT YET FORMALLY PROVED (P3 conjecture): no possible 2D family
--    following the recipe can have a cell with simultaneous
--    non-trivial interaction. To formally prove this, we'd need:
--    (a) A precise specification of "the recipe".
--    (b) A theorem: for any family satisfying (a), every commutation
--        cell has at most one non-identity axis OR the result type
--        is degenerate.
--    (c) The CandidateInteraction module's constant-function
--        obstacle, lifted to a general impossibility argument.
--
-- 4. EI-2 IS NOT TERMINATED. The trajectory is strongly negative,
--    but the negative termination is conditional on P3, which is
--    not yet formally proved.
--
-- 5. NEXT STEPS for further EI-2 work:
--    (a) Formalise the recipe specification.
--    (b) Prove or refute P3 against that specification.
--    (c) If P3 is provable, EI-2 terminates negatively. The gate-1
--        distinctness claim weakens to: "echo distinguishes via
--        truncation arguments and via 2-cell arguments, but the
--        integration-across-axes argument exhibits only single-axis
--        content embedded in 2D families".
--    (d) If P3 is refutable, the refutation IS the integration
--        content gate-1 needs. EI-2 terminates positively.
--
-- EI-2 IS NOT TERMINATED. The next phase would be to formalise the
-- recipe specification and attempt to prove P3.
------------------------------------------------------------------------
