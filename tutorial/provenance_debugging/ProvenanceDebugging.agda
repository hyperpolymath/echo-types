{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

------------------------------------------------------------------------
-- Lane 5 Walkthrough 3: provenance / debugging echo.
--
-- ## HONEST BOUND DISCLOSURE (read this first)
--
-- This walkthrough is a *type-level* statement about which information
-- survives at which residue layer.  It is NOT a runtime debugger.  It
-- does NOT recover application state from a running process, a core
-- dump, or any operational artefact.  Conflating the residue
-- walk-through below with an operational debugger is the category
-- error this walkthrough exists to head off.
--
-- What is proved: for a small fixed 4-element `State` and a fixed
-- `firstSign : State → Bool`, the residue layer carrying the
-- `secondSign` of the source state is precisely enough information to
-- recover the full echo (a section exists), while the trivial residue
-- carrying no source information is precisely not enough (no section
-- exists).  The contrast is the pedagogy: the class-level information
-- captured at layer 1 is exactly the information needed to recover
-- the source within this 4-element world.
--
-- ## What this walkthrough does
--
-- 1. Defines a 4-element `State`, an opaque `firstSign : State → Bool`,
--    and a helper `secondSign : State → Bool` that distinguishes
--    within each `firstSign`-fibre.
-- 2. Exhibits two genuinely distinct echoes `echo-pp` and `echo-pn`
--    of the same visible output `firstSign s ≡ true`.
-- 3. Walks the source through three residue layers in order:
--      Layer 0 — `Echo firstSign true` (the full echo).
--      Layer 1 — `EchoR Bool ClassCert true` (carrying secondSign).
--      Layer 2 — `EchoR ⊤ TrivialCert' true` (carrying no source data).
-- 4. Headline (positive): `recover-from-class` is a section of the
--    layer-0 ↦ layer-1 lowering, with `recover-section-at-layer-1`
--    as the witness.  The class-level information is *exactly enough*
--    to reconstruct the source echo.
-- 5. Headline (negative): `no-recovery-from-trivial` rules out any
--    section of the layer-0 ↦ layer-2 lowering.  The two distinct
--    echoes collapse to the same layer-2 residue, so any candidate
--    section would have to equate them — which `states-distinct-at-true`
--    refutes.
-- 6. Pedagogical takeaway: the residue layer that carries `secondSign`
--    is the load-bearing one for this domain.  Strip it and recovery
--    becomes impossible; keep it and recovery is mechanical.
--
-- ## What this walkthrough deliberately does NOT prove
--
-- * Runtime / operational debugging.  Out of scope (engineering, not
--   type theory).  See HONEST BOUND DISCLOSURE above.
-- * Reconstruction across arbitrary source domains.  The 4-element
--   `State` is fixed; the section depends on the *injectivity of
--   secondSign within each firstSign-fibre*, which is a property of
--   this specific domain.  No analogous section exists when the
--   fibres are larger than the class carrier.
-- * Class-extraction completeness.  `secondSign` is one particular
--   choice of class; other class predicates would yield other layer-1
--   residues with their own recovery properties.  Nothing here speaks
--   to which class predicate is "the right one" for a given debugging
--   task.
-- * Adversarial recovery.  The section is a pure Agda function; no
--   claim is made about adversaries with access to additional side
--   information (timing, memory inspection, other echoes from the
--   same domain, etc.).
------------------------------------------------------------------------

module tutorial.provenance_debugging.ProvenanceDebugging where

open import Data.Bool.Base                       using (Bool; true; false)
open import Data.Empty                           using (⊥; ⊥-elim)
open import Data.Product.Base                    using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base                       using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary                     using (¬_)

open import Echo                                 using (Echo; echo-intro)
open import EchoResidue                          using
  ( EchoR
  ; echo-to-residue
  )

----------------------------------------------------------------------
-- Reusable B-side disequality (kept local to avoid coupling).
----------------------------------------------------------------------

true≢false : true ≢ false
true≢false ()

----------------------------------------------------------------------
-- Concrete domain: 4-element state, with two orthogonal sign bits
----------------------------------------------------------------------

data State : Set where
  pp pn np nn : State

-- Visible output (the "f" of the echo): the first sign bit.
-- Two states per Bool — the source of the fibre's non-singleton-ness.
firstSign : State → Bool
firstSign pp = true
firstSign pn = true
firstSign np = false
firstSign nn = false

-- The second sign bit.  Distinguishes within each firstSign-fibre,
-- and (crucially) it is *injective on each fibre*: among the two
-- states with `firstSign s ≡ true`, `secondSign` is `true` on `pp`
-- and `false` on `pn`.  That injectivity is what makes the layer-1
-- section possible.
secondSign : State → Bool
secondSign pp = true
secondSign pn = false
secondSign np = true
secondSign nn = false

----------------------------------------------------------------------
-- Layer 0: the full echo retains the state
----------------------------------------------------------------------

echo-pp : Echo firstSign true
echo-pp = echo-intro firstSign pp

echo-pn : Echo firstSign true
echo-pn = echo-intro firstSign pn

pp≢pn : pp ≢ pn
pp≢pn ()

-- States are distinct, therefore the echoes are distinct.  This is
-- the same shape as `echo-prov-true≢echo-prov-false` in
-- `EchoExampleProvenance.agda` — the projection on the Σ-first
-- component separates the two echoes.
states-distinct-at-true : echo-pp ≢ echo-pn
states-distinct-at-true eq = pp≢pn (cong proj-state eq)
  where
    proj-state : Echo firstSign true → State
    proj-state (s , _) = s

----------------------------------------------------------------------
-- Layer 1: residue cert carrying the second-sign class
----------------------------------------------------------------------

-- The cert relation at layer 1 is trivial — the carrier (a `Bool`)
-- already carries the class information.  We could refine `ClassCert`
-- to require `secondSign s ≡ c` at the cert, but `echo-to-residue`'s
-- soundness obligation already ensures this definitionally; we keep
-- the cert relation maximally permissive to mirror the existing
-- `TrivialCert` / `ProjCert` shape in the rest of the suite.
ClassCert : Bool → Bool → Set
ClassCert _ _ = ⊤

class-kappa : State → Bool
class-kappa = secondSign

class-sound : ∀ s → ClassCert (class-kappa s) (firstSign s)
class-sound _ = tt

state-to-class : ∀ {b} → Echo firstSign b → EchoR Bool ClassCert b
state-to-class {b} =
  echo-to-residue firstSign class-kappa ClassCert class-sound

-- The two layer-1 residues for our running echoes.  Computed
-- definitionally to (true , tt) and (false , tt) respectively;
-- their first components differ.
class-pp : EchoR Bool ClassCert true
class-pp = state-to-class echo-pp

class-pn : EchoR Bool ClassCert true
class-pn = state-to-class echo-pn

-- The class-level claim SURVIVES at layer 1: the two echoes remain
-- distinguishable as residues.  This is the load-bearing positive
-- observation of the walkthrough — the residue carrier carries the
-- secondSign of the source, and that is enough to keep them apart.
classes-remain-distinct : class-pp ≢ class-pn
classes-remain-distinct eq = true≢false (cong proj₁ eq)

----------------------------------------------------------------------
-- Layer 1 headline: a SECTION exists
----------------------------------------------------------------------

-- Within each firstSign-fibre, secondSign is injective: at
-- `firstSign s ≡ true`, the state is `pp` iff secondSign is true,
-- and `pn` iff secondSign is false.  So given the class residue
-- (and the visible value `true`), the source state is uniquely
-- determined.  We exhibit the section directly.
recover-from-class : EchoR Bool ClassCert true → Echo firstSign true
recover-from-class (true  , _) = pp , refl
recover-from-class (false , _) = pn , refl

-- The section property: `recover-from-class` is a right inverse of
-- `state-to-class` at the `b = true` fibre.  Proved by case-splitting
-- on the source state and the visible-value witness.
recover-section-at-layer-1 :
  ∀ (e : Echo firstSign true) → recover-from-class (state-to-class e) ≡ e
recover-section-at-layer-1 (pp , refl) = refl
recover-section-at-layer-1 (pn , refl) = refl
recover-section-at-layer-1 (np , ())
recover-section-at-layer-1 (nn , ())

-- Section package, mirroring the `Σ _ (λ reify → ∀ e → reify (lower e)
-- ≡ e)` shape that the layer-2 no-section refutes.  This is the
-- *positive* counterpart to `no-recovery-from-trivial` below: at
-- layer 1, the section exists; at layer 2, it does not.
recover-section-package :
  Σ (EchoR Bool ClassCert true → Echo firstSign true)
    (λ reify → ∀ e → reify (state-to-class e) ≡ e)
recover-section-package = recover-from-class , recover-section-at-layer-1

----------------------------------------------------------------------
-- Layer 2: trivial residue (no source information)
----------------------------------------------------------------------

TrivialCert' : ⊤ → Bool → Set
TrivialCert' _ _ = ⊤

triv-kappa : State → ⊤
triv-kappa _ = tt

triv-sound : ∀ s → TrivialCert' (triv-kappa s) (firstSign s)
triv-sound _ = tt

state-to-trivial : ∀ {b} → Echo firstSign b → EchoR ⊤ TrivialCert' b
state-to-trivial =
  echo-to-residue firstSign triv-kappa TrivialCert' triv-sound

triv-pp : EchoR ⊤ TrivialCert' true
triv-pp = state-to-trivial echo-pp

triv-pn : EchoR ⊤ TrivialCert' true
triv-pn = state-to-trivial echo-pn

-- The two layer-2 residues collapse to the same value: both are
-- (tt , tt).  This is what defeats any candidate section.
trivials-collapse : triv-pp ≡ triv-pn
trivials-collapse = refl

----------------------------------------------------------------------
-- Layer 2 headline: NO section exists
----------------------------------------------------------------------

-- The structural argument mirrors `EchoResidue.no-section-collapse-
-- to-residue`: two distinct source echoes collapse to the same
-- layer-2 residue, so a putative section would have to send the
-- shared residue to two different sources, contradicting
-- `states-distinct-at-true`.
no-recovery-from-trivial :
  ¬ (Σ (EchoR ⊤ TrivialCert' true → Echo firstSign true)
       (λ reify → ∀ e → reify (state-to-trivial e) ≡ e))
no-recovery-from-trivial (reify , sec) =
  states-distinct-at-true (trans (sym p-pp) p-pn')
  where
    p-pp : reify (state-to-trivial echo-pp) ≡ echo-pp
    p-pp = sec echo-pp

    p-pn : reify (state-to-trivial echo-pn) ≡ echo-pn
    p-pn = sec echo-pn

    p-pn' : reify (state-to-trivial echo-pp) ≡ echo-pn
    p-pn' = trans (cong reify trivials-collapse) p-pn

----------------------------------------------------------------------
-- Pedagogical takeaway, mechanised as a lemma pair
----------------------------------------------------------------------

-- The provenance walk in one statement: the layer-1 section exists
-- AND the layer-2 section does not.  This is the contrast the
-- walkthrough is built around — the class-level information
-- captured at layer 1 is exactly the load-bearing residue for
-- recovery in this domain.
provenance-walk-contrast :
  (Σ (EchoR Bool ClassCert true → Echo firstSign true)
     (λ reify → ∀ e → reify (state-to-class e) ≡ e))
  ×
  ¬ (Σ (EchoR ⊤ TrivialCert' true → Echo firstSign true)
       (λ reify → ∀ e → reify (state-to-trivial e) ≡ e))
provenance-walk-contrast =
  recover-section-package , no-recovery-from-trivial

----------------------------------------------------------------------
-- Matched-negative: what was NOT proved
----------------------------------------------------------------------

-- For each claim a sceptic might charitably read into the walkthrough,
-- a one-line marker that says "not proved here".  These are not
-- defined as `⊥`-shaped lemmas (that would be wrong — they are not
-- *refuted*, they are *out of scope*); they are postulate-free
-- markers documenting the type-level vs operational gap, mirroring
-- the discipline of Walkthrough 2's `NotProved-*` block.

NotProved-runtimeDebugger : Set
NotProved-runtimeDebugger = ⊤  -- type-level only; no operational debugger

NotProved-stateReconstructionInGeneral : Set
NotProved-stateReconstructionInGeneral = ⊤  -- 4-element State only

NotProved-completenessAcrossClasses : Set
NotProved-completenessAcrossClasses = ⊤  -- secondSign is one choice of class

NotProved-recoveryUnderSideInformation : Set
NotProved-recoveryUnderSideInformation = ⊤  -- pure-function recovery only
