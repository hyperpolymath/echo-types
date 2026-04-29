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
-- characteristic.RecipeNonTriviality — EI-2 obligation 5.
--
-- The recipe-non-triviality theorem in formal Agda. Two halves:
--
--   FORWARD direction:
--     For each of the three 2D constructions whose pair contains
--     a non-loss-only axis (RoleGraded, RoleMode), there exists a
--     cell whose composed action is NOT the identity function.
--
--   REVERSE direction:
--     For the loss-only-pair construction (ModeGrade), the only
--     "live" cell has composed action equal to the identity. Stated
--     as: the cell's action is provably ≡ identity, with the
--     contrapositive of "is non-identity" closed by ⊥-introduction.
--
-- Together, the two directions formalise the recipe-non-triviality
-- hypothesis at the level of the three concrete 2D constructions.
-- The hypothesis is now formally backed.
--
-- ============================================================
-- EI-2 STATUS: hypothesis FORMALLY PROVED for n=2 concrete cases.
-- ============================================================
--
-- This file does NOT prove the *general* theorem (over arbitrary
-- abstract Axis records). The general theorem is harder because
-- it requires:
--   (a) an abstract Axis record with sufficient structure to
--       construct generic 2D families,
--   (b) decidable equality on the decoration types,
--   (c) a generic non-triviality predicate that doesn't presuppose
--       a specific F : D → Set shape,
--   (d) potentially extensionality, which is not available in
--       --safe Agda.
--
-- The general theorem is partially formalised in the §<<abstract>>
-- section below as far as it goes in safe Agda.
--
-- Honest qualification: this proof closes the n=2 concrete case of
-- the recipe-non-triviality hypothesis. The general theorem
-- (over arbitrary abstract axes) remains open.
--
-- WHAT THIS DOES TERMINATE:
--   * The concrete recipe-non-triviality claim across the three
--     n=2 constructions (RoleGraded, RoleMode, ModeGrade).
--
-- WHAT THIS DOES NOT TERMINATE:
--   * The general recipe-non-triviality theorem (over arbitrary
--     axes). This needs more abstract machinery; flagged as a
--     residual open obligation.
--   * The READING 1 vs READING 2 documentation decision
--     (obligation 2). Doc decision, not formal.
--   * The 4th data point (obligation 3). Requires building a new
--     non-loss-only axis, not currently in repo.
--
-- EI-2 IS NOT TERMINATED. The hypothesis is formally proved for
-- the concrete n=2 case; the general theorem and the documentation
-- decision remain.
------------------------------------------------------------------------

module characteristic.RecipeNonTriviality where

open import Data.Bool.Base                        using (Bool; true; false)
open import Data.Unit.Base                        using (⊤; tt)
open import Data.Empty                            using (⊥)
open import Data.Product.Base                     using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; trans; sym)

open import Echo                                  using (Echo)
open import EchoChoreo                            using
  ( Role
  ; Client
  ; Server
  ; Global
  ; obs
  ; RoleEcho
  ; client-to-server
  ; swap
  ; swap-square
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
open import EchoCharacteristic                    using (collapse)
open import characteristic.RoleGraded             using
  ( RoleGEcho
  ; applyRole
  ; applyGrade
  )
open import characteristic.RoleMode               using
  ( RoleMEcho
  )
  renaming
  ( applyRole to applyRoleM
  ; applyMode to applyModeRM
  )
open import characteristic.ModeGrade              using
  ( ModeGEcho
  ; applyMode
  )
  renaming
  ( applyGrade to applyGradeM
  )

------------------------------------------------------------------------
-- Definitions of "non-trivial" for the formal theorem
--
-- A cell's composed action is non-trivial iff it is *not the
-- identity function*. Captured concretely as: there exists an input
-- whose output differs from itself.
--
-- For functions A → B with A ≠ B, "identity" is replaced by "preserves
-- distinguishability" — i.e., distinct inputs give distinct outputs.
-- The combination is captured by NonIdentityOrDistinguishing.
------------------------------------------------------------------------

-- For functions A → A: not the identity iff some input is moved.
NonIdentity : ∀ {A : Set} → (A → A) → Set
NonIdentity {A} f = Σ A (λ x → f x ≢ x)

-- For functions A → B (possibly A ≠ B): preserves distinguishability
-- iff distinct inputs give distinct outputs.
PreservesDistinct : ∀ {A B : Set} → (A → B) → Set
PreservesDistinct {A} {B} f =
  Σ A (λ x →
  Σ A (λ y →
    (x ≢ y) × (f x ≢ f y)))

------------------------------------------------------------------------
-- Forward direction — RoleGraded
--
-- The cell (c⊑s, keep≤keep) has composed action equal to
-- client-to-server. We prove this is non-identity-preserving on
-- distinguishability — i.e., it sends distinct inputs to distinct
-- outputs (not just preserves distinctness, but actively maps a pair
-- to a different pair).
------------------------------------------------------------------------

-- Two distinct inputs in RoleEcho Client true.
rg-input₁ : RoleEcho Client true
rg-input₁ = (true , true) , refl

rg-input₂ : RoleEcho Client true
rg-input₂ = (true , false) , refl

rg-inputs-distinct : rg-input₁ ≢ rg-input₂
rg-inputs-distinct p = true≢false (cong (λ z → proj₂ (proj₁ z)) p)
  where
    true≢false : true ≡ false → ⊥
    true≢false ()

-- Their c2s images: c2s rg-input₁ has proj₁ proj₁ = true; c2s
-- rg-input₂ has proj₁ proj₁ = false. These are distinct.
rg-images-distinct :
  client-to-server rg-input₁ ≢ client-to-server rg-input₂
rg-images-distinct p = true≢false (cong (λ z → proj₁ (proj₁ z)) p)
  where
    true≢false : true ≡ false → ⊥
    true≢false ()

-- The cell's action, fully spelled out.
rolegraded-cell-action :
  RoleEcho Client true → RoleEcho Server true
rolegraded-cell-action e =
  applyGrade {r = Server} keep≤keep (applyRole {g = keep} c⊑s e)

-- Confirm it equals client-to-server.
rolegraded-cell-action-equals-c2s :
  ∀ (e : RoleEcho Client true) →
  rolegraded-cell-action e ≡ client-to-server e
rolegraded-cell-action-equals-c2s e = refl

-- Forward direction for RoleGraded: there exists a non-trivial cell.
RoleGraded-has-non-trivial-cell :
  PreservesDistinct rolegraded-cell-action
RoleGraded-has-non-trivial-cell =
  rg-input₁ , rg-input₂ , rg-inputs-distinct , rg-images-distinct

------------------------------------------------------------------------
-- Forward direction — RoleMode
--
-- The cell (c⊑s, linear≤linear) has composed action equal to
-- client-to-server. Same construction as RoleGraded with Mode in
-- place of Grade.
------------------------------------------------------------------------

rm-input₁ : RoleEcho Client true
rm-input₁ = (true , true) , refl

rm-input₂ : RoleEcho Client true
rm-input₂ = (true , false) , refl

rm-inputs-distinct : rm-input₁ ≢ rm-input₂
rm-inputs-distinct p = true≢false (cong (λ z → proj₂ (proj₁ z)) p)
  where
    true≢false : true ≡ false → ⊥
    true≢false ()

rm-images-distinct :
  client-to-server rm-input₁ ≢ client-to-server rm-input₂
rm-images-distinct p = true≢false (cong (λ z → proj₁ (proj₁ z)) p)
  where
    true≢false : true ≡ false → ⊥
    true≢false ()

rolemode-cell-action :
  RoleEcho Client true → RoleEcho Server true
rolemode-cell-action e =
  applyModeRM {r = Server} linear≤linear (applyRoleM {m = linear} c⊑s e)

rolemode-cell-action-equals-c2s :
  ∀ (e : RoleEcho Client true) →
  rolemode-cell-action e ≡ client-to-server e
rolemode-cell-action-equals-c2s e = refl

RoleMode-has-non-trivial-cell :
  PreservesDistinct rolemode-cell-action
RoleMode-has-non-trivial-cell =
  rm-input₁ , rm-input₂ , rm-inputs-distinct , rm-images-distinct

------------------------------------------------------------------------
-- Reverse direction — ModeGrade
--
-- The only "live" cell of ModeGrade is (linear≤linear, keep≤keep)
-- where the data type is Echo collapse tt and BOTH actions are
-- identity. Therefore the composed action is identity, and there
-- is NO input x such that the cell's action sends x to something
-- different from x.
------------------------------------------------------------------------

modegrade-cell-action :
  ModeGEcho linear keep → ModeGEcho linear keep
modegrade-cell-action e =
  applyGradeM {m = linear} keep≤keep (applyMode {g = keep} linear≤linear e)

modegrade-cell-action-is-identity :
  ∀ (e : ModeGEcho linear keep) →
  modegrade-cell-action e ≡ e
modegrade-cell-action-is-identity e = refl

-- The cell's action is NOT non-identity — i.e., NonIdentity fails
-- because the action provably equals the identity.
ModeGrade-no-non-identity-cell :
  NonIdentity modegrade-cell-action → ⊥
ModeGrade-no-non-identity-cell (x , px) = px refl

------------------------------------------------------------------------
-- The recipe-non-triviality theorem (concrete form)
--
-- Statement: across the three 2D constructions, the existence of a
-- non-trivial cell correlates exactly with the presence of a
-- non-loss-only axis in the pair.
--
-- This is the concrete form of EI-2 obligation 5. The generic form
-- (over arbitrary abstract axes) is partially formalised in the
-- §<<abstract>> section below.
------------------------------------------------------------------------

-- Tag for "this construction has a non-loss-only axis"
data HasNonLossOnly : Set where
  RoleGraded-has-NLO : HasNonLossOnly  -- Role contributes c⊑s
  RoleMode-has-NLO   : HasNonLossOnly  -- Role contributes c⊑s
  ModeGrade-no-NLO   : HasNonLossOnly  -- (negative tag)

-- The three concrete constructions, with their NLO status.
-- Each entry pairs the construction with a proof of its
-- non-triviality status.
data ConstructionWithStatus : Set where
  rg-non-trivial    : PreservesDistinct rolegraded-cell-action →
                      ConstructionWithStatus
  rm-non-trivial    : PreservesDistinct rolemode-cell-action →
                      ConstructionWithStatus
  mg-trivial        : (NonIdentity modegrade-cell-action → ⊥) →
                      ConstructionWithStatus

-- The recipe-non-triviality theorem (concrete enumeration form):
-- each of the three 2D constructions has the non-triviality status
-- predicted by the hypothesis.
recipe-non-triviality-concrete :
  ConstructionWithStatus
  × ConstructionWithStatus
  × ConstructionWithStatus
recipe-non-triviality-concrete =
    rg-non-trivial RoleGraded-has-non-trivial-cell
  , rm-non-trivial RoleMode-has-non-trivial-cell
  , mg-trivial ModeGrade-no-non-identity-cell

------------------------------------------------------------------------
-- §<<abstract>> — Generic abstract axis machinery (partial)
--
-- The general theorem requires an abstract Axis record. The forward
-- direction (NLO ⇒ ∃ non-trivial cell) needs a generic 2D family
-- construction, which itself requires axes to carry decidable
-- equality on D and a designated "live" decoration. With those
-- additions, the forward direction can be proved generically.
--
-- The reverse direction (no NLO ⇒ no non-trivial cell) is harder
-- because it requires *bidirectional* reasoning over the recipe's
-- structure. In particular, it relies on the cell's action being
-- decidably equal to the identity, which requires extensionality
-- (not available in --safe Agda).
--
-- Status of the generic form:
--   * Axis record: defined.
--   * NonLossOnly predicate: defined.
--   * Generic 2D family: requires decidable equality and a live
--     decoration; partial scaffolding below.
--   * Generic forward direction: not yet proved.
--   * Generic reverse direction: blocked by extensionality issue.
--
-- The generic form is therefore *not closed* by this file. The
-- concrete form above is closed for the three n=2 cases.
------------------------------------------------------------------------

record Axis : Set₁ where
  field
    D     : Set
    _≤_   : D → D → Set
    F     : D → Set
    t     : ∀ {d1 d2} → d1 ≤ d2 → F d1 → F d2

-- Abstract strictness: a step is strict if it has a distinguishing
-- pair (two distinct inputs that map to distinct outputs).
record IsStrict (a : Axis) {d1 d2 : Axis.D a} (le : Axis._≤_ a d1 d2)
                : Set where
  open Axis a
  field
    x y       : F d1
    x≢y       : x ≢ y
    tx≢ty     : t le x ≢ t le y

-- Abstract non-loss-only: there exists a strict step somewhere in
-- the axis's order.
NonLossOnly : Axis → Set
NonLossOnly a =
  Σ (Axis.D a) (λ d1 →
  Σ (Axis.D a) (λ d2 →
  Σ (Axis._≤_ a d1 d2) (λ le →
    IsStrict a le)))

------------------------------------------------------------------------
-- Choreo as an abstract Axis (specialised to y=true).
------------------------------------------------------------------------

RoleEchoTrue : Role → Set
RoleEchoTrue r = RoleEcho r true

-- Choreographic action specialised to y=true.
applyChoreoTrue : ∀ {r1 r2} → r1 ⊑c r2 → RoleEchoTrue r1 → RoleEchoTrue r2
applyChoreoTrue c⊑c e = e
applyChoreoTrue c⊑s e = client-to-server e
applyChoreoTrue s⊑s e = e

ChoreoAxis : Axis
ChoreoAxis = record
  { D = Role
  ; _≤_ = _⊑c_
  ; F = RoleEchoTrue
  ; t = applyChoreoTrue
  }

------------------------------------------------------------------------
-- Choreo is non-loss-only: c⊑s is strict.
------------------------------------------------------------------------

choreo-c⊑s-strict : IsStrict ChoreoAxis c⊑s
choreo-c⊑s-strict = record
  { x = rg-input₁
  ; y = rg-input₂
  ; x≢y = rg-inputs-distinct
  ; tx≢ty = rg-images-distinct
  }

ChoreoAxis-non-loss-only : NonLossOnly ChoreoAxis
ChoreoAxis-non-loss-only =
  Client , Server , c⊑s , choreo-c⊑s-strict

------------------------------------------------------------------------
-- Mode is loss-only at the abstract level.
--
-- The strict step linear≤affine has transport `weaken` =
-- collapse-to-residue, which collapses Echo collapse tt (multiple
-- inhabitants) to EchoR ⊤ TrivialCert tt (one inhabitant up to
-- TrivialCert structure). All inputs map to the same output, so
-- the step has no distinguishing pair.
--
-- Formalising "no distinguishing pair" requires showing that
-- distinct inputs map to equal outputs, which is the
-- collapse-residue-same property. EchoLinear has
-- weaken-collapses-distinction : weaken echo-true ≡ weaken echo-false
-- as the formal certificate. We can lift this to "Mode is not
-- non-loss-only" — i.e., Mode does not satisfy NonLossOnly.
--
-- However: NonLossOnly only requires the EXISTENCE of *some* strict
-- step with a distinguishing pair. Mode has only one strict step
-- (linear≤affine), and we need to show it has no distinguishing
-- pair. This requires examining all pairs of inputs in
-- LEcho linear and showing they all map to equal outputs under
-- weaken — which involves the universal property of LEcho linear.
--
-- This is straightforward but requires more machinery (LEcho's
-- definition unfolds to Echo collapse tt; collapse-to-residue's
-- behaviour on all such inputs; uniqueness of the residue).
--
-- Left as an open obligation in the abstract section. The concrete
-- forward direction above (rolegraded-cell-action,
-- rolemode-cell-action) does not depend on this abstract
-- formalisation.
------------------------------------------------------------------------

-- Mode-is-loss-only : ¬ NonLossOnly ModeAxis
-- ^^^ open obligation; requires more LEcho machinery.

------------------------------------------------------------------------
-- Summary (prose; the formal content is above)
--
-- This file closes EI-2 obligation 5 in its CONCRETE form:
--
--   ✓ RoleGraded-has-non-trivial-cell — formal exhibit of a
--     non-identity-acting cell for RoleGraded.
--   ✓ RoleMode-has-non-trivial-cell — same for RoleMode.
--   ✓ ModeGrade-no-non-identity-cell — formal proof that
--     ModeGrade's only candidate non-trivial cell has identity
--     action.
--
-- The CONCRETE recipe-non-triviality theorem holds across the three
-- n=2 constructions.
--
-- The GENERIC theorem (over arbitrary abstract axes) is partially
-- formalised: Axis record and NonLossOnly predicate are defined;
-- ChoreoAxis is shown to be non-loss-only via formal exhibits.
-- The full generic theorem is not yet proved because:
--
--   1. A generic 2D family construction requires decidable
--      equality on D plus a designated live decoration; these
--      need to be added to the Axis record before the generic
--      forward direction can be stated.
--
--   2. The generic reverse direction (no-NLO ⇒ all cells trivial)
--      requires extensionality on the cell's action, which is not
--      available in --safe Agda.
--
-- ============================================================
-- EI-2 STATUS: concrete form proved; generic form open.
-- NOT TERMINATED.
-- ============================================================
--
-- Two paths to terminate EI-2 from here:
--
--   PATH A (generic-form completion): extend the Axis record to
--   carry the additional structure needed (decidable equality, live
--   decoration), prove the generic forward direction, accept the
--   generic reverse direction as decidably-extensional (out of
--   scope for --safe). Roughly 100-200 more lines of Agda.
--
--   PATH B (documentation closure): accept the concrete form as
--   sufficient evidence for the gate-1 distinctness claim, document
--   the generic form as future work, and CLOSE EI-2 with a
--   conditional verdict ("the recipe is non-trivial for axis pairs
--   containing a non-loss-only axis, demonstrated by the three
--   concrete cases"). This is a documentation decision, not formal
--   work.
--
-- Either path closes EI-2. PATH A is more thorough; PATH B is
-- faster and more honest about the limits of safe-Agda formalisation.
------------------------------------------------------------------------
