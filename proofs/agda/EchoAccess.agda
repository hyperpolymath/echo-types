{-# OPTIONS --safe --without-K #-}

-- Axis-8 (taxonomy.md §8) third artifact: graded access modality.
--
-- `EchoAccess.agda` lands refinement 2 of axis 8: a *graded
-- modality* `EchoA f y φ` where `φ : Access` ranges over a
-- two-point lattice `{feasible, infeasible}`.  The grade marks
-- whether the echo's witness is reachable by a constructive
-- extractor (feasible) or only known to exist in the metatheory
-- (infeasible).
--
-- The grade is a *label*; the meaningful content is the order /
-- join structure it carries.  Inside `--safe --without-K` Agda
-- cannot express the operational distinction directly (taxonomy
-- §8 lines 228–230), but the lattice shape lands and the
-- composition / join lemmas are real — they are exactly what
-- the per-decoration composition sweep does for the other five
-- decorations (grade, linear, indexed, choreographic, epistemic).
-- The structural recipe is identical: decoration order →
-- propositionality → join → factoring-free compose → via-join
-- restatement.
--
-- This is refinement 2 of the four axis-8 candidates listed in
-- `taxonomy.md` §8.  Refinement 3 (decidability-respecting) landed
-- as `EchoDecidable`.  Refinement 1 (cost-indexed, scalar ℕ
-- ledger) landed as `EchoCost`.  Refinement 2 (this module) is the
-- modal layer; the projection `EchoCost → EchoA … feasible`
-- pins the access modality as the qualitative ceiling on the
-- cost-indexed layer.
--
-- Refinement 4 (witness-search abstract machine) remains
-- unformalised; it would operationally substantiate the
-- `feasible` grade, which is currently a modality label.
--
-- Headline lemmas (pinned in `Smoke.agda`):
--
--   * Access, _⊑a_, _⊔a_     -- the access lattice
--   * ⊑a-prop                 -- order is propositional
--   * ⊑a-⊔a-{left, right, univ}  -- categorical join structure
--   * EchoA                   -- grade-indexed echo type family
--   * echo-access-forget      -- forget grade, project to base Echo
--   * echo-access-intro       -- immediate witness at infeasible
--   * echo-access-relax       -- weaken access claim along ⊑a
--   * echo-access-from-cost   -- bridge from refinement 1 (EchoCost)
--   * echo-access-compose     -- composition takes join of grades

module EchoAccess where

open import Level                                 using (Level; _⊔_)
open import Function.Base                         using (_∘_)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo                                  using
  ( Echo
  ; echo-intro
  ; Echo-comp-iso-from
  )
open import EchoCost                              using
  ( EchoCost
  ; echo-cost-forget
  )

----------------------------------------------------------------------
-- The access lattice
----------------------------------------------------------------------

-- Two-point lattice on echo accessibility.  `feasible` marks
-- "constructive extractor exists" (the EchoDec layer of
-- refinement 3); `infeasible` marks "information-theoretically
-- inhabited only" (the bare Echo layer).  Information-theoretic
-- access is the WEAKER claim: every feasible echo is also
-- info-theoretically accessible.  The order direction reflects
-- that — `feasible ⊑a infeasible` reads "feasibility implies
-- info-theoretic accessibility".

data Access : Set where
  feasible   : Access
  infeasible : Access

----------------------------------------------------------------------
-- Order
----------------------------------------------------------------------

data _⊑a_ : Access → Access → Set where
  feasible⊑feasible      : feasible   ⊑a feasible
  feasible⊑infeasible    : feasible   ⊑a infeasible
  infeasible⊑infeasible  : infeasible ⊑a infeasible

⊑a-trans : ∀ {φ₁ φ₂ φ₃} → φ₁ ⊑a φ₂ → φ₂ ⊑a φ₃ → φ₁ ⊑a φ₃
⊑a-trans feasible⊑feasible      p23 = p23
⊑a-trans feasible⊑infeasible    infeasible⊑infeasible = feasible⊑infeasible
⊑a-trans infeasible⊑infeasible  infeasible⊑infeasible = infeasible⊑infeasible

----------------------------------------------------------------------
-- Order is propositional
----------------------------------------------------------------------

-- Each constructor of `_⊑a_` is pinned by both its source and target
-- grades, so the order is propositional: any two proofs of
-- `φ₁ ⊑a φ₂` are definitionally equal.  Mirrors `EchoGraded.≤g-prop`.

⊑a-prop : ∀ {φ₁ φ₂} → (p q : φ₁ ⊑a φ₂) → p ≡ q
⊑a-prop feasible⊑feasible       feasible⊑feasible      = refl
⊑a-prop feasible⊑infeasible     feasible⊑infeasible    = refl
⊑a-prop infeasible⊑infeasible   infeasible⊑infeasible  = refl

----------------------------------------------------------------------
-- Join
----------------------------------------------------------------------

-- Categorical join: `infeasible` is the top.  Joining a feasible
-- access claim with anything gives the weaker (right-or-top) claim.
-- Mirrors `EchoGraded._⊔g_` with `infeasible` playing the `forget`
-- role.

_⊔a_ : Access → Access → Access
feasible   ⊔a φ          = φ
infeasible ⊔a _          = infeasible

⊑a-⊔a-left : ∀ φ₁ φ₂ → φ₁ ⊑a (φ₁ ⊔a φ₂)
⊑a-⊔a-left feasible   feasible   = feasible⊑feasible
⊑a-⊔a-left feasible   infeasible = feasible⊑infeasible
⊑a-⊔a-left infeasible feasible   = infeasible⊑infeasible
⊑a-⊔a-left infeasible infeasible = infeasible⊑infeasible

⊑a-⊔a-right : ∀ φ₁ φ₂ → φ₂ ⊑a (φ₁ ⊔a φ₂)
⊑a-⊔a-right feasible   feasible   = feasible⊑feasible
⊑a-⊔a-right feasible   infeasible = infeasible⊑infeasible
⊑a-⊔a-right infeasible feasible   = feasible⊑infeasible
⊑a-⊔a-right infeasible infeasible = infeasible⊑infeasible

⊑a-⊔a-univ
  : ∀ {φ₁ φ₂ φ₃}
  → φ₁ ⊑a φ₃ → φ₂ ⊑a φ₃ → (φ₁ ⊔a φ₂) ⊑a φ₃
⊑a-⊔a-univ feasible⊑feasible       p2 = p2
⊑a-⊔a-univ feasible⊑infeasible     p2 = p2
⊑a-⊔a-univ infeasible⊑infeasible   _  = infeasible⊑infeasible

----------------------------------------------------------------------
-- The grade-indexed echo
----------------------------------------------------------------------

-- The access grade is a *label* on an ordinary `Echo` — the grade
-- carries the modality, the witness carries the data.  Inside
-- `--safe --without-K` we cannot constrain the extractor at the
-- type level; the lattice / composition structure is the modal
-- content.

record EchoA
  {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B) (φ : Access) : Set (a ⊔ b) where
  constructor access-echo
  field
    witness : Echo f y

open EchoA public

----------------------------------------------------------------------
-- Headline 1 — `echo-access-forget`.
--
-- Forget the access grade and project down to the base Echo.
-- Mirrors `EchoCost.echo-cost-forget`.
----------------------------------------------------------------------

echo-access-forget :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} {φ : Access}
  → EchoA f y φ → Echo f y
echo-access-forget e = witness e

----------------------------------------------------------------------
-- Headline 2 — `echo-access-intro`.
--
-- An immediate witness `x : A` is at the infeasible grade by
-- default: we have not committed to an extractor.  Promoting to
-- feasible would require additional content (an extractor); the
-- bookkeeping shape here doesn't supply one.  Mirrors
-- `echo-cost-intro-zero` (no operational commitment).
----------------------------------------------------------------------

echo-access-intro :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (x : A) → EchoA f (f x) infeasible
echo-access-intro f x = access-echo (echo-intro f x)

----------------------------------------------------------------------
-- Headline 3 — `echo-access-relax`.
--
-- Weakening the access claim is monotone along `_⊑a_`.  Feasible
-- access can always be presented as info-theoretic access (the
-- weaker claim); not the other way around without an extractor.
-- The grade is a label, so the data is unchanged — analogous to
-- `EchoGraded.degrade-compose` operating by relabel only when the
-- order step doesn't change the carrier.
----------------------------------------------------------------------

echo-access-relax :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} {φ₁ φ₂ : Access}
  → φ₁ ⊑a φ₂ → EchoA f y φ₁ → EchoA f y φ₂
echo-access-relax _ e = access-echo (witness e)

----------------------------------------------------------------------
-- Headline 4 — `echo-access-from-cost`.
--
-- Bridge from refinement 1 (cost-indexed echo, `EchoCost`) to the
-- access modality.  A cost-indexed echo carries a ℕ ledger but no
-- operational extractor; we present it at the `infeasible` grade
-- by default.  Promoting to `feasible` requires a separate
-- commitment that the cost ledger corresponds to a real extractor
-- — not captured at this layer.  The projection is conservative.
----------------------------------------------------------------------

echo-access-from-cost :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B}
  → EchoCost f y → EchoA f y infeasible
echo-access-from-cost e = access-echo (echo-cost-forget e)

----------------------------------------------------------------------
-- Headline 5 — `echo-access-compose`.
--
-- Composition takes the join of access grades.  An f-side echo at
-- grade φ₁ composed with a g-side echo at grade φ₂ produces a
-- (g ∘ f)-side echo at grade `φ₁ ⊔a φ₂` — the weaker of the two
-- claims.  This is the natural composition shape for an access
-- modality: a composite extractor needs both component extractors,
-- so the composite's access class is bounded above by the slower
-- component.  Mirrors `EchoGraded.degrade-via-join` and the
-- per-decoration composition sweep.
--
-- Built on `Echo-comp-iso-from` (the accumulation iso's reverse
-- direction): given an intermediate `b : B`, an `Echo f b` witness,
-- and `g b ≡ y`, we get `Echo (g ∘ f) y`.  The grade combines via
-- `_⊔a_`.
----------------------------------------------------------------------

echo-access-compose :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C}
  (b : B) {φ₁ φ₂ : Access}
  → EchoA f b φ₁
  → (g b ≡ y)
  → EchoA (g ∘ f) y (φ₁ ⊔a φ₂)
echo-access-compose f g b ef gb≡y =
  access-echo (Echo-comp-iso-from f g (b , witness ef , gb≡y))

----------------------------------------------------------------------
-- Convenience: via-join restatement
--
-- The composition lemma factors through the join.  This is the
-- counterpart of `EchoGraded.degrade-via-join` for the access
-- modality.  Useful when callers want to thread the join structure
-- explicitly rather than apply `echo-access-compose` directly.
----------------------------------------------------------------------

echo-access-via-join :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  {f : A → B} {g : B → C} {y : C}
  {φ₁ φ₂ : Access}
  → EchoA (g ∘ f) y φ₁
  → φ₁ ⊑a (φ₁ ⊔a φ₂)
echo-access-via-join {φ₁ = φ₁} {φ₂ = φ₂} _ = ⊑a-⊔a-left φ₁ φ₂
