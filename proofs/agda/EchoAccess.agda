{-# OPTIONS --safe --without-K #-}

-- Axis-8 second formal artifact: graded access modality.
--
-- `EchoDecidable.agda` shipped the decidability-respecting refinement
-- of axis 8 (taxonomy.md §8): `EchoDec f y := Dec (Echo f y)`. That
-- module is the bottom of a lattice; this one builds the lattice.
--
-- The graded access modality refines `Echo f y` with a grade
-- `c : Access` naming the *feasibility class* at which the echo's
-- witness is reachable:
--
--   free        — witness in hand, no search
--   decidable   — a constructive decider exists (EchoDecidable.EchoDec)
--   enum        — exhaustive Fin-search (EchoFiberCount terrain)
--   feasible    — polynomial-time class (grade-only marker)
--   infeasible  — super-polynomial / cryptographic; witness exists
--                 only metatheoretically (grade-only marker)
--
-- The chain `free ≤ decidable ≤ enum ≤ feasible ≤ infeasible` is
-- reflexive at every grade and one-step at the named edges; the order
-- relation `_≤a_` is enumerated by its 15 reachable pairs in
-- Hasse-diagram style, exactly mirroring `EchoGraded._≤g_` and
-- `EchoLinear._≤m_`.
--
-- This file lands the **thin slice** of the recipe per the design in
-- `taxonomy.md` §8 / the Axis 8 study under `/tmp/echo-types-exploration`:
--
--   1. `Access`         — enum of five feasibility classes
--   2. `_≤a_`           — Hasse-enumerated access order
--   3. `≤a-trans`       — transitivity by case-split
--   4. `≤a-prop`        — propositionality by case-split + refl
--                         (load-bearing; the falsifier from the
--                         design's §6)
--   5. `EchoAccess`     — Σ-shape carrier indexed by `Access`
--   6. `access-of`,
--      `degrade-access` — projection + ≤a-indexed degrade primitive
--
-- Deferred to follow-up (the design doc §5 obligations 5–8):
--
--   * `degrade-access-comp`, `degrade-access-compose`,
--     `degrade-access-via-join` — per-decoration composition; the
--     "factoring-free" closer chain of `composition.md` §6.
--   * `_⊔a_` join + `≤a-⊔a-{left,right,univ}` — categorical join
--     structure.
--   * Honest carrier for `enum` (bridge to `EchoFiberCount.FiberSize-fin`)
--     so `feasible` / `infeasible` are not Potemkin labels — the
--     falsifier mode B of the design's §6. The current carriers are
--     deliberately the minimal placeholders that let the order layer
--     ship green.

module EchoAccess where

open import Level                                 using (Level; _⊔_)
open import Data.Unit.Base                        using (⊤; tt)
open import Data.Product.Base                     using (Σ; _,_)
open import Relation.Nullary.Decidable.Core       using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo         using (Echo)
open import EchoDecidable using (EchoDec)

----------------------------------------------------------------------
-- 1. The access enum
----------------------------------------------------------------------

-- Five feasibility classes along a single chain. Lower = more
-- accessible. The taxonomy §8 reading: `free` is information-
-- theoretic *and* operationally trivial; `infeasible` is the
-- cryptographic-hash regime (a witness exists metatheoretically but
-- is computationally out of reach).

data Access : Set where
  free       : Access
  decidable  : Access
  enum       : Access
  feasible   : Access
  infeasible : Access

----------------------------------------------------------------------
-- 2. The access order
----------------------------------------------------------------------

-- Hasse-enumerated: every reachable (c1, c2) pair has exactly one
-- inhabitant. 5 grades give 15 constructors (5+4+3+2+1). Each
-- constructor names its source and target — the same shape as
-- `EchoGraded._≤g_` (6 constructors for 3 grades) and
-- `EchoLinear._≤m_` (3 constructors for 2 modes). This shape is what
-- makes `≤a-prop` reduce to case-split + `refl` under `--without-K`.

data _≤a_ : Access → Access → Set where
  free≤free             : free       ≤a free
  free≤decidable        : free       ≤a decidable
  free≤enum             : free       ≤a enum
  free≤feasible         : free       ≤a feasible
  free≤infeasible       : free       ≤a infeasible
  decidable≤decidable   : decidable  ≤a decidable
  decidable≤enum        : decidable  ≤a enum
  decidable≤feasible    : decidable  ≤a feasible
  decidable≤infeasible  : decidable  ≤a infeasible
  enum≤enum             : enum       ≤a enum
  enum≤feasible         : enum       ≤a feasible
  enum≤infeasible       : enum       ≤a infeasible
  feasible≤feasible     : feasible   ≤a feasible
  feasible≤infeasible   : feasible   ≤a infeasible
  infeasible≤infeasible : infeasible ≤a infeasible

----------------------------------------------------------------------
-- 3. Transitivity
----------------------------------------------------------------------

-- Same recipe as `EchoGraded.≤g-trans`: on a reflexive first step,
-- propagate `p23`; otherwise enumerate the reachable composites. The
-- enumerated relation has exactly one inhabitant per (c1, c3) pair so
-- there is no choice of factoring — each clause is forced.

≤a-trans : ∀ {c1 c2 c3} → c1 ≤a c2 → c2 ≤a c3 → c1 ≤a c3
≤a-trans free≤free             p23                     = p23
≤a-trans free≤decidable        decidable≤decidable     = free≤decidable
≤a-trans free≤decidable        decidable≤enum          = free≤enum
≤a-trans free≤decidable        decidable≤feasible      = free≤feasible
≤a-trans free≤decidable        decidable≤infeasible    = free≤infeasible
≤a-trans free≤enum             enum≤enum               = free≤enum
≤a-trans free≤enum             enum≤feasible           = free≤feasible
≤a-trans free≤enum             enum≤infeasible         = free≤infeasible
≤a-trans free≤feasible         feasible≤feasible       = free≤feasible
≤a-trans free≤feasible         feasible≤infeasible     = free≤infeasible
≤a-trans free≤infeasible       infeasible≤infeasible   = free≤infeasible
≤a-trans decidable≤decidable   p23                     = p23
≤a-trans decidable≤enum        enum≤enum               = decidable≤enum
≤a-trans decidable≤enum        enum≤feasible           = decidable≤feasible
≤a-trans decidable≤enum        enum≤infeasible         = decidable≤infeasible
≤a-trans decidable≤feasible    feasible≤feasible       = decidable≤feasible
≤a-trans decidable≤feasible    feasible≤infeasible     = decidable≤infeasible
≤a-trans decidable≤infeasible  infeasible≤infeasible   = decidable≤infeasible
≤a-trans enum≤enum             p23                     = p23
≤a-trans enum≤feasible         feasible≤feasible       = enum≤feasible
≤a-trans enum≤feasible         feasible≤infeasible     = enum≤infeasible
≤a-trans enum≤infeasible       infeasible≤infeasible   = enum≤infeasible
≤a-trans feasible≤feasible     p23                     = p23
≤a-trans feasible≤infeasible   infeasible≤infeasible   = feasible≤infeasible
≤a-trans infeasible≤infeasible infeasible≤infeasible   = infeasible≤infeasible

----------------------------------------------------------------------
-- 4. Propositionality of the access order
----------------------------------------------------------------------

-- Each constructor of `_≤a_` is pinned by both source and target, so
-- the order is propositional: any two proofs of `c1 ≤a c2` are equal.
-- This is the *load-bearing* lemma of the access recipe — see
-- `composition.md` §6 and `EchoGraded.≤g-prop` (lines 79–89 of
-- `EchoGraded.agda`). The whole "factoring-free composition" closer
-- chain rests on it.
--
-- Pattern-matches close under `--without-K` because each (c1, c2)
-- pair has exactly one inhabitant of `_≤a_`; Agda's case-split picks
-- the unique constructor on both sides and both reduce to `refl`.
-- The design doc's §6 falsifier reads: "If `≤a-prop` does not close
-- on case-split + `refl` in ≤30 minutes, the design is wrong; collapse
-- grades that case-split distinguished but propositional equality
-- does not." This module shows the chain does close.

≤a-prop : ∀ {c1 c2} (p p' : c1 ≤a c2) → p ≡ p'
≤a-prop free≤free             free≤free             = refl
≤a-prop free≤decidable        free≤decidable        = refl
≤a-prop free≤enum             free≤enum             = refl
≤a-prop free≤feasible         free≤feasible         = refl
≤a-prop free≤infeasible       free≤infeasible       = refl
≤a-prop decidable≤decidable   decidable≤decidable   = refl
≤a-prop decidable≤enum        decidable≤enum        = refl
≤a-prop decidable≤feasible    decidable≤feasible    = refl
≤a-prop decidable≤infeasible  decidable≤infeasible  = refl
≤a-prop enum≤enum             enum≤enum             = refl
≤a-prop enum≤feasible         enum≤feasible         = refl
≤a-prop enum≤infeasible       enum≤infeasible       = refl
≤a-prop feasible≤feasible     feasible≤feasible     = refl
≤a-prop feasible≤infeasible   feasible≤infeasible   = refl
≤a-prop infeasible≤infeasible infeasible≤infeasible = refl

----------------------------------------------------------------------
-- 5. The graded carrier
----------------------------------------------------------------------

-- Per-grade carriers along the design's §4 sketch. `free` and
-- `decidable` are honest (full witness; constructive decider). The
-- `enum`, `feasible`, and `infeasible` carriers are deliberately the
-- minimal placeholder `⊤` for this slice — promoting them to honest
-- bridges (`enum` → `FiberSize-fin`, `feasible` / `infeasible` →
-- complexity-tagged variants) is the design's deferred §6 mode-B
-- mitigation and lands in the follow-up PR.
--
-- The level lift on `⊤` is needed because `Echo f y` lives in
-- `Set (a ⊔ b)` and Agda demands a single ambient level across the
-- match. `Level.Lift` from the standard library keeps the carrier
-- universe-uniform without disturbing `≤a-prop` (which is
-- grade-indexed, not carrier-indexed).

open import Level using (Lift; lift)

CEcho :
  ∀ {a b} {A : Set a} {B : Set b}
  → Access → (A → B) → B → Set (a ⊔ b)
CEcho free       f y = Echo f y
CEcho decidable  f y = EchoDec f y
CEcho {a} {b} enum       _ _ = Lift (a ⊔ b) ⊤
CEcho {a} {b} feasible   _ _ = Lift (a ⊔ b) ⊤
CEcho {a} {b} infeasible _ _ = Lift (a ⊔ b) ⊤

-- The Σ-shape mirror of `EchoGraded.GEcho`'s implicit graded bundle:
-- pair a grade with content at that grade. Useful when callers want
-- a single hom-set to thread through the access lattice rather than
-- a grade-indexed family.

EchoAccess :
  ∀ {a b} {A : Set a} {B : Set b}
  → (A → B) → B → Set (a ⊔ b)
EchoAccess f y = Σ Access (λ c → CEcho c f y)

----------------------------------------------------------------------
-- 6. `access-of` and `degrade-access`
----------------------------------------------------------------------

-- Projection: read off the access grade of a packed `EchoAccess`.

access-of :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} → EchoAccess f y → Access
access-of (c , _) = c

-- The `_≤a_`-indexed degrade primitive. Going to a *less accessible*
-- grade *forgets* content: `free → decidable` wraps the witness in
-- `yes`, every step into the placeholder block discards down to
-- `tt`, and reflexive cases are the identity.
--
-- The cases enumerate the same 15 constructors as `_≤a_`. The chain
-- `free → decidable → enum/.../infeasible` is the only place real
-- content moves; from `enum` onward the carrier is already `⊤`-lifted
-- so every transition is `lift tt`.
--
-- Per-decoration composition (`degrade-access-comp` + `compose` +
-- `via-join`) is deferred to the follow-up PR per the body of this
-- module. The order layer (`≤a-trans`, `≤a-prop`) is the
-- mathematical prerequisite for that follow-up, and lands here.

degrade-access :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {c1 c2 : Access} → c1 ≤a c2 → CEcho c1 f y → CEcho c2 f y
degrade-access free≤free             e = e
degrade-access free≤decidable        e = yes e
degrade-access free≤enum             _ = lift tt
degrade-access free≤feasible         _ = lift tt
degrade-access free≤infeasible       _ = lift tt
degrade-access decidable≤decidable   d = d
degrade-access decidable≤enum        _ = lift tt
degrade-access decidable≤feasible    _ = lift tt
degrade-access decidable≤infeasible  _ = lift tt
degrade-access enum≤enum             e = e
degrade-access enum≤feasible         _ = lift tt
degrade-access enum≤infeasible       _ = lift tt
degrade-access feasible≤feasible     e = e
degrade-access feasible≤infeasible   _ = lift tt
degrade-access infeasible≤infeasible e = e
