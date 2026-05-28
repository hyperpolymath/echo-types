{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

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
--   7. `_⊔a_`,
--      `≤a-⊔a-{left,right,univ}` — categorical join structure
--   8. `degrade-access-comp`,
--      `degrade-access-compose`,
--      `degrade-access-via-join` — per-decoration composition; the
--                          "factoring-free" closer chain of
--                          `composition.md` §6.
--
-- Sections 7–8 close the design doc's §5 obligations 5–8 and complete
-- the same recipe `EchoGraded` and `EchoLinear` close at the
-- per-decoration composition rung.
--
-- Carrier design (resolved 2026-05-20, owner decision):
--
--   The carriers for `enum` / `feasible` / `infeasible` remain the
--   minimal `Lift ⊤` placeholder — and this is the correct honest
--   answer, not a Potemkin label. Option (b) (existential carriers
--   burying an enumerator + decider) was tried and STRUCTURALLY FAILS:
--   `degrade-access : c1 ≤a c2 → CEcho c1 → CEcho c2` becomes
--   uninhabitable at multiple constructors because the access lattice
--   tracks DECREASING information as you climb (free → infeasible),
--   so degrading must DROP info, never fabricate it. There is no
--   way to construct an `Echo f y` witness when degrading from a
--   `Dec (Echo f y)` refutation, and no way to fabricate a `Dec B`
--   from a domain-side witness. The `Lift ⊤` shape at the top is
--   honest in the same sense that `EchoGraded.forget = ⊤` is honest:
--   at the loss-maximal grade, there is no extractable data to carry.
--   The grade-indexed composition layer (`degrade-access-comp`,
--   `_⊔a_`, the join-three) above this module operates on the grade,
--   not the carrier shape, and is sound under either design — so
--   this decision affects only the carrier reading, not any landed
--   theorem. See `docs/echo-types/decisions/echo-access-trivial-carrier.adoc`.
--
--   Option (a) (parameterise CEcho on Decidable B + enumerator) would
--   force every caller to supply machinery at the `free` grade where
--   it does nothing — explicitly rejected for that reason. Option (c)
--   (⊎-shape honest+placeholder) considered as a future affordance
--   if a real use-case for existential extraction emerges.

module EchoAccess where

open import Level                                 using (Level; _⊔_)
open import Data.Unit.Base                        using (⊤; tt)
open import Data.Product.Base                     using (Σ; _,_)
open import Relation.Nullary.Decidable.Core       using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

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
-- The per-decoration composition trio
-- (`degrade-access-comp` / `compose` / `via-join`) and the join
-- structure (`_⊔a_` + universal property) follow this section — the
-- order layer (`≤a-trans`, `≤a-prop`) is their mathematical
-- prerequisite.

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

----------------------------------------------------------------------
-- 7. The access join
----------------------------------------------------------------------

-- Componentwise max along the chain
-- `free ≤ decidable ≤ enum ≤ feasible ≤ infeasible`. `free` is bottom
-- (`free ⊔a c = c`); `infeasible` is top (`infeasible ⊔a _ = infeasible`).
-- Same shape as `EchoGraded._⊔g_` and `EchoLinear._⊔m_`, only widened
-- to five grades. Enumeration is forced once the bottom and top
-- absorbing cases are fixed.

_⊔a_ : Access → Access → Access
free       ⊔a c2         = c2
decidable  ⊔a free       = decidable
decidable  ⊔a decidable  = decidable
decidable  ⊔a enum       = enum
decidable  ⊔a feasible   = feasible
decidable  ⊔a infeasible = infeasible
enum       ⊔a free       = enum
enum       ⊔a decidable  = enum
enum       ⊔a enum       = enum
enum       ⊔a feasible   = feasible
enum       ⊔a infeasible = infeasible
feasible   ⊔a free       = feasible
feasible   ⊔a decidable  = feasible
feasible   ⊔a enum       = feasible
feasible   ⊔a feasible   = feasible
feasible   ⊔a infeasible = infeasible
infeasible ⊔a _          = infeasible

-- Join is an upper bound on its left summand. The proof enumerates
-- the 25 reachable `(c1, c2)` pairs; each picks out the unique
-- inhabitant of `_≤a_` from `c1` to `c1 ⊔a c2`. Mirrors
-- `EchoGraded.≤g-⊔g-left` and `EchoLinear.≤m-⊔m-left`.

≤a-⊔a-left : ∀ c1 c2 → c1 ≤a (c1 ⊔a c2)
≤a-⊔a-left free       free       = free≤free
≤a-⊔a-left free       decidable  = free≤decidable
≤a-⊔a-left free       enum       = free≤enum
≤a-⊔a-left free       feasible   = free≤feasible
≤a-⊔a-left free       infeasible = free≤infeasible
≤a-⊔a-left decidable  free       = decidable≤decidable
≤a-⊔a-left decidable  decidable  = decidable≤decidable
≤a-⊔a-left decidable  enum       = decidable≤enum
≤a-⊔a-left decidable  feasible   = decidable≤feasible
≤a-⊔a-left decidable  infeasible = decidable≤infeasible
≤a-⊔a-left enum       free       = enum≤enum
≤a-⊔a-left enum       decidable  = enum≤enum
≤a-⊔a-left enum       enum       = enum≤enum
≤a-⊔a-left enum       feasible   = enum≤feasible
≤a-⊔a-left enum       infeasible = enum≤infeasible
≤a-⊔a-left feasible   free       = feasible≤feasible
≤a-⊔a-left feasible   decidable  = feasible≤feasible
≤a-⊔a-left feasible   enum       = feasible≤feasible
≤a-⊔a-left feasible   feasible   = feasible≤feasible
≤a-⊔a-left feasible   infeasible = feasible≤infeasible
≤a-⊔a-left infeasible free       = infeasible≤infeasible
≤a-⊔a-left infeasible decidable  = infeasible≤infeasible
≤a-⊔a-left infeasible enum       = infeasible≤infeasible
≤a-⊔a-left infeasible feasible   = infeasible≤infeasible
≤a-⊔a-left infeasible infeasible = infeasible≤infeasible

-- Join is an upper bound on its right summand. Same shape.

≤a-⊔a-right : ∀ c1 c2 → c2 ≤a (c1 ⊔a c2)
≤a-⊔a-right free       free       = free≤free
≤a-⊔a-right free       decidable  = decidable≤decidable
≤a-⊔a-right free       enum       = enum≤enum
≤a-⊔a-right free       feasible   = feasible≤feasible
≤a-⊔a-right free       infeasible = infeasible≤infeasible
≤a-⊔a-right decidable  free       = free≤decidable
≤a-⊔a-right decidable  decidable  = decidable≤decidable
≤a-⊔a-right decidable  enum       = enum≤enum
≤a-⊔a-right decidable  feasible   = feasible≤feasible
≤a-⊔a-right decidable  infeasible = infeasible≤infeasible
≤a-⊔a-right enum       free       = free≤enum
≤a-⊔a-right enum       decidable  = decidable≤enum
≤a-⊔a-right enum       enum       = enum≤enum
≤a-⊔a-right enum       feasible   = feasible≤feasible
≤a-⊔a-right enum       infeasible = infeasible≤infeasible
≤a-⊔a-right feasible   free       = free≤feasible
≤a-⊔a-right feasible   decidable  = decidable≤feasible
≤a-⊔a-right feasible   enum       = enum≤feasible
≤a-⊔a-right feasible   feasible   = feasible≤feasible
≤a-⊔a-right feasible   infeasible = infeasible≤infeasible
≤a-⊔a-right infeasible free       = free≤infeasible
≤a-⊔a-right infeasible decidable  = decidable≤infeasible
≤a-⊔a-right infeasible enum       = enum≤infeasible
≤a-⊔a-right infeasible feasible   = feasible≤infeasible
≤a-⊔a-right infeasible infeasible = infeasible≤infeasible

-- Universal property of join: anything dominated by both `c1` and
-- `c2` is dominated by their join. Together with the two upper-bound
-- lemmas above this exhibits `_⊔a_` as the categorical join in
-- `_≤a_`. Same recipe as `EchoGraded.≤g-⊔g-univ` and
-- `EchoLinear.≤m-⊔m-univ`.
--
-- The pattern-match strategy: case-split on the first inequality `p1`
-- so the join `c1 ⊔a c2` reduces enough for Agda to see the
-- constructor needed in the result. Where `c1 = free`, the join is
-- `c2` and the result is just `p2`. For other rows, case-split on
-- `p2` and read off the unique inhabitant of `_≤a_` from
-- `(c1 ⊔a c2)` to the common upper bound.

≤a-⊔a-univ :
  ∀ {c1 c2 c} → c1 ≤a c → c2 ≤a c → (c1 ⊔a c2) ≤a c
≤a-⊔a-univ free≤free             p2 = p2
≤a-⊔a-univ free≤decidable        p2 = p2
≤a-⊔a-univ free≤enum             p2 = p2
≤a-⊔a-univ free≤feasible         p2 = p2
≤a-⊔a-univ free≤infeasible       p2 = p2
≤a-⊔a-univ decidable≤decidable   free≤decidable        = decidable≤decidable
≤a-⊔a-univ decidable≤decidable   decidable≤decidable   = decidable≤decidable
≤a-⊔a-univ decidable≤enum        free≤enum             = decidable≤enum
≤a-⊔a-univ decidable≤enum        decidable≤enum        = decidable≤enum
≤a-⊔a-univ decidable≤enum        enum≤enum             = enum≤enum
≤a-⊔a-univ decidable≤feasible    free≤feasible         = decidable≤feasible
≤a-⊔a-univ decidable≤feasible    decidable≤feasible    = decidable≤feasible
≤a-⊔a-univ decidable≤feasible    enum≤feasible         = enum≤feasible
≤a-⊔a-univ decidable≤feasible    feasible≤feasible     = feasible≤feasible
≤a-⊔a-univ decidable≤infeasible  free≤infeasible       = decidable≤infeasible
≤a-⊔a-univ decidable≤infeasible  decidable≤infeasible  = decidable≤infeasible
≤a-⊔a-univ decidable≤infeasible  enum≤infeasible       = enum≤infeasible
≤a-⊔a-univ decidable≤infeasible  feasible≤infeasible   = feasible≤infeasible
≤a-⊔a-univ decidable≤infeasible  infeasible≤infeasible = infeasible≤infeasible
≤a-⊔a-univ enum≤enum             free≤enum             = enum≤enum
≤a-⊔a-univ enum≤enum             decidable≤enum        = enum≤enum
≤a-⊔a-univ enum≤enum             enum≤enum             = enum≤enum
≤a-⊔a-univ enum≤feasible         free≤feasible         = enum≤feasible
≤a-⊔a-univ enum≤feasible         decidable≤feasible    = enum≤feasible
≤a-⊔a-univ enum≤feasible         enum≤feasible         = enum≤feasible
≤a-⊔a-univ enum≤feasible         feasible≤feasible     = feasible≤feasible
≤a-⊔a-univ enum≤infeasible       free≤infeasible       = enum≤infeasible
≤a-⊔a-univ enum≤infeasible       decidable≤infeasible  = enum≤infeasible
≤a-⊔a-univ enum≤infeasible       enum≤infeasible       = enum≤infeasible
≤a-⊔a-univ enum≤infeasible       feasible≤infeasible   = feasible≤infeasible
≤a-⊔a-univ enum≤infeasible       infeasible≤infeasible = infeasible≤infeasible
≤a-⊔a-univ feasible≤feasible     free≤feasible         = feasible≤feasible
≤a-⊔a-univ feasible≤feasible     decidable≤feasible    = feasible≤feasible
≤a-⊔a-univ feasible≤feasible     enum≤feasible         = feasible≤feasible
≤a-⊔a-univ feasible≤feasible     feasible≤feasible     = feasible≤feasible
≤a-⊔a-univ feasible≤infeasible   free≤infeasible       = feasible≤infeasible
≤a-⊔a-univ feasible≤infeasible   decidable≤infeasible  = feasible≤infeasible
≤a-⊔a-univ feasible≤infeasible   enum≤infeasible       = feasible≤infeasible
≤a-⊔a-univ feasible≤infeasible   feasible≤infeasible   = feasible≤infeasible
≤a-⊔a-univ feasible≤infeasible   infeasible≤infeasible = infeasible≤infeasible
≤a-⊔a-univ infeasible≤infeasible free≤infeasible       = infeasible≤infeasible
≤a-⊔a-univ infeasible≤infeasible decidable≤infeasible  = infeasible≤infeasible
≤a-⊔a-univ infeasible≤infeasible enum≤infeasible       = infeasible≤infeasible
≤a-⊔a-univ infeasible≤infeasible feasible≤infeasible   = infeasible≤infeasible
≤a-⊔a-univ infeasible≤infeasible infeasible≤infeasible = infeasible≤infeasible

----------------------------------------------------------------------
-- 8. Per-decoration composition
----------------------------------------------------------------------

-- The keystone lemma: two successive degrades along a factoring
-- `c1 ≤a c2 ≤a c3` agree with a single degrade along the composed
-- ordering proof. Mirrors `EchoGraded.degrade-comp` and
-- `EchoLinear.degradeMode-comp`. Closes `refl` on every reachable
-- `(p12, p23)` constructor pair: the carriers reduce definitionally
-- in lock-step with `≤a-trans`, so on both sides Agda lands on the
-- same canonical form.

degrade-access-comp :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {c1 c2 c3 : Access}
  (p12 : c1 ≤a c2)
  (p23 : c2 ≤a c3)
  (e : CEcho c1 f y) →
  degrade-access p23 (degrade-access p12 e)
  ≡ degrade-access (≤a-trans p12 p23) e
degrade-access-comp free≤free             p23                     e = refl
degrade-access-comp free≤decidable        decidable≤decidable     e = refl
degrade-access-comp free≤decidable        decidable≤enum          e = refl
degrade-access-comp free≤decidable        decidable≤feasible      e = refl
degrade-access-comp free≤decidable        decidable≤infeasible    e = refl
degrade-access-comp free≤enum             enum≤enum               e = refl
degrade-access-comp free≤enum             enum≤feasible           e = refl
degrade-access-comp free≤enum             enum≤infeasible         e = refl
degrade-access-comp free≤feasible         feasible≤feasible       e = refl
degrade-access-comp free≤feasible         feasible≤infeasible     e = refl
degrade-access-comp free≤infeasible       infeasible≤infeasible   e = refl
degrade-access-comp decidable≤decidable   p23                     e = refl
degrade-access-comp decidable≤enum        enum≤enum               e = refl
degrade-access-comp decidable≤enum        enum≤feasible           e = refl
degrade-access-comp decidable≤enum        enum≤infeasible         e = refl
degrade-access-comp decidable≤feasible    feasible≤feasible       e = refl
degrade-access-comp decidable≤feasible    feasible≤infeasible     e = refl
degrade-access-comp decidable≤infeasible  infeasible≤infeasible   e = refl
degrade-access-comp enum≤enum             p23                     e = refl
degrade-access-comp enum≤feasible         feasible≤feasible       e = refl
degrade-access-comp enum≤feasible         feasible≤infeasible     e = refl
degrade-access-comp enum≤infeasible       infeasible≤infeasible   e = refl
degrade-access-comp feasible≤feasible     p23                     e = refl
degrade-access-comp feasible≤infeasible   infeasible≤infeasible   e = refl
degrade-access-comp infeasible≤infeasible infeasible≤infeasible   e = refl

-- Factoring-free composition: any direct ordering proof
-- `p13 : c1 ≤a c3` agrees with the composed-via-`c2` degrade, because
-- `≤a-prop` makes the choice of factoring irrelevant. Mirrors
-- `EchoGraded.degrade-compose` and `EchoLinear.degradeMode-compose`.

degrade-access-compose :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {c1 c2 c3 : Access}
  (p12 : c1 ≤a c2)
  (p23 : c2 ≤a c3)
  (p13 : c1 ≤a c3)
  (e : CEcho c1 f y) →
  degrade-access p23 (degrade-access p12 e) ≡ degrade-access p13 e
degrade-access-compose p12 p23 p13 e
  rewrite ≤a-prop p13 (≤a-trans p12 p23) = degrade-access-comp p12 p23 e

-- Same composition law restated through the join structure: any
-- degrade to a common upper bound `c` factors through the `c1 ⊔a c2`
-- join. Mirrors `EchoGraded.degrade-via-join` and
-- `EchoLinear.degradeMode-via-join`.

degrade-access-via-join :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  {c1 c2 c : Access}
  (p1 : c1 ≤a c)
  (p2 : c2 ≤a c)
  (e : CEcho c1 f y) →
  degrade-access p1 e
  ≡ degrade-access (≤a-⊔a-univ p1 p2) (degrade-access (≤a-⊔a-left c1 c2) e)
degrade-access-via-join {c1 = c1} {c2 = c2} p1 p2 e =
  sym (degrade-access-compose (≤a-⊔a-left c1 c2) (≤a-⊔a-univ p1 p2) p1 e)
