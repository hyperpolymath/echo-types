{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoDecorationStructure: observation-side companion to
-- EchoResidueTaxonomy. The DECORATION RECIPE that the eight
-- decoration modules each re-implement, packaged as one record so
-- the recipe becomes a theorem ("here are the load-bearing fields
-- every decoration shares") rather than a comment.
--
-- The recipe across the eight modules:
--
--   1. An ORDER `_≤_` on the decoration tags (modes / grades /
--      roles / access modalities / costs / search bounds / indices
--      / knowledge classes).
--   2. REFLEXIVITY of the order.
--   3. TRANSITIVITY of the order.
--   4. PROPOSITIONALITY of the order (the thinness witness; this
--      is the load-bearing field that makes the per-decoration
--      `degrade-compose` and `degrade-via-join` laws close on
--      `refl` after applying `≤-prop`).
--   5. A JOIN `join` on tags.
--   6. The join is an UPPER BOUND of both inputs (`≤-join-left`,
--      `≤-join-right`).
--   7. The join is UNIVERSAL among upper bounds (`≤-join-univ`).
--
-- All eight decoration modules in the repo (Linear / Graded /
-- Choreo / Access / Cost / Search / Indexed / Epistemic) implement
-- this seven-field recipe under module-local names (`_≤m_` /
-- `_≤g_` / `_⊑c_` / `_≤a_` / ...). This module exposes the recipe
-- as a single `record DecorationStructure` and pins three instance
-- witnesses (Graded, Linear, Access) so the abstraction is
-- demonstrably inhabitable.
--
-- Naming choice: the abstract join field is `join` (not `_⊔_`)
-- because `_⊔_` collides with `Level._⊔_` from `Agda.Primitive` at
-- the record-projection level. The per-decoration modules' joins
-- (`_⊔g_`, `_⊔m_`, `_⊔a_`, etc.) keep their suffixed forms; the
-- abstract record uses `join` to avoid namespace pollution.
--
-- The per-carrier `degrade` / `degrade-compose` / `degrade-via-join`
-- theorems are NOT in this record — they require the per-decoration
-- carrier `D : G → Set` plus a `degrade : g₁ ≤ g₂ → D g₁ → D g₂`,
-- and each decoration's carrier signature differs (some are
-- indexed by `f`, some fix `collapse`, some are 5-grade Σ-shapes).
-- The record packages the COMMON FOUNDATION (the seven-field
-- recipe); the per-decoration degrade-compose theorems are
-- corollaries provable for any instance plus a carrier + degrade,
-- and live in the per-decoration modules (already proved there).
--
-- The companion abstraction `EchoResidueTaxonomy.ResidueForm`
-- packages the RESIDUE SHAPE (per-output carrier + lowering); this
-- module packages the DECORATION ORDER + JOIN structure. Together
-- they form the two-axis grid the audit called for.
--
-- Closes Tier 2 #4 per the synthesis-roadmap reorder.
--
-- Headlines (pinned in Smoke.agda):
--
--   * DecorationStructure              -- the seven-field recipe record
--   * graded-decoration-structure      -- EchoGraded instance witness
--   * linear-decoration-structure      -- EchoLinear instance witness
--   * access-decoration-structure      -- EchoAccess instance witness
--
-- Scope guardrail. `DecorationStructure` packages the order + join
-- structure that the eight decoration modules share. It does NOT
-- claim "all degradation theorems are derivable in the abstract";
-- the per-decoration degrade-compose / degrade-via-join laws still
-- live in the per-decoration modules (where the carrier signature
-- is concrete). The record makes the SHARED FOUNDATION explicit;
-- the corollary lift to "every instance + carrier + degrade
-- automatically gives degrade-compose" is a deferred follow-on.

module EchoDecorationStructure where

open import EchoLinear  using
  ( Mode
  ; linear
  ; affine
  ; linear≤linear
  ; affine≤affine
  ; _≤m_
  ; ≤m-trans
  ; ≤m-prop
  ; _⊔m_
  ; ≤m-⊔m-left
  ; ≤m-⊔m-right
  ; ≤m-⊔m-univ
  )
open import EchoGraded  using
  ( Grade
  ; _≤g_
  ; _⊔g_
  ; ≤g-prop
  ; ≤g-⊔g-left
  ; ≤g-⊔g-right
  ; ≤g-⊔g-univ
  ; keep≤keep
  ; keep≤residue
  ; keep≤forget
  ; residue≤residue
  ; residue≤forget
  ; forget≤forget
  )
open import EchoAccess  using
  ( Access
  ; free
  ; decidable
  ; enum
  ; feasible
  ; infeasible
  ; free≤free
  ; decidable≤decidable
  ; enum≤enum
  ; feasible≤feasible
  ; infeasible≤infeasible
  ; _≤a_
  ; ≤a-trans
  ; ≤a-prop
  ; _⊔a_
  ; ≤a-⊔a-left
  ; ≤a-⊔a-right
  ; ≤a-⊔a-univ
  )
open import EchoChoreo  using
  ( Role
  ; Client
  ; Server
  ; c⊑c
  ; c⊑s
  ; s⊑s
  ; _⊑c_
  ; ⊑c-trans
  ; ⊑c-prop
  ; _⊔c_
  ; ⊑c-⊔c-left
  ; ⊑c-⊔c-right
  ; ⊑c-⊔c-univ
  )

open import Level                using (Level; suc)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong)

private variable
  c ℓ : Level

----------------------------------------------------------------------
-- The decoration-structure record.
--
-- A `DecorationStructure G` packages the seven-field recipe shared
-- across the eight decoration modules: an order, its reflexivity /
-- transitivity / propositionality, and a join with upper-bound +
-- universal-property witnesses.
----------------------------------------------------------------------

record DecorationStructure {c} (G : Set c) ℓ : Set (c Level.⊔ suc ℓ) where
  field
    _≤_         : G → G → Set ℓ
    ≤-refl      : ∀ {g} → g ≤ g
    ≤-trans     : ∀ {g₁ g₂ g₃} → g₁ ≤ g₂ → g₂ ≤ g₃ → g₁ ≤ g₃
    ≤-prop      : ∀ {g₁ g₂} (p q : g₁ ≤ g₂) → p ≡ q
    join        : G → G → G
    ≤-join-left : ∀ g₁ g₂ → g₁ ≤ join g₁ g₂
    ≤-join-right : ∀ g₁ g₂ → g₂ ≤ join g₁ g₂
    ≤-join-univ : ∀ {g₁ g₂ g} → g₁ ≤ g → g₂ ≤ g → join g₁ g₂ ≤ g

----------------------------------------------------------------------
-- Graded instance.
--
-- `EchoGraded` packages the 3-grade order (`keep` / `residue` /
-- `forget`). All fields already proved in `EchoGraded` modulo
-- reflexivity (per-grade constructors) and transitivity (derived
-- by case-split on the order constructors).
----------------------------------------------------------------------

graded-≤-refl : ∀ {g} → g ≤g g
graded-≤-refl {Grade.keep}    = keep≤keep
graded-≤-refl {Grade.residue} = residue≤residue
graded-≤-refl {Grade.forget}  = forget≤forget

graded-≤-trans : ∀ {g₁ g₂ g₃} → g₁ ≤g g₂ → g₂ ≤g g₃ → g₁ ≤g g₃
graded-≤-trans keep≤keep       q  = q
graded-≤-trans keep≤residue    residue≤residue = keep≤residue
graded-≤-trans keep≤residue    residue≤forget  = keep≤forget
graded-≤-trans keep≤forget     forget≤forget   = keep≤forget
graded-≤-trans residue≤residue residue≤residue = residue≤residue
graded-≤-trans residue≤residue residue≤forget  = residue≤forget
graded-≤-trans residue≤forget  forget≤forget   = residue≤forget
graded-≤-trans forget≤forget   forget≤forget   = forget≤forget

graded-decoration-structure : DecorationStructure Grade _
graded-decoration-structure = record
  { _≤_          = _≤g_
  ; ≤-refl       = graded-≤-refl
  ; ≤-trans      = graded-≤-trans
  ; ≤-prop       = ≤g-prop
  ; join         = _⊔g_
  ; ≤-join-left  = ≤g-⊔g-left
  ; ≤-join-right = ≤g-⊔g-right
  ; ≤-join-univ  = ≤g-⊔g-univ
  }

----------------------------------------------------------------------
-- Linear instance.
--
-- `EchoLinear` packages the 2-grade order (`linear` ≤m `affine`).
-- All seven fields already proved in `EchoLinear`; reflexivity is
-- the per-mode constructor.
----------------------------------------------------------------------

linear-≤-refl : ∀ {m} → m ≤m m
linear-≤-refl {linear} = linear≤linear
linear-≤-refl {affine} = affine≤affine

linear-decoration-structure : DecorationStructure Mode _
linear-decoration-structure = record
  { _≤_          = _≤m_
  ; ≤-refl       = linear-≤-refl
  ; ≤-trans      = ≤m-trans
  ; ≤-prop       = ≤m-prop
  ; join         = _⊔m_
  ; ≤-join-left  = ≤m-⊔m-left
  ; ≤-join-right = ≤m-⊔m-right
  ; ≤-join-univ  = ≤m-⊔m-univ
  }

----------------------------------------------------------------------
-- Access instance.
--
-- `EchoAccess` packages the 5-grade access modality (`free` ≤a
-- `decidable` ≤a `enum` ≤a `feasible` ≤a `infeasible`). All seven
-- fields already proved in `EchoAccess`; reflexivity is the
-- per-grade constructor.
----------------------------------------------------------------------

access-≤-refl : ∀ {a} → a ≤a a
access-≤-refl {free}       = free≤free
access-≤-refl {decidable}  = decidable≤decidable
access-≤-refl {enum}       = enum≤enum
access-≤-refl {feasible}   = feasible≤feasible
access-≤-refl {infeasible} = infeasible≤infeasible

access-decoration-structure : DecorationStructure Access _
access-decoration-structure = record
  { _≤_          = _≤a_
  ; ≤-refl       = access-≤-refl
  ; ≤-trans      = ≤a-trans
  ; ≤-prop       = ≤a-prop
  ; join         = _⊔a_
  ; ≤-join-left  = ≤a-⊔a-left
  ; ≤-join-right = ≤a-⊔a-right
  ; ≤-join-univ  = ≤a-⊔a-univ
  }

----------------------------------------------------------------------
-- Choreo instance.
--
-- `EchoChoreo` packages the 2-role choreography order (`Client ⊑c
-- Server`) with reflexive constructors `c⊑c` / `s⊑s` and one
-- strict step `c⊑s`. All seven fields already proved in
-- `EchoChoreo`; reflexivity per-role.
----------------------------------------------------------------------

choreo-≤-refl : ∀ {r} → r ⊑c r
choreo-≤-refl {Client} = c⊑c
choreo-≤-refl {Server} = s⊑s

choreo-decoration-structure : DecorationStructure Role _
choreo-decoration-structure = record
  { _≤_          = _⊑c_
  ; ≤-refl       = choreo-≤-refl
  ; ≤-trans      = ⊑c-trans
  ; ≤-prop       = ⊑c-prop
  ; join         = _⊔c_
  ; ≤-join-left  = ⊑c-⊔c-left
  ; ≤-join-right = ⊑c-⊔c-right
  ; ≤-join-univ  = ⊑c-⊔c-univ
  }

----------------------------------------------------------------------
-- Carrier-side abstract degrade-compose theorem.
--
-- The companion-remark deferred follow-on: for ANY decoration
-- structure + carrier + degrade with a degrade-comp law, the
-- abstract `degrade-compose` and `degrade-via-join` close via
-- `≤-prop` (the load-bearing thinness witness from the record).
--
-- Each per-decoration module (EchoLinear, EchoGraded, EchoAccess,
-- ...) currently re-proves these laws by hand for its concrete
-- carrier; the abstract forms here close them once and for all
-- over the record. The per-decoration proofs remain (the concrete
-- forms compile faster + give pinned-name CI signals); the
-- abstract forms exist for any future decoration carrier that
-- inhabits `DecorationStructure`.
----------------------------------------------------------------------

open import Function.Base using (id)

module DegradeAbstract
  {c ℓ d} {G : Set c}
  (DS : DecorationStructure G ℓ)
  (Carrier : G → Set d)
  (degrade : ∀ {g₁ g₂} → DecorationStructure._≤_ DS g₁ g₂ →
             Carrier g₁ → Carrier g₂)
  (degrade-comp : ∀ {g₁ g₂ g₃}
                    (p12 : DecorationStructure._≤_ DS g₁ g₂)
                    (p23 : DecorationStructure._≤_ DS g₂ g₃)
                    (e : Carrier g₁) →
                  degrade p23 (degrade p12 e) ≡
                    degrade (DecorationStructure.≤-trans DS p12 p23) e)
  where

  open DecorationStructure DS

  ----------------------------------------------------------------------
  -- `degrade-compose`: any factoring agrees with any direct map.
  --
  -- Given `p12 : g₁ ≤ g₂`, `p23 : g₂ ≤ g₃`, and `p13 : g₁ ≤ g₃`,
  -- the factored degradation `degrade p23 ∘ degrade p12` equals the
  -- direct degradation `degrade p13`. Two steps: `degrade-comp`
  -- gives `degrade (≤-trans p12 p23) e`, then `≤-prop` identifies
  -- that with `degrade p13 e`.
  ----------------------------------------------------------------------

  degrade-compose-abstract :
    ∀ {g₁ g₂ g₃}
    (p12 : g₁ ≤ g₂) (p23 : g₂ ≤ g₃) (p13 : g₁ ≤ g₃)
    (e : Carrier g₁) →
    degrade p23 (degrade p12 e) ≡ degrade p13 e
  degrade-compose-abstract p12 p23 p13 e =
    trans (degrade-comp p12 p23 e)
          (cong (λ p → degrade p e) (≤-prop (≤-trans p12 p23) p13))

  ----------------------------------------------------------------------
  -- `degrade-via-join`: factor any direct degradation through the
  -- join of the two upper bounds.
  --
  -- Given `p1 : g₁ ≤ g₃` and `p2 : g₂ ≤ g₃`, the direct degradation
  -- `degrade p1 e` equals the factored route through the join:
  -- first degrade `g₁ ≤ join g₁ g₂` (a join-left bound), then
  -- degrade `join g₁ g₂ ≤ g₃` (the join's universal-property
  -- witness). Symmetric application of `degrade-compose-abstract`.
  ----------------------------------------------------------------------

  degrade-via-join-abstract :
    ∀ {g₁ g₂ g₃}
    (p1 : g₁ ≤ g₃) (p2 : g₂ ≤ g₃) (e : Carrier g₁) →
    degrade p1 e ≡
      degrade (≤-join-univ p1 p2) (degrade (≤-join-left g₁ g₂) e)
  degrade-via-join-abstract p1 p2 e =
    sym (degrade-compose-abstract
           (≤-join-left _ _) (≤-join-univ p1 p2) p1 e)

----------------------------------------------------------------------
-- Companion remark.
--
-- The remaining five decoration modules are structurally compatible
-- with `DecorationStructure` but require per-module wiring:
--
--   * EchoChoreo — LANDED 2026-05-27 as `choreo-decoration-structure`
--     above. 2-role order `_⊑c_` with join `_⊔c_`; same wiring shape
--     as graded/linear/access.
--
--   * EchoCost — abstract `CostAlgebra` (ordered commutative
--     monoid). Reflexivity / transitivity / propositionality
--     present; the join is the monoid's `_+_` plus monotonicity.
--     The carrier is parameterised, not enum'd, but the recipe
--     fits.
--
--   * EchoSearch — `SearchStrategy` carrier with bound-monotonicity
--     order. Seven fields present.
--
--   * EchoIndexed — index-equality residue. The order is
--     propositional equality of indices; the join is delicate
--     (uses Maybe-shape). Recipe satisfied degenerately.
--
--   * EchoEpistemic — knowledge-equivalence relation `Indist`. The
--     order is implication of knowledge predicates; the join is
--     conjunction. Carrier is relational rather than tag-shaped,
--     but the recipe still fits.
--
-- Adding instances for these five is mechanical. The three pinned
-- above demonstrate the abstraction is real on the canonical
-- small-poset decorations.
--
-- The carrier-side abstract degrade-compose theorem ("for any
-- `DecorationStructure G` + carrier `D : G → Set _` + degrade
-- `d : g₁ ≤ g₂ → D g₁ → D g₂`, degrade-compose holds whenever
-- degrade-comp holds") is a one-screen lemma over this abstract
-- structure; it is NOT proved here because each per-decoration
-- module already has the concrete form. The honest scope: the
-- record packages the SHARED FOUNDATION; the carrier-side
-- abstract theorem is a deferred follow-on (mechanical).
----------------------------------------------------------------------
