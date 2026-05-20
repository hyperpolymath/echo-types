{-# OPTIONS --safe --without-K #-}

-- Axis-8 (taxonomy.md §8) fourth artifact: witness-search abstract
-- machine.
--
-- `EchoSearch.agda` lands refinement 4 of axis 8 in its simplest
-- form: a *bounded enumeration* extractor.  A `BoundedSearch f y
-- bound` packages an explicit candidate function `Fin bound → A`
-- together with a hit position — i.e. an enumeration that finds
-- the witness within `bound` attempts.  This is the lightest
-- operational substantiation of the `feasible` grade in
-- `EchoAccess`: a bounded search IS a constructive extractor, and
-- the bound IS the cost ledger.
--
-- Compared to the other three axis-8 artifacts:
--
-- * Refinement 1 (`EchoCost`) — scalar ℕ ledger, no operational
--   commitment.  The cost is bookkeeping.
-- * Refinement 2 (`EchoAccess`) — two-point modal lattice
--   `{feasible, infeasible}`.  The grade is a label; lattice
--   structure carries the modal content.
-- * Refinement 3 (`EchoDecidable`) — `Dec (Echo f y)`, qualitative
--   yes/no decidability layer.
-- * Refinement 4 (this module) — the bounded search IS an
--   operational extractor.  It substantiates the `feasible` grade
--   of refinement 2 and supplies a concrete cost (the bound) for
--   refinement 1.
--
-- Headline lemmas (pinned in `Smoke.agda`):
--
--   * BoundedSearch                        -- the bounded-search record
--   * bounded-search-to-echo               -- project to base Echo
--   * bounded-search-to-cost               -- bridge to refinement 1
--   * bounded-search-to-dec                -- bridge to refinement 3
--   * bounded-search-to-access-feasible    -- bridge to refinement 2 at feasible
--   * bounded-search-introduce-1           -- immediate witness at bound 1

module EchoSearch where

open import Level                                 using (Level; _⊔_)
open import Data.Nat.Base                         using (ℕ; suc; zero)
open import Data.Fin.Base                         using (Fin; zero)
open import Data.Product.Base                     using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core       using (yes)

open import Echo                                  using
  ( Echo
  ; echo-intro
  )
open import EchoCost                              using
  ( EchoCost
  ; cost-echo
  )
open import EchoDecidable                         using
  ( EchoDec
  )
open import EchoAccess                            using
  ( EchoA
  ; access-echo
  ; feasible
  )

----------------------------------------------------------------------
-- The witness-search abstract machine
----------------------------------------------------------------------

-- A bounded-enumeration extractor: a candidate-producing function on
-- `Fin bound` and a hit position witnessing that some candidate maps
-- to the target.  The `bound` measures search-space cardinality
-- (NOT step count of a more refined machine), so this is the
-- *unstructured-enumeration* layer of refinement 4.  A richer
-- abstract machine — `Step : Term → Term`, `Halts : Term → Set`,
-- step-counter — would refine this further; the present layer is
-- what we can land under `--safe --without-K` without committing
-- to a specific term-language.

record BoundedSearch
  {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B) (bound : ℕ) : Set (a ⊔ b) where
  constructor bounded-search
  field
    enumerate : Fin bound → A
    hit       : Σ (Fin bound) (λ i → f (enumerate i) ≡ y)

open BoundedSearch public

----------------------------------------------------------------------
-- Headline 1 — `bounded-search-to-echo`.
--
-- Project to the base information-theoretic echo by extracting the
-- hit candidate.  This is the canonical "search succeeded" → "echo
-- exists" map.  Mirrors `echo-cost-forget` / `echo-access-forget`
-- at the bottom of the axis-8 lattice.
----------------------------------------------------------------------

bounded-search-to-echo :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} {n : ℕ}
  → BoundedSearch f y n → Echo f y
bounded-search-to-echo s =
  let (i , p) = hit s
  in enumerate s i , p

----------------------------------------------------------------------
-- Headline 2 — `bounded-search-to-cost`.
--
-- Bridge to refinement 1 (cost-indexed echo, `EchoCost`).  The
-- enumeration bound BECOMES the cost ledger.  This is the
-- operational content refinement 1 lacked: where `EchoCost`'s `ℕ`
-- field was bookkeeping, here it is a real upper bound on the
-- number of candidates the search examined.
----------------------------------------------------------------------

bounded-search-to-cost :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} {n : ℕ}
  → BoundedSearch f y n → EchoCost f y
bounded-search-to-cost {n = n} s = cost-echo (bounded-search-to-echo s) n

----------------------------------------------------------------------
-- Headline 3 — `bounded-search-to-dec`.
--
-- Bridge to refinement 3 (decidability-respecting echo,
-- `EchoDecidable`).  A bounded search that found the witness gives
-- a `yes`-decision immediately.  This is the same bridge as
-- `echo-cost-to-dec` but with the operational backing the cost
-- ledger lacked.
----------------------------------------------------------------------

bounded-search-to-dec :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} {n : ℕ}
  → BoundedSearch f y n → EchoDec f y
bounded-search-to-dec s = yes (bounded-search-to-echo s)

----------------------------------------------------------------------
-- Headline 4 — `bounded-search-to-access-feasible`.
--
-- Bridge to refinement 2 (graded access modality, `EchoAccess`) at
-- the `feasible` grade.  This is the operational substantiation
-- refinement 2's `feasible` grade was waiting for: a bounded
-- search IS a constructive extractor, and is therefore feasibly
-- accessible (in the modal sense — not yet a complexity-class
-- claim, since the bound is unstructured).
--
-- Contrast with `echo-access-from-cost`, which projects
-- conservatively to `infeasible`: the cost ledger alone doesn't
-- substantiate feasibility.  Here, the explicit enumeration does.
----------------------------------------------------------------------

bounded-search-to-access-feasible :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} {n : ℕ}
  → BoundedSearch f y n → EchoA f y feasible
bounded-search-to-access-feasible s = access-echo (bounded-search-to-echo s)

----------------------------------------------------------------------
-- Headline 5 — `bounded-search-introduce-1`.
--
-- An immediate witness `x : A` gives a one-step bounded search
-- whose single candidate is `x` itself.  The enumeration function
-- is the constant `x` at the unique position `Fin 1`, and the hit
-- is `(zero , refl)`.  Mirrors `echo-intro` / `echo-dec-intro` /
-- `echo-cost-intro-zero` at the bottom of the axis-8 lattice.
----------------------------------------------------------------------

bounded-search-introduce-1 :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (x : A) → BoundedSearch f (f x) 1
bounded-search-introduce-1 f x =
  bounded-search (λ _ → x) (zero , refl)
