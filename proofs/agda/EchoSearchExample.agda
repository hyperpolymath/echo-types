{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- A worked axis-8 lattice exhibit: a concrete bounded search
-- (`EchoSearch.EchoS`, refinement 4) for a small doubling function,
-- projected through the other axis-8 refinements.
--
-- `EchoSearchInstance` pins the `EchoSearch` headlines at the
-- trivial-on-⊤ instance (proof-of-life only). This module is the
-- non-trivial operational counterpart: one concrete witness, found by
-- an explicit step-bounded enumeration, chased to
--
--   * the base information-theoretic `Echo`        (axis 1),
--   * refinement 1 (`EchoCost.Cost.EchoC`)         at a real ℕ cost
--                                                  algebra,
--   * refinement 3 (`EchoDecidable.EchoDec`)       from a search hit,
--   * refinement 2 (`EchoAccess.CEcho … feasible`) via `degrade-access`.
--
-- Setting: `double : ℕ → ℕ`, `double n = n + n` (by recursion).  At
-- the target `6` the witness is `3`.  The enumerator is the identity
-- on ℕ (step `k` proposes candidate `k`), so a budget of `4` admits
-- the candidates `0, 1, 2, 3` and the hit is at index `3`.  The landed
-- `bounded-search-is-decidable` procedure, run on this instance,
-- computes to `yes` on exactly that witness (`search-double-6-decided`).
-- Note that procedure tests indices from the top of the budget
-- downwards (`suc n` tests `enum n` first), so here it hits index `3`
-- on its *first* comparison; it does not walk `0, 1, 2, 3`.
--
-- Honesty notes:
--
--   * The cost bridge is specialised to the identity enumerator: the
--     cost of a candidate is its enumeration position (inclusive),
--     `search-steps x = suc x` — the number of steps an *ascending*
--     scan of `countUp` takes to reach `x`.  It is a function of `x`
--     only because the enumerator is `id`.  It is a property of the
--     enumerator, NOT the executed comparison count of
--     `bounded-search-is-decidable` (which scans downwards and here
--     makes one comparison).  With that choice the
--     search bound `k < n` *is* the budget receipt `suc k ≤ n` on the
--     nose (stdlib's `_<_` unfolds to `suc k ≤ n`), so no arithmetic
--     glue is needed.  A general-enumerator cost bridge would need the
--     step index carried in the witness and is not attempted here.
--
--   * The `feasible` carrier of `EchoAccess.CEcho` is the deliberate
--     `Lift ⊤` placeholder (decision doc
--     `docs/echo-types/decisions/echo-access-trivial-carrier.adoc`);
--     `search-as-feasible` therefore records the *grade* reached by
--     `degrade-access`, not extractable content.
--
-- Headlines (pinned in `Smoke.agda`):
--
--   * double                              -- the doubling function
--   * search-double-6                     -- the bounded search
--   * search-double-6-decided             -- bounded decision computes to `yes`
--   * search-as-echo                      -- bridge to base Echo
--   * search-as-cost                      -- bridge to refinement 1
--   * search-as-dec                       -- bridge to refinement 3
--   * search-as-feasible                  -- bridge to refinement 2

module EchoSearchExample where

open import Level                                 using (0ℓ)
open import Function.Base                         using (id)
open import Data.Nat.Base                         using (ℕ; zero; suc; _+_; s≤s; z≤n)
open import Data.Nat.Properties                   using (_≟_; +-mono-≤)
import Data.Nat.Base                              as ℕ
import Data.Nat.Properties                        as ℕₚ
open import Data.Product.Base                     using (_,_)
open import Relation.Nullary                      using (yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo                                  using (Echo)
open import EchoCost                              using (CostAlgebra; module Cost)
open import EchoDecidable                         using (EchoDec)
open import EchoAccess                            using (CEcho; feasible; free≤feasible; degrade-access)
open import EchoSearch                            using
  ( SearchStrategy
  ; EchoS
  ; echo-search-forget
  ; bounded-search-is-decidable
  )

----------------------------------------------------------------------
-- The map: doubling
----------------------------------------------------------------------

-- A tiny map with a nontrivial search: `Echo double 6` has the unique
-- witness `3`, which sits at position `3` of the `countUp` enumeration,
-- inside a budget of `4`.

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

----------------------------------------------------------------------
-- The bounded search at target 6
----------------------------------------------------------------------

-- Step `k` of the identity enumerator proposes candidate `k`.
countUp : SearchStrategy ℕ
countUp = id

-- The hit is at step `3 < 4`, where `double 3 ≡ 6` by computation.
search-double-6 : EchoS countUp double 6 4
search-double-6 = 3 , s≤s (s≤s (s≤s (s≤s z≤n))) , refl

-- The landed decision procedure, run on this instance, *finds* the
-- same search echo: the bounded decision computes to `yes` by `refl`.
-- The witness is not merely asserted, the decider produces it.  (The
-- decider scans from index `3` downwards, so this is a one-comparison
-- hit; it is not evidence of an ascending four-step walk.)
search-double-6-decided :
  bounded-search-is-decidable _≟_ countUp double 6 4 ≡ yes search-double-6
search-double-6-decided = refl

----------------------------------------------------------------------
-- A real cost algebra: ℕ with step counts
----------------------------------------------------------------------

stepCostAlgebra : CostAlgebra 0ℓ
stepCostAlgebra = record
  { Cost        = ℕ
  ; zero        = 0
  ; _+_         = _+_
  ; _≤_         = ℕ._≤_
  ; ≤-refl      = ℕₚ.≤-refl
  ; ≤-trans     = ℕₚ.≤-trans
  ; +-identityˡ = λ _ → refl
  ; +-mono-≤    = +-mono-≤
  }

open Cost stepCostAlgebra using (EchoC)

-- Enumeration position of candidate `x` under `countUp` (inclusive):
-- an ascending scan reaches `0` in one step, `x` in `suc x`.  This is
-- the cost the bound `k < n` certifies, not the decider's work.
search-steps : ℕ → ℕ
search-steps = suc

----------------------------------------------------------------------
-- The bridges
----------------------------------------------------------------------

-- Refinement 4 → refinement 1. A bound-`n` search echo under the
-- identity enumerator is a cost echo with budget `n` under the
-- step-count cost: `k < n` is definitionally `search-steps k ≤ n`.
count-up-search-to-cost :
  ∀ {b} {B : Set b} {f : ℕ → B} {y : B} {n : ℕ} →
  EchoS countUp f y n → EchoC search-steps n f y
count-up-search-to-cost (k , k<n , eq) = k , eq , k<n

-- Refinement 4 → refinement 3. A search hit is a constructive `yes`.
-- (A bounded *miss* does not refute the unbounded echo, so the bridge
-- is stated from a hit only.)
search-to-dec :
  ∀ {a b} {A : Set a} {B : Set b}
  {enum : SearchStrategy A} {f : A → B} {y : B} {n : ℕ} →
  EchoS enum f y n → EchoDec f y
search-to-dec s = yes (echo-search-forget s)

----------------------------------------------------------------------
-- The bridges, fired on the concrete witness
----------------------------------------------------------------------

-- Project to the base information-theoretic echo.  Just the witness.
search-as-echo : Echo double 6
search-as-echo = echo-search-forget search-double-6

-- Refinement 1: the witness with a budget receipt of 4 steps.
search-as-cost : EchoC search-steps 4 double 6
search-as-cost = count-up-search-to-cost search-double-6

-- Refinement 3: a `yes`-decision carrying the witness.
search-as-dec : EchoDec double 6
search-as-dec = search-to-dec search-double-6

-- Refinement 2 at `feasible`: degrade the in-hand (`free`) echo along
-- the access order.  The carrier at `feasible` is the `Lift ⊤`
-- placeholder; what this records is the grade.
search-as-feasible : CEcho feasible double 6
search-as-feasible = degrade-access free≤feasible search-as-echo
