{-# OPTIONS --safe --without-K #-}

-- A worked axis-8 lattice exhibit: a concrete `BoundedSearch` for
-- a small doubling function and its projections through the four
-- axis-8 refinements.
--
-- Demonstrates `EchoSearch.BoundedSearch` (refinement 4) in
-- operational use, then chases the four bridges to refinements 1
-- (`EchoCost`), 2 (`EchoAccess.EchoA … feasible`), and 3
-- (`EchoDecidable.EchoDec`).  The whole axis-8 lattice fires on a
-- single concrete witness.
--
-- Setting: `double : ℕ → ℕ`, `double n = n + n`.  At the target
-- value `6`, the witness is `3` (since `3 + 3 ≡ 6`).  A bounded
-- search with `bound = 4` and enumeration `λ i → toℕ i` finds the
-- witness at position `Fin 4`'s third index.  This is a small
-- enough concrete operational substantiation that the bridges all
-- fire by direct application.
--
-- Headlines (pinned in `Smoke.agda`):
--
--   * double                              -- the doubling function
--   * search-double-6                     -- the bounded search
--   * search-as-echo                      -- bridge to base Echo
--   * search-as-cost                      -- bridge to refinement 1
--   * search-as-dec                       -- bridge to refinement 3
--   * search-as-feasible                  -- bridge to refinement 2

module EchoSearchExample where

open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Fin.Base                         using (Fin; zero; suc)
open import Data.Product.Base                     using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo                                  using (Echo)
open import EchoCost                              using (EchoCost)
open import EchoDecidable                         using (EchoDec)
open import EchoAccess                            using (EchoA; feasible)
open import EchoSearch                            using
  ( BoundedSearch
  ; bounded-search
  ; bounded-search-to-echo
  ; bounded-search-to-cost
  ; bounded-search-to-dec
  ; bounded-search-to-access-feasible
  )

----------------------------------------------------------------------
-- The map: doubling
----------------------------------------------------------------------

-- A tiny lossy collapse: `double n = n + n`.  Echo at `6` has a
-- unique witness `3`, but the *search procedure* for finding it
-- is a 4-step enumeration that explicitly tries `0, 1, 2, 3`.

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

----------------------------------------------------------------------
-- The bounded search at target 6
----------------------------------------------------------------------

-- A 4-position enumeration: candidate `i` (as a `Fin 4`) corresponds
-- to natural-number `i`.  The hit is at position `3 : Fin 4`, where
-- `double 3 = 6`.

search-double-6 : BoundedSearch double 6 4
search-double-6 = bounded-search enumerate hit
  where
  enumerate : Fin 4 → ℕ
  enumerate zero                   = 0
  enumerate (suc zero)             = 1
  enumerate (suc (suc zero))       = 2
  enumerate (suc (suc (suc zero))) = 3

  hit : _
  hit = suc (suc (suc zero)) , refl

----------------------------------------------------------------------
-- The four axis-8 bridges, fired
----------------------------------------------------------------------

-- Project to the base information-theoretic echo.  Just the witness.
search-as-echo : Echo double 6
search-as-echo = bounded-search-to-echo search-double-6

-- Bridge to refinement 1: pair the witness with the search bound as
-- a cost ledger.  This is the operational content `EchoCost` lacked
-- when standing alone.
search-as-cost : EchoCost double 6
search-as-cost = bounded-search-to-cost search-double-6

-- Bridge to refinement 3: a `yes`-decision with the witness.
search-as-dec : EchoDec double 6
search-as-dec = bounded-search-to-dec search-double-6

-- Bridge to refinement 2 at `feasible`: the modal substantiation
-- that says "computationally accessible".  Operationally backed by
-- the explicit search procedure.
search-as-feasible : EchoA double 6 feasible
search-as-feasible = bounded-search-to-access-feasible search-double-6
