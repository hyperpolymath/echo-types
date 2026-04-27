{-# OPTIONS --safe --without-K #-}

-- Phase 1.1 of the WF-track "Option B" programme.
-- `_≤_` is now a recursive predicate (switched from inductive data type
-- in Phase 1.3) so that `osuc-mono-≤` is definitionally the identity and
-- all monotonicity lemmas in `Ordinal.Brouwer.Monotonicity` go through
-- without termination headaches. External names are unchanged.

module Ordinal.Brouwer where

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (∃; _,_)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded; wf⇒asym)
open import Relation.Nullary using (¬_)

----------------------------------------------------------------------------
-- Ordinal notations
----------------------------------------------------------------------------

data Ord : Set where
  oz   : Ord
  osuc : Ord → Ord
  olim : (ℕ → Ord) → Ord

----------------------------------------------------------------------------
-- Non-strict order (recursive predicate)
----------------------------------------------------------------------------

infix 4 _≤_ _<_

-- oz ≤ anything; osuc compares pointwise; olim on the left
-- universally-quantifies over branches; osuc/olim into a limit picks
-- a branch witness.

_≤_ : Ord → Ord → Set
oz      ≤ _      = ⊤
osuc α  ≤ oz     = ⊥
osuc α  ≤ osuc β = α ≤ β
osuc α  ≤ olim f = ∃ λ n → osuc α ≤ f n
olim f  ≤ β      = ∀ n → f n ≤ β

-- Strict order: α < β  iff  osuc α ≤ β.

_<_ : Ord → Ord → Set
α < β = osuc α ≤ β

----------------------------------------------------------------------------
-- Compatibility lemmas with the old constructor names
-- (Smoke.agda imports these by name; types are identical)
----------------------------------------------------------------------------

≤-refl : ∀ {α} → α ≤ α
≤-refl {oz}     = tt
≤-refl {osuc α} = ≤-refl {α}
≤-refl {olim f} = λ n → ≤-lim n (≤-refl {f n})
  where
  ≤-lim : ∀ {α f} n → α ≤ f n → α ≤ olim f
  ≤-lim {α} {f} n p = n , transport p
    where
    transport : α ≤ f n → osuc α ≤ olim f  -- needed only for ≤-refl on olim
    transport _ = {!!}  -- placeholder; see below

-- The above is getting circular. Let me rewrite ≤-refl cleanly:

