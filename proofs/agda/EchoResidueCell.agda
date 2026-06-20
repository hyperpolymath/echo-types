-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- EchoResidueCell: the Agda mirror of 007's `ResidueCell` (Holding / Spent)
-- operational once-only reversal discipline, under --safe --without-K.
--
-- 007's Layer-10 reversibility runtime (and its Idris2 spec
-- `proofs/idris2/EchoResidueLinear.idr`) represents an armed undo as a
-- `ResidueCell f y` that is either `Holding` a residue or `Spent`.
-- `takeForReverse` replays a Holding cell (recovering the input) and returns
-- `nothing` on a Spent cell; consuming a cell transitions it Holding → Spent,
-- so a residue reverses AT MOST ONCE.
--
-- The Idris version enforces once-only via the LINEAR quantity `(1 e : Echo f
-- y)`. Agda has no such quantity under `--safe`, so this module enforces it
-- via the STATE MACHINE instead: `consume` makes the cell `Spent`, and
-- `once-only` proves that a second `takeForReverse` after `consume` is always
-- `nothing`. This is the operational half that `EchoReversibilityBridge`
-- deferred as "runtime Holding/Spent bookkeeping": the bridge's
-- `takeForReverse` is the *total* `Just`-branch (a bare `Echo f y → A`); here
-- it is the partial `ResidueCell f y → Maybe A` with the cell carrying the
-- Holding/Spent state.
--
-- Honest scope: this captures the once-PER-CELL discipline operationally. It
-- does NOT model linear NON-DUPLICATION (nothing stops a caller copying a
-- `holding` cell before consuming) — that needs the `(1 e)` quantity / an
-- `@0`-style erasure encoding and remains the documented next slice.

{-# OPTIONS --safe --without-K #-}

module EchoResidueCell where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (proj₁)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo using (Echo; echo-intro)

private variable
  a b : Level
  A : Set a
  B : Set b

-- A residue cell over the visible output `y`: either `holding` an echo
-- residue, or `spent`. (= the Idris `ResidueCell`; `holding` takes a bare
-- `Echo f y` rather than a linear `(1 e)` — see the honest-scope note above.)
data ResidueCell {a b} {A : Set a} {B : Set b} (f : A → B) (y : B)
       : Set (a ⊔ b) where
  holding : Echo f y → ResidueCell f y
  spent   : ResidueCell f y

-- Replay the cell: a `holding` cell yields the recovered input; a `spent`
-- cell yields `nothing`. (= the Idris `takeForReverse`.)
takeForReverse : {f : A → B} {y : B} → ResidueCell f y → Maybe A
takeForReverse (holding e) = just (proj₁ e)
takeForReverse spent       = nothing

-- Consuming a cell transitions `holding → spent` (`spent` stays `spent`).
-- This is the cell-state effect of a `reverse <name>` in 007.
consume : {f : A → B} {y : B} → ResidueCell f y → ResidueCell f y
consume (holding _) = spent
consume spent       = spent

-- A `holding` cell armed from `x` reverses to exactly `x`
-- (= Idris `holdingReverses`).
holding-reverses : (f : A → B) (x : A) →
                   takeForReverse (holding (echo-intro f x)) ≡ just x
holding-reverses f x = refl

-- A `spent` cell never reverses (= Idris `spentDoesNotReverse`).
spent-does-not-reverse : {f : A → B} {y : B} →
                         takeForReverse {f = f} {y} spent ≡ nothing
spent-does-not-reverse = refl

-- Consuming a `holding` cell spends it.
consume-spends : {f : A → B} {y : B} (e : Echo f y) →
                 consume (holding e) ≡ spent
consume-spends _ = refl

-- THE once-only theorem: after consuming ANY cell, a further `takeForReverse`
-- is always `nothing` — a residue reverses at most once. This is the
-- state-machine form of the Idris `(1 e)` linear-consumption guarantee, and
-- the operational content of 007's cross-handler "once-only" property that
-- the rung-3b *static* check could only approximate by presence.
once-only : {f : A → B} {y : B} (c : ResidueCell f y) →
            takeForReverse (consume c) ≡ nothing
once-only (holding _) = refl
once-only spent       = refl
