{-# OPTIONS --safe --without-K #-}

-- Axis-8 (taxonomy.md §8) second artifact: cost-indexed echo.
--
-- The dependent-sum `Echo f y` expresses *information-theoretic*
-- accessibility (a witness exists in the metatheory).
-- `EchoDecidable.EchoDec f y` (axis-8 first artifact) pairs the echo
-- with a *constructive decision procedure* — the qualitative
-- "yes/no" layer of axis 8.
--
-- This module ships the next layer up:
--
--   record EchoCost (f : A → B) (y : B) where
--     witness : Echo f y
--     cost    : ℕ
--
-- An `EchoCost f y` is a *cost-indexed echo*: a witness together with
-- a non-negative cost ledger.  The cost is not (yet) tied to an
-- operational semantics — Agda's type system does not express
-- complexity bounds (`taxonomy.md` §8 lines 228–230) — so the cost
-- here is bookkeeping, not a complexity-class claim.  What the layer
-- does provide is a uniform shape for the heavier refinements
-- (witness-search machine, graded access modality) to project down
-- into: every cost-bearing echo forgets to a decidability echo,
-- which forgets to a base echo, which forgets to extensional
-- inhabitedness.  The axis-8 lattice is named explicitly.
--
-- Of the four refinement candidates listed in `taxonomy.md` §8, this
-- is refinement 1 ("Cost-indexed echo.  Pair `Echo f y` with a
-- witness-extraction bound").  The fully realised version would
-- replace the `ℕ` field with a resource monad / cost-passing
-- semantics; the bookkeeping shape lands today and the upgrade is
-- orthogonal.
--
-- Headline lemmas (pinned in `Smoke.agda`):
--
--   * echo-cost-forget       -- project down to base Echo
--   * echo-cost-to-dec       -- project down to EchoDec (refinement 3)
--   * echo-cost-intro-zero   -- immediate witness has cost 0
--   * echo-cost-bump         -- upper bound is loose (cost can grow)
--   * echo-cost-compose      -- cost composes additively along g ∘ f

module EchoCost where

open import Level                                 using (Level; _⊔_)
open import Function.Base                         using (_∘_)
open import Data.Nat.Base                         using (ℕ; zero; suc; _+_)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core       using (yes)

open import Echo                                  using
  ( Echo
  ; echo-intro
  ; Echo-comp-iso-from
  )
open import EchoDecidable                         using
  ( EchoDec
  )

----------------------------------------------------------------------
-- The cost-indexed echo
----------------------------------------------------------------------

-- A cost-indexed echo at `y` is a witness paired with a non-negative
-- cost ledger.  The cost field is bookkeeping; the present module
-- makes no claim that the ledger reflects an operational notion of
-- extraction steps.  Downstream refinements (witness-search machine,
-- resource-monad cost-passing) would substantiate the ledger; this
-- shape names the layer where they project.

record EchoCost
  {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B) : Set (a ⊔ b) where
  constructor cost-echo
  field
    witness : Echo f y
    cost    : ℕ

open EchoCost public

----------------------------------------------------------------------
-- Headline 1 — `echo-cost-forget`.
--
-- A cost-indexed echo forgets its cost ledger to the base
-- information-theoretic echo.  This is the projection down the
-- axis-8 lattice from refinement 1 to the bare-existence layer.
----------------------------------------------------------------------

echo-cost-forget :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} → EchoCost f y → Echo f y
echo-cost-forget e = witness e

----------------------------------------------------------------------
-- Headline 2 — `echo-cost-to-dec`.
--
-- A cost-indexed echo also projects down to the decidability-
-- respecting layer (refinement 3, `EchoDecidable`).  The decider
-- returns `yes` with the carried witness: cost data is forgotten,
-- but the underlying constructive decision is retained.  This pins
-- refinement 1 → refinement 3 as one step of the axis-8 lattice.
----------------------------------------------------------------------

echo-cost-to-dec :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} → EchoCost f y → EchoDec f y
echo-cost-to-dec e = yes (witness e)

----------------------------------------------------------------------
-- Headline 3 — `echo-cost-intro-zero`.
--
-- The trivial direction of axis 8: an immediate witness `x : A`
-- gives a zero-cost echo.  Cost is bookkeeping; the immediate
-- witness has not "done" any work.  Mirrors `echo-dec-intro` from
-- `EchoDecidable`, adding the cost-zero ledger.
----------------------------------------------------------------------

echo-cost-intro-zero :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (x : A) → EchoCost f (f x)
echo-cost-intro-zero f x = cost-echo (echo-intro f x) zero

----------------------------------------------------------------------
-- Headline 4 — `echo-cost-bump`.
--
-- The cost ledger is a loose upper bound: an echo at cost `c` is
-- also an echo at any larger cost `c + k`.  This captures the
-- intuition that "this witness can be extracted in at most c steps"
-- weakens monotonically.  Useful when composing or transporting a
-- cost-indexed echo across operations whose precise step count is
-- not tracked.
----------------------------------------------------------------------

echo-cost-bump :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B}
  (k : ℕ) → EchoCost f y → EchoCost f y
echo-cost-bump k e = cost-echo (witness e) (cost e + k)

----------------------------------------------------------------------
-- Headline 5 — `echo-cost-compose`.
--
-- Cost composes additively along `g ∘ f`.  Given a cost-indexed
-- echo `(b , p : f x ≡ b , k₁)` in the f-fibre over an intermediate
-- `b`, and a cost-indexed echo `(b , q : g b ≡ y , k₂)` in the
-- g-fibre over `y`, we produce a cost-indexed echo `(x , g∘f x ≡ y,
-- k₁ + k₂)` in the composite-fibre.
--
-- This is the canonical complexity-composition shape: the cost of
-- extracting a `g ∘ f`-witness is the sum of the component costs.
-- The accumulation iso `Echo-comp-iso-to` supplies the witness; the
-- additive cost combines the ledgers.  Anchors `taxonomy.md` §8's
-- "Composition conjecture" at the bookkeeping layer (the
-- multiplicative-cost version would require a richer cost semiring
-- and is left to the witness-search-machine refinement).
----------------------------------------------------------------------

echo-cost-compose :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C}
  (b : B)
  → EchoCost f b
  → (g b ≡ y) × ℕ
  → EchoCost (g ∘ f) y
echo-cost-compose f g b ef (gb≡y , k₂) =
  cost-echo
    (Echo-comp-iso-from f g (b , witness ef , gb≡y))
    (cost ef + k₂)
