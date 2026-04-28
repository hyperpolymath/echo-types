{-# OPTIONS --safe --without-K #-}

-- Phase 1.3 — STATUS: scaffolding only.  The recursive `_≤′_`
-- definition lands here, plus `osuc-mono-≤′ p = p` (the bullseye
-- lemma).  `≤′-refl` for the `olim f` case requires `f-in-lim′`,
-- which is the documented obstacle described below.
--
-- This module compiles under `--safe --without-K`.  Anything that
-- depends on the open `f-in-lim′` is left out so the file is honest:
-- what's here is provable, what's not here is exactly the work
-- remaining.
--
-- ## Background
--
-- Echidna's SA design-search recommended switching `Ordinal.Brouwer._≤_`
-- to a fully-recursive shape (energy [0, 0, 1, 0]; both single-chain
-- and 4-agent swarm unanimous).  The data-style alternative
-- (`data + ≤-cong-suc`) was tested by hand-trace and rejected — the
-- new constructor cascades into mutually-recursive `pred-of-osuc`
-- proofs that need to be redesigned alongside.
--
-- See `echidna/docs/decisions/2026-04-28-corpus-and-design-search.md`
-- and `echo-types/docs/echidna-design-search-2026-04-28.adoc` for
-- the full design-search log.
--
-- ## What's done
--
-- * Recursive `_≤′_` defined; passes Agda's coverage + termination
--   checks under `--safe --without-K`.
-- * `osuc-mono-≤′ p = p` — the Phase-1.3 bullseye is identity.
-- * `≤′-zero` — definitional from the `oz ≤ _ = ⊤` clause.
-- * `osuc-mono-<′` — strict version, also identity-shaped.
--
-- ## What's open
--
-- * `≤′-refl` for the `olim f` case is `(n : ℕ) → f n ≤′ olim f`,
--   which requires `f-in-lim′ : ∀ f n → f n ≤′ olim f`.  The
--   `f-in-lim′` proof has three sub-cases (per `f n`'s constructor);
--   the `oz` and `osuc α` cases are routine, but the `olim g` case
--   (where `f n = olim g`) is the documented obstacle.
--
--   The `olim g` case wants `(m : ℕ) → g m ≤′ olim f`.  Termination is
--   fine — `g m` is strictly smaller than `f n = olim g`, so structural
--   recursion goes through — but Agda's `with f n` pattern loses the
--   equation `f n ≡ olim g`, leaving the goal in a shape Foetus can't
--   verify is decreasing.
--
--   Two viable closure paths:
--
--   1.  Mutual definition with `≤′-trans`.  Then the `olim g` case
--       becomes `≤′-trans (f-in-lim′ g m) (f-in-lim′ f n)` — both
--       calls are structurally smaller, and Foetus accepts mutual
--       structural recursion when each call shrinks one of the
--       lex-ordered measures.
--
--   2.  Strengthen `f-in-lim′` to carry an accessibility witness for
--       the limit — `(∀ k → Acc _<′_ (f k)) → f n ≤′ olim f`.  This
--       makes the recursion structure visible to Foetus directly.
--
-- The Phase-1.3 follow-up commit lands either path; for now the
-- recursive shape stands up + the bullseye lemma compiles.

module Ordinal.Brouwer.Phase13 where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)

open import Ordinal.Brouwer using (Ord; oz; osuc; olim)

----------------------------------------------------------------------------
-- Recursive `_≤′_` per the Echidna SA recommendation
----------------------------------------------------------------------------

infix 4 _≤′_

_≤′_ : Ord → Ord → Set
oz      ≤′ _        = ⊤
osuc α  ≤′ oz       = ⊥
osuc α  ≤′ osuc β   = α ≤′ β
osuc α  ≤′ olim f   = Σ ℕ (λ n → osuc α ≤′ f n)
olim f  ≤′ β        = (n : ℕ) → f n ≤′ β

----------------------------------------------------------------------------
-- Phase-1.3 bullseye: osuc-mono-≤′ is identity
----------------------------------------------------------------------------

-- Under the recursive definition, `osuc α ≤′ osuc β` reduces
-- definitionally to `α ≤′ β`.  No structural recursion on the proof,
-- no case split on α or β.  This is the entire point of the
-- redesign — what was a non-trivial induction in the data-`_≤_`
-- shape collapses to identity.

osuc-mono-≤′ : ∀ {α β} → α ≤′ β → osuc α ≤′ osuc β
osuc-mono-≤′ p = p

-- Strict version follows immediately.  α <′ β is `osuc α ≤′ β`.

infix 4 _<′_

_<′_ : Ord → Ord → Set
α <′ β = osuc α ≤′ β

osuc-mono-<′ : ∀ {α β} → α <′ β → osuc α <′ osuc β
osuc-mono-<′ p = p

----------------------------------------------------------------------------
-- Trivial corollaries (all definitional)
----------------------------------------------------------------------------

≤′-zero : ∀ {α} → oz ≤′ α
≤′-zero = tt

-- `oz <′ α` for α nonzero. Since `oz <′ α = osuc oz ≤′ α`, we case on α.

oz<′osuc : ∀ {α} → oz <′ osuc α
oz<′osuc {α} = ≤′-zero {α}
