{-# OPTIONS --safe --without-K #-}

-- Phase 1.3 — recursive `_≤′_` per Echidna's SA + 4-agent swarm
-- recommendation (energy [0, 0, 1, 0]; both unanimous).  Replaces
-- the data-style `Ordinal.Brouwer._≤_` for the cases where
-- `osuc-mono` and structural shape matter, while leaving the
-- data-style intact so the existing `wf-<` proof keeps composing.
--
-- See `echidna/docs/decisions/2026-04-28-corpus-and-design-search.md`
-- and `echo-types/docs/echidna-design-search-2026-04-28.adoc` for
-- the full design-search log.
--
-- ## What's here
--
-- * Recursive `_≤′_` and derived `_<′_`.
-- * `osuc-mono-≤′ p = p`, `osuc-mono-<′ p = p` — the Phase-1.3
--   bullseyes collapse to identity under the recursive shape.
-- * `≤′-zero`, `oz<′osuc` — trivial corollaries.
-- * `≤′-lim` — the source-side limit-introduction lemma.
-- * `≤′-refl` — reflexivity, with the `olim f` case discharged by
--   `≤′-lim n (≤′-refl {f n})`.  The recursive call on `f n` is
--   structurally smaller than `olim f` per Agda's subterm relation
--   for higher-order inductive constructors.
-- * `f-in-lim′` — direct corollary `f n ≤′ olim f`, the recursive
--   analogue of `Ordinal.Brouwer.f-in-lim`.
-- * `≤′-trans` — transitivity, by lex structural recursion on
--   `(α, β, γ)`.  Together with `≤′-refl` this makes `_≤′_` a
--   preorder; `_<′_` strict-order companions follow downstream.
-- * `wf-<′` — well-foundedness of `_<′_`, by structural induction
--   on `Ord` mirroring `Ordinal.Brouwer.wf-<`.  Predecessor lemmas
--   `pred-of-osuc-<′` and `pred-of-olim-<′` reduce through the
--   computed shape of `_<′_` rather than constructor pattern-match.
--
-- ## Closure of the original obstacle
--
-- The earlier draft deferred `≤′-refl` for `olim f` because the
-- naïve `f-in-lim′` recursion on `f n`'s constructor lost the
-- equation `f n ≡ olim g` under `with`, blocking Foetus.  The
-- closure here factors through `≤′-lim`, which recurses on the
-- source α (not on `f n`).  Termination is then immediate: `α`
-- shrinks structurally on each recursive call, independent of `f`.

module Ordinal.Brouwer.Phase13 where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc; WellFounded)

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

----------------------------------------------------------------------------
-- Limit-introduction and reflexivity (Phase-1.3 closure)
----------------------------------------------------------------------------

-- Source-side limit introduction.  Any α that is `≤′`-below some
-- branch `f n` is also `≤′`-below the limit `olim f`.  Structural
-- recursion on the source α; the implicit `f` is threaded
-- unchanged.
--
-- This is the lemma that breaks the original obstacle.  The blocked
-- attempt recursed on `f n`'s constructor, which loses the equation
-- under `with`.  Recursing on α is fine: each constructor of the
-- source admits a direct construction of the limit-shaped result.

-- `f` is explicit because Agda can't infer it from the value `f n`
-- (the unification problem `_f_ n = f n` is non-unique — many
-- functions agree at a single point).  Each call site passes the
-- intended `f` directly.

≤′-lim : ∀ {α} (f : ℕ → Ord) (n : ℕ) → α ≤′ f n → α ≤′ olim f
≤′-lim {oz}     f n p = tt
≤′-lim {osuc α} f n p = n , p
≤′-lim {olim g} f n p = λ m → ≤′-lim {α = g m} f n (p m)

-- Reflexivity.  Structural recursion on α; the `olim f` case
-- threads through `≤′-lim` at each branch.

≤′-refl : ∀ {α} → α ≤′ α
≤′-refl {oz}     = tt
≤′-refl {osuc α} = ≤′-refl {α}
≤′-refl {olim f} = λ n → ≤′-lim {α = f n} f n (≤′-refl {f n})

-- Each branch of a limit sits at-or-below it.  Recursive analogue
-- of `Ordinal.Brouwer.f-in-lim`.  Falls out of `≤′-lim` plus
-- reflexivity at the branch.

f-in-lim′ : ∀ f n → f n ≤′ olim f
f-in-lim′ f n = ≤′-lim {α = f n} f n (≤′-refl {f n})

----------------------------------------------------------------------------
-- Transitivity (Phase-1.3 round-out)
----------------------------------------------------------------------------

-- Recursion on (α, β, γ) under the lex order.  Each non-base case
-- either terminates immediately on a ⊥ leg or recurses with one of
-- the three positions a strict structural subterm and the others
-- syntactically unchanged.  Agda's structural-recursion checker
-- accepts this as lex-decreasing; no explicit measure annotation
-- needed.

≤′-trans : ∀ {α β γ} → α ≤′ β → β ≤′ γ → α ≤′ γ
≤′-trans {oz}                                 _       _       = tt
≤′-trans {osuc _} {oz}                        p       _       = ⊥-elim p
≤′-trans {osuc _} {osuc _} {oz}               _       q       = ⊥-elim q
≤′-trans {osuc α} {osuc β} {osuc γ}           p       q       = ≤′-trans {α} {β} {γ} p q
≤′-trans {osuc α} {osuc β} {olim h}           p       (k , q) = k , ≤′-trans {osuc α} {osuc β} {h k} p q
≤′-trans {osuc α} {olim g} {γ}                (n , p) q       = ≤′-trans {osuc α} {g n} {γ} p (q n)
≤′-trans {olim f} {β} {γ}                     p       q       = λ n → ≤′-trans {f n} {β} {γ} (p n) q

----------------------------------------------------------------------------
-- Well-foundedness of `_<′_` (path (a) of the handoff)
----------------------------------------------------------------------------

-- The data-style `wf-<` proof recurses on the three constructors of
-- `_≤_`.  Here `_≤′_` is recursive — there are no constructors to
-- pattern-match on — so the predecessor lemmas reduce predecessors
-- through the computed shape of `_<′_`:
--
--   β <′ osuc α  ≡  osuc β ≤′ osuc α  ≡  β ≤′ α
--   β <′ olim f  ≡  Σ ℕ (λ n → β <′ f n)
--   β <′ oz      ≡  ⊥
--
-- so the `osuc` case is "lift hypothetical predecessors of β through
-- ≤′-trans to predecessors of α", and the `olim` case is the same
-- branch-selection move as the data-style `pred-of-olim`.

pred-of-osuc-<′ : ∀ {α} → Acc _<′_ α → ∀ {β} → β <′ osuc α → Acc _<′_ β
pred-of-osuc-<′ {α} (acc rsα) {β} p =
  acc (λ {γ} q → rsα (≤′-trans {osuc γ} {β} {α} q p))

pred-of-olim-<′ : ∀ {f} → (∀ n → Acc _<′_ (f n)) → ∀ {β} → β <′ olim f → Acc _<′_ β
pred-of-olim-<′ wfs (n , q) with wfs n
... | acc rs = rs q

-- Top-level WF: structural induction on `Ord`.  Mirrors `wf-<`'s
-- shape; differs only in the predecessor lemmas above.

wf-<′ : WellFounded _<′_
wf-<′ oz       = acc (λ {β} ())
wf-<′ (osuc α) = acc (pred-of-osuc-<′ (wf-<′ α))
wf-<′ (olim f) = acc (pred-of-olim-<′ (λ n → wf-<′ (f n)))
