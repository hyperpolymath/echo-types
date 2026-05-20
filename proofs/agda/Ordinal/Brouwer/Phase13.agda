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
-- * `≤′-self-osuc` — every ordinal is below its successor: x ≤′ osuc x.
-- * `≤′-weaken-osuc` — weakening: x ≤′ y → x ≤′ osuc y.
-- * `⊕-left-≤-sum` — left addend ≤ sum: α ≤′ α ⊕ γ.
-- * `⊕-mono-≤-right` — `_⊕_` is monotone on the right w.r.t. `≤′`.
-- * `⊕-mono-<-right` — `_⊕_` is strictly monotone on the right
--   w.r.t. `<′`.  Closes the `<ᵇʳᶠ-ψα` and `<ᵇʳᶠ-+2` cases of
--   `rank-mono` in `Ordinal.Buchholz.RankBrouwer` (issue #34).
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
open import Ordinal.Brouwer.Arithmetic using (_⊕_)

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

----------------------------------------------------------------------------
-- x ≤′ osuc x (every ordinal is strictly below its successor)
----------------------------------------------------------------------------

-- Structural recursion on x.  The `olim f` case uses f-in-lim′ to
-- route through the branch: f n ≤′ osuc (f n) ≤′ osuc (olim f).
-- The last step holds because `osuc (f n) ≤′ osuc (olim f)` reduces
-- definitionally to `f n ≤′ olim f`, which is f-in-lim′.

≤′-self-osuc : ∀ x → x ≤′ osuc x
≤′-self-osuc oz       = tt
≤′-self-osuc (osuc x) = ≤′-self-osuc x
≤′-self-osuc (olim f) = λ n →
  ≤′-trans {f n} {osuc (f n)} {osuc (olim f)}
    (≤′-self-osuc (f n))
    (f-in-lim′ f n)

-- Weakening: x ≤′ y → x ≤′ osuc y.  One-liner via transitivity and
-- ≤′-self-osuc; no case analysis needed.

≤′-weaken-osuc : ∀ {x y} → x ≤′ y → x ≤′ osuc y
≤′-weaken-osuc {x} {y} p = ≤′-trans {x} {y} {osuc y} p (≤′-self-osuc y)

----------------------------------------------------------------------------
-- α ≤′ α ⊕ γ (left addend is always ≤ the sum)
----------------------------------------------------------------------------

-- Structural recursion on γ.  Right-recursive `_⊕_` is essential:
-- each case of γ reduces `α ⊕ γ` to a form whose `_≤′_` target is
-- immediately dischargeable.

⊕-left-≤-sum : ∀ {α} γ → α ≤′ α ⊕ γ
⊕-left-≤-sum {α}        oz       = ≤′-refl {α}
⊕-left-≤-sum {α}        (osuc γ') = ≤′-weaken-osuc {α} {α ⊕ γ'} (⊕-left-≤-sum {α} γ')
⊕-left-≤-sum {α}        (olim g)  =
  ≤′-trans {α} {α ⊕ g 0} {α ⊕ olim g}
    (⊕-left-≤-sum {α} (g 0))
    (f-in-lim′ (λ n → α ⊕ g n) 0)

----------------------------------------------------------------------------
-- Right monotonicity of `_⊕_` (issue #34 fix)
----------------------------------------------------------------------------

-- `⊕-mono-<-right` and `⊕-mono-≤-right` are mutually recursive.
-- Both induct primarily on γ (for <) or β (for ≤), with the other
-- position decreasing in cross-calls.  Agda's termination checker
-- accepts the lex pair (β, γ) as the measure.
--
-- Right-recursive `_⊕_` is the enabling change: each constructor of
-- γ in `⊕-mono-<-right` matches exactly one clause of `_≤′_`'s
-- second-argument computation, giving a direct proof path.

mutual

  ⊕-mono-<-right : ∀ {α β γ} → β <′ γ → α ⊕ β <′ α ⊕ γ
  ⊕-mono-<-right {_} {_} {oz}      ()
  ⊕-mono-<-right {α} {β} {osuc γ'} p       = ⊕-mono-≤-right {α} {β}  {γ'} p
  ⊕-mono-<-right {α} {β} {olim g}  (n , p) = n , ⊕-mono-<-right {α} {β} {g n} p

  ⊕-mono-≤-right : ∀ {α β γ} → β ≤′ γ → α ⊕ β ≤′ α ⊕ γ
  ⊕-mono-≤-right {α} {oz}      {γ}       _       = ⊕-left-≤-sum {α} γ
  ⊕-mono-≤-right {_} {osuc _}  {oz}      ()
  ⊕-mono-≤-right {α} {osuc β'} {osuc γ'} p       = ⊕-mono-≤-right {α} {β'} {γ'} p
  ⊕-mono-≤-right {α} {osuc β'} {olim g}  (n , p) = n , ⊕-mono-<-right {α} {β'} {g n} p
  ⊕-mono-≤-right {α} {olim f}  {γ}       p       = λ n → ⊕-mono-≤-right {α} {f n} {γ} (p n)

----------------------------------------------------------------------------
-- Left monotonicity of `_⊕_` (companion to right-mono above)
----------------------------------------------------------------------------

-- `α ≤′ β → α ⊕ γ ≤′ β ⊕ γ`.  Recursion on `γ`; each case of γ
-- matches one clause of the right-recursive `_⊕_` definition.
--
--   * γ = oz       : α ⊕ oz = α, β ⊕ oz = β; reduces to `α ≤′ β`.
--   * γ = osuc γ'  : both sides reduce to successors of sub-sums;
--                    `osuc-mono-≤′ = id` collapses to the IH on γ'.
--   * γ = olim g   : both sides are limits with branch-shifted sums;
--                    each branch dischargeable by IH plus `f-in-lim′`.

⊕-mono-≤-left : ∀ {α β γ} → α ≤′ β → α ⊕ γ ≤′ β ⊕ γ
⊕-mono-≤-left {α} {β} {oz}      p = p
⊕-mono-≤-left {α} {β} {osuc γ'} p = ⊕-mono-≤-left {α} {β} {γ'} p
⊕-mono-≤-left {α} {β} {olim g}  p = λ k →
  ≤′-trans {α ⊕ g k} {β ⊕ g k} {β ⊕ olim g}
    (⊕-mono-≤-left {α} {β} {g k} p)
    (⊕-mono-≤-right {β} {g k} {olim g} (f-in-lim′ g k))

-- Note: strict left-monotonicity of `_⊕_` is NOT a theorem.
-- Counterexample: `α = oz`, `β = osuc oz`, `γ = ω = olim nat-to-ord`.
-- Both `α ⊕ γ` and `β ⊕ γ` evaluate to (the Brouwer representation
-- of) ω; right-recursive `_⊕_` distributes through the limit, and
-- the finite-step shift gets absorbed by the supremum.  Classically:
-- for any finite n, `n + ω = ω`, so the inequality `α + γ < β + γ`
-- fails when γ is a limit and the gap `β - α` is finite.  Only the
-- non-strict `⊕-mono-≤-left` above is sound.

----------------------------------------------------------------------------
-- Associativity of `_⊕_` (both directions, in `≤′` form)
----------------------------------------------------------------------------

-- Propositional `(A ⊕ B) ⊕ C ≡ A ⊕ (B ⊕ C)` requires function
-- extensionality on the `olim` limb (the two underlying ℕ-indexed
-- functions agree pointwise but the binders are at different depths
-- of the right-recursive `_⊕_` definition).  Both `≤′` directions
-- are funext-free and suffice for downstream consumers.
--
-- Each direction is a structural recursion on `C`:
--   * C = oz       : both sides reduce to `A ⊕ B`; ≤′-refl.
--   * C = osuc C'  : both sides are osuc-wrapped sub-sums; the
--                    `osuc/osuc` clause of `_≤′_` collapses to the IH.
--   * C = olim g   : both sides are limits indexed by g; branch-by-
--                    branch IH combined with `f-in-lim′`.

⊕-assoc-≤ : ∀ {A B C} → (A ⊕ B) ⊕ C ≤′ A ⊕ (B ⊕ C)
⊕-assoc-≤ {A} {B} {oz}      = ≤′-refl {A ⊕ B}
⊕-assoc-≤ {A} {B} {osuc C'} = ⊕-assoc-≤ {A} {B} {C'}
⊕-assoc-≤ {A} {B} {olim g}  = λ k →
  ≤′-trans
    {(A ⊕ B) ⊕ g k}
    {A ⊕ (B ⊕ g k)}
    {A ⊕ (B ⊕ olim g)}
    (⊕-assoc-≤ {A} {B} {g k})
    (⊕-mono-≤-right {A} {B ⊕ g k} {B ⊕ olim g}
      (⊕-mono-≤-right {B} {g k} {olim g} (f-in-lim′ g k)))

⊕-assoc-≥ : ∀ {A B C} → A ⊕ (B ⊕ C) ≤′ (A ⊕ B) ⊕ C
⊕-assoc-≥ {A} {B} {oz}      = ≤′-refl {A ⊕ B}
⊕-assoc-≥ {A} {B} {osuc C'} = ⊕-assoc-≥ {A} {B} {C'}
⊕-assoc-≥ {A} {B} {olim g}  = λ k →
  ≤′-trans
    {A ⊕ (B ⊕ g k)}
    {(A ⊕ B) ⊕ g k}
    {(A ⊕ B) ⊕ olim g}
    (⊕-assoc-≥ {A} {B} {g k})
    (f-in-lim′ (λ j → (A ⊕ B) ⊕ g j) k)
