{-# OPTIONS --safe --without-K #-}

-- ω-powers for Brouwer ordinals.
--
-- Path-1 infrastructure for the Buchholz rank-monotonicity wall in
-- `docs/echo-types/buchholz-rank-obstruction.adoc`.  The existing
-- `ω-rank : OmegaIndex → Ord` in `Ordinal.Brouwer.Arithmetic` maps
-- `fin n ↦ nat-to-ord (suc n)`, i.e. successor stacks.  Successor
-- stacks are NOT *additive principal*: `one ⊕ one ≡ two`
-- (definitional), so the inference
-- `α, β < ω-rank ν ⇒ α ⊕ β < ω-rank ν` FAILS at `ν = fin 1`
-- (witness: `α = β = one`, `ω-rank (fin 1) = two`, `one ⊕ one = two`).
--
-- This module ships the limit-shaped replacement `ω^_ : ℕ → Ord`,
-- whose values *are* additive principal: a limit ordinal of finite
-- products `(ω^n) ·ℕ k`.  The classical fact
-- `α, β < ω^(k+1) ⇒ α ⊕ β < ω^(k+1)` is the load-bearing rank-mono
-- lemma for the WfCNF-restricted Buchholz order `_<ᵇ⁻_`; it follows
-- in a later slice that consumes this module's definitions plus
-- left-monotonicity of `_⊕_` (which `Ordinal.Brouwer.Phase13` already
-- supplies on the right but not the left).
--
-- This first slice ships definitions plus the easy facts:
--
--   * `_·ℕ_`              — finite iterated sum (ℕ-exponent product).
--   * `ω^_`               — ω-power; `ω^0 = 1`, `ω^(n+1) = lim (ω^n ·ℕ _)`.
--   * `ω^0≡one`           — definitional sanity check.
--   * `·ℕ-zero`, `·ℕ-suc` — definitional sanity checks.
--   * `one·ℕ≡nat-to-ord`  — `one ·ℕ n ≡ nat-to-ord n`.
--   * `ω^_-pos`           — every `ω^ n` is strictly above zero.
--   * `ω^-strict-mono-suc` — one-step strict monotonicity
--                            `ω^ n <′ ω^ (suc n)`.
--   * `ω^-step`           — weakening: `ω^ n ≤′ ω^ (suc n)`.
--
-- ## Deferred to the next slice
--
--   * General gap strict-mono `m < n → ω^ m <′ ω^ n`.  Needs
--     left-monotonicity of `_⊕_` (`α ≤′ β → α ⊕ γ ≤′ β ⊕ γ`), which
--     `Phase13` does not yet export.
--   * Additive-principal lemma `α, β < ω^(suc n) → α ⊕ β < ω^(suc n)`.
--   * `ω-rank-pow : OmegaIndex → Ord` and the rank-pow consumer
--     ladder that uses ω-powers in place of `nat-to-ord` successor
--     stacks.

module Ordinal.Brouwer.OmegaPow where

open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Product.Base                     using (_,_)
open import Data.Unit.Base                        using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Ordinal.Brouwer                       using
  ( Ord
  ; oz
  ; osuc
  ; olim
  ; one
  ; two
  )
open import Ordinal.Brouwer.Arithmetic            using
  ( _⊕_
  ; nat-to-ord
  )
open import Ordinal.Brouwer.Phase13               using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-zero
  ; ≤′-trans
  ; ≤′-self-osuc
  ; ≤′-weaken-osuc
  ; ⊕-mono-≤-right
  ; ⊕-mono-<-right
  ; ⊕-mono-≤-left
  ; f-in-lim′
  )

open import Data.Nat.Base                         using (_≤_; _<_; z≤n; s≤s)

----------------------------------------------------------------------
-- Finite iterated product (ℕ exponent)
----------------------------------------------------------------------

-- `α ·ℕ n` is α added to itself n times (right-associated via `_⊕_`):
--
--   α ·ℕ 0      = oz
--   α ·ℕ (n+1) = (α ·ℕ n) ⊕ α
--
-- Right-recursive on the ℕ exponent.  Matches the right-recursive
-- shape of `_⊕_` so monotonicity facts compose cleanly.

infixl 7 _·ℕ_

_·ℕ_ : Ord → ℕ → Ord
α ·ℕ zero  = oz
α ·ℕ suc n = (α ·ℕ n) ⊕ α

----------------------------------------------------------------------
-- ω-powers (ω^n)
----------------------------------------------------------------------

-- `ω^ n` is the standard Brouwer-ordinal encoding of ω to the n.
--   * ω^ 0       = 1 = osuc oz       (successor stack of length 1)
--   * ω^ (n+1)   = olim (λ k → (ω^ n) ·ℕ k)
--
-- The successor case is a limit ordinal — exactly the shape that
-- makes ω^(n+1) additive principal.  For `n = 0`, `ω^ 1` is
-- definitionally `olim (λ k → one ·ℕ k)`, which is `≤′`-equivalent
-- to the canonical `Ordinal.Brouwer.ω = olim nat-to-ord` (via
-- `one·ℕ≡nat-to-ord` below; the propositional equality requires
-- function extensionality on the limit's branch, but the bidirected
-- `≤′` containment is funext-free and is what callers need).

ω^_ : ℕ → Ord
ω^ zero  = osuc oz
ω^ suc n = olim (λ k → (ω^ n) ·ℕ k)

----------------------------------------------------------------------
-- Definitional identifications
----------------------------------------------------------------------

ω^0≡one : ω^ zero ≡ one
ω^0≡one = refl

·ℕ-zero : ∀ α → α ·ℕ zero ≡ oz
·ℕ-zero _ = refl

·ℕ-suc : ∀ α n → α ·ℕ suc n ≡ (α ·ℕ n) ⊕ α
·ℕ-suc _ _ = refl

----------------------------------------------------------------------
-- `1 ·ℕ n ≡ nat-to-ord n`
----------------------------------------------------------------------

-- Multiplying `one = osuc oz` by `n` gives back the successor-stack
-- encoding.  Straightforward induction on `n`.  The successor case
-- unfolds:
--
--   one ·ℕ (suc n) = (one ·ℕ n) ⊕ one
--                  = (one ·ℕ n) ⊕ osuc oz
--                  = osuc ((one ·ℕ n) ⊕ oz)
--                  = osuc (one ·ℕ n)
--
-- and recurses via `cong osuc`.

one·ℕ≡nat-to-ord : ∀ n → one ·ℕ n ≡ nat-to-ord n
one·ℕ≡nat-to-ord zero    = refl
one·ℕ≡nat-to-ord (suc n) = cong osuc (one·ℕ≡nat-to-ord n)

----------------------------------------------------------------------
-- `ω^ n` is strictly above zero
----------------------------------------------------------------------

-- Helper used in both `ω^_-pos` and `ω^-strict-mono-suc`: every
-- ordinal whose head admits a successor-step witness lives strictly
-- above `oz` after a left-zero `⊕`.  Right-recursive `⊕` means
-- `oz ⊕ X` reduces clause-by-clause to a shape `≥′ X`.

oz<′oz⊕ : ∀ {X} → oz <′ X → oz <′ oz ⊕ X
oz<′oz⊕ {oz}      ()
oz<′oz⊕ {osuc _}  _       = tt
oz<′oz⊕ {olim g}  (k , q) = k , oz<′oz⊕ {g k} q

-- `oz <′ ω^ n` for every n.
--
-- For `n = 0`, ω^0 = osuc oz, so `oz <′ osuc oz` is `≤′-refl`.
-- For `n = suc k`, ω^(suc k) = olim (λ j → ω^ k ·ℕ j); pick branch 1
-- where `ω^ k ·ℕ 1 = (ω^ k ·ℕ 0) ⊕ ω^ k = oz ⊕ ω^ k`; then
-- `oz <′ oz ⊕ ω^ k` via `oz<′oz⊕` applied to the IH.

ω^_-pos : ∀ n → oz <′ ω^ n
ω^_-pos zero    = tt
ω^_-pos (suc n) = 1 , oz<′oz⊕ {ω^ n} (ω^_-pos n)

----------------------------------------------------------------------
-- `ω^_` is strictly monotone in its ℕ exponent (one-step version)
----------------------------------------------------------------------

-- `ω^ n <′ ω^ (suc n)`.
--
-- Unfolds to `osuc (ω^ n) ≤′ olim (λ k → ω^ n ·ℕ k)`, which by the
-- recursive computation of `_≤′_` is `Σ k. osuc (ω^ n) ≤′ ω^ n ·ℕ k`.
-- Pick `k = 2`; the target becomes `osuc (ω^ n) ≤′ (oz ⊕ ω^ n) ⊕ ω^ n`.
-- Strategy: `ω^ n ≤′ oz ⊕ ω^ n` (left-zero is `≤′`-trivial on
-- right-recursive ⊕, lemma below), bump to `osuc (oz ⊕ ω^ n)` via
-- `≤′-weaken-osuc`, then a right-mono step using `ω^_-pos n` lifts
-- to `(oz ⊕ ω^ n) ⊕ ω^ n`.

-- `X ≤′ oz ⊕ X`: structural recursion on `X`.  Right-recursive `_⊕_`
-- means each `X` shape reduces to a clause of `_≤′_`'s second
-- argument computation; the `osuc` case collapses to identity per
-- `osuc-mono-≤′`'s recursive shape, and the `olim` case threads
-- through right-mono of `⊕` plus `f-in-lim′`.

X≤′oz⊕X : ∀ {X} → X ≤′ oz ⊕ X
X≤′oz⊕X {oz}      = tt
X≤′oz⊕X {osuc X'} = X≤′oz⊕X {X'}
X≤′oz⊕X {olim g}  = λ k →
  ≤′-trans {g k} {oz ⊕ g k} {oz ⊕ olim g}
    (X≤′oz⊕X {g k})
    (⊕-mono-≤-right {oz} {g k} {olim g} (f-in-lim′ g k))

ω^-strict-mono-suc : ∀ n → ω^ n <′ ω^ (suc n)
ω^-strict-mono-suc n = 2 , step
  where
  -- Show `osuc (ω^ n) ≤′ (oz ⊕ ω^ n) ⊕ ω^ n` (which is `ω^ n ·ℕ 2`).
  -- Step 1 reduces under `_≤′_`'s `osuc/osuc` clause:
  --   osuc (ω^ n) ≤′ osuc (oz ⊕ ω^ n)  ≡  ω^ n ≤′ oz ⊕ ω^ n
  -- Step 2 uses right-mono of `⊕` and the right-unit of `⊕`:
  --   (oz ⊕ ω^ n) ⊕ oz <′ (oz ⊕ ω^ n) ⊕ ω^ n   -- from oz <′ ω^ n
  -- and `α ⊕ oz = α` reduces the LHS to `oz ⊕ ω^ n`, giving
  --   osuc (oz ⊕ ω^ n) ≤′ (oz ⊕ ω^ n) ⊕ ω^ n.
  step : osuc (ω^ n) ≤′ (oz ⊕ ω^ n) ⊕ ω^ n
  step = ≤′-trans
           {osuc (ω^ n)} {osuc (oz ⊕ ω^ n)} {(oz ⊕ ω^ n) ⊕ ω^ n}
           (X≤′oz⊕X {ω^ n})
           (⊕-mono-<-right {oz ⊕ ω^ n} {oz} {ω^ n} (ω^_-pos n))

----------------------------------------------------------------------
-- Weakening: `ω^ n ≤′ ω^ (suc n)`
----------------------------------------------------------------------

-- Direct corollary of `ω^-strict-mono-suc` via `≤′-self-osuc` and
-- transitivity: `ω^ n ≤′ osuc (ω^ n) ≤′ ω^ (suc n)`.

ω^-step : ∀ n → ω^ n ≤′ ω^ (suc n)
ω^-step n =
  ≤′-trans {ω^ n} {osuc (ω^ n)} {ω^ (suc n)}
    (≤′-self-osuc (ω^ n))
    (ω^-strict-mono-suc n)

----------------------------------------------------------------------
-- Left-monotonicity of `_·ℕ_` in its Ord argument
----------------------------------------------------------------------

-- `α ≤′ β → α ·ℕ k ≤′ β ·ℕ k` by induction on the ℕ exponent.
-- The successor case combines left- and right-mono of `_⊕_`:
--
--   α ·ℕ (suc k) = (α ·ℕ k) ⊕ α
--   β ·ℕ (suc k) = (β ·ℕ k) ⊕ β
--
--   (α ·ℕ k) ⊕ α  ≤′  (β ·ℕ k) ⊕ α     -- ⊕-mono-≤-left + IH
--                ≤′  (β ·ℕ k) ⊕ β     -- ⊕-mono-≤-right + hyp

·ℕ-mono-≤-left : ∀ {α β} k → α ≤′ β → α ·ℕ k ≤′ β ·ℕ k
·ℕ-mono-≤-left          zero    _ = tt
·ℕ-mono-≤-left {α} {β} (suc k)  p =
  ≤′-trans {(α ·ℕ k) ⊕ α} {(β ·ℕ k) ⊕ α} {(β ·ℕ k) ⊕ β}
    (⊕-mono-≤-left {α ·ℕ k} {β ·ℕ k} {α} (·ℕ-mono-≤-left k p))
    (⊕-mono-≤-right {β ·ℕ k} {α} {β} p)

----------------------------------------------------------------------
-- Gap-monotonicity of `ω^_` (non-strict and strict)
----------------------------------------------------------------------

-- `ω^ 0 ≤′ ω^ n` for any n.  Induction on n; chain `ω^-step` at each
-- step.

ω^-from-zero : ∀ n → ω^ zero ≤′ ω^ n
ω^-from-zero zero    = tt
ω^-from-zero (suc n) =
  ≤′-trans {ω^ zero} {ω^ n} {ω^ (suc n)}
    (ω^-from-zero n)
    (ω^-step n)

-- `ω^ (suc m) ≤′ ω^ (suc n)` from `ω^ m ≤′ ω^ n`.  Both sides are
-- limits.  By the recursive `_≤′_` clause for `olim ≤′ olim`,
-- suffices to show for each branch `k`: `ω^ m ·ℕ k ≤′ ω^ (suc n)`.
-- Route through `ω^ n ·ℕ k`: `ω^ m ·ℕ k ≤′ ω^ n ·ℕ k ≤′ ω^ (suc n)`.

ω^-mono-≤-suc-suc : ∀ m n → ω^ m ≤′ ω^ n → ω^ (suc m) ≤′ ω^ (suc n)
ω^-mono-≤-suc-suc m n p = λ k →
  ≤′-trans {ω^ m ·ℕ k} {ω^ n ·ℕ k} {ω^ (suc n)}
    (·ℕ-mono-≤-left k p)
    (f-in-lim′ (λ j → ω^ n ·ℕ j) k)

-- General gap monotonicity: `m ≤ n → ω^ m ≤′ ω^ n`.  Induction on the
-- `≤` derivation; the `z≤n` case dispatches to `ω^-from-zero`, the
-- `s≤s` case recurses and lifts via `ω^-mono-≤-suc-suc`.

ω^-mono-≤ : ∀ {m n} → m ≤ n → ω^ m ≤′ ω^ n
ω^-mono-≤ {.0}     {n}     z≤n     = ω^-from-zero n
ω^-mono-≤ {suc m'} {suc n'} (s≤s p) = ω^-mono-≤-suc-suc m' n' (ω^-mono-≤ p)

-- Strict gap monotonicity: `m < n → ω^ m <′ ω^ n`.  Note `_<_` on ℕ
-- is `suc m ≤ n`, so `p : m < n` gives `ω^ (suc m) ≤′ ω^ n` via
-- `ω^-mono-≤`.  Combined with the one-step strict `ω^-strict-mono-suc`
-- this lifts to a strict bound on ω^ m.

ω^-strict-mono : ∀ {m n} → m < n → ω^ m <′ ω^ n
ω^-strict-mono {m} {n} p =
  ≤′-trans {osuc (ω^ m)} {ω^ (suc m)} {ω^ n}
    (ω^-strict-mono-suc m)
    (ω^-mono-≤ p)
