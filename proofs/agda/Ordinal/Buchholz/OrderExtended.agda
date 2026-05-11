{-# OPTIONS --safe --without-K #-}

-- Buchholz extended order — shared-binder lex cases.
--
-- This module sits on top of `Ordinal.Buchholz.Order._<ᵇ_` and adds
-- the two shared-binder lex constructors that the comment block at
-- the top of `Order.agda` flagged as "the next follow-up on top of
-- WF-0":
--
--   * `<ᵇ⁺-ψα` : `bpsi ν α <ᵇ⁺ bpsi ν β` whenever `α <ᵇ β`
--                (lex on the ψ-argument, same Ω-index).
--   * `<ᵇ⁺-+2` : `bplus x y₁ <ᵇ⁺ bplus x y₂` whenever `y₁ <ᵇ y₂`
--                (lex on the right summand, same left summand).
--
-- Why a separate relation `_<ᵇ⁺_` instead of adding to `_<ᵇ_`.
-- Adding the constructors directly to `_<ᵇ_` would break the
-- existing `Ordinal.Buchholz.WellFounded.wf-<ᵇ` proof — the
-- per-Ω-index bundle that proof uses recurses on `Acc _<Ω_ μ` and
-- has no Acc on the ψ-argument or the right summand to thread
-- through the new shared-binder cases. The bundle would have to
-- expand to `Acc _<Ω_ μ × Acc _<ᵇ_ α` (and a sibling pair for
-- bplus), with `wf-<ᵇ` mutual with the bundle to supply the
-- `Acc _<ᵇ_ α` side via BT structural recursion. That restructure
-- compiles in scope but Agda's termination checker cannot verify
-- the cycle through `wf-<ᵇ` calls inside `pred-bpsi-from`. We keep
-- the constructor and well-foundedness workstreams separated here
-- so the WF gap is named explicitly.
--
-- K-restriction handling. Both new constructors carry an explicit
-- equality witness for the shared binder rather than letting the
-- shape `bpsi ν α <ᵇ bpsi ν β` (or `bplus x y₁ <ᵇ bplus x y₂`)
-- bind `ν` (or `x`) on both sides:
--
--   <ᵇ⁺-ψα : ∀ {ν₁ ν₂ α β}    → ν₁ ≡ ν₂ → α <ᵇ β → bpsi ν₁ α <ᵇ⁺ bpsi ν₂ β
--   <ᵇ⁺-+2 : ∀ {x₁ x₂ y₁ y₂}  → x₁ ≡ y₁ → x₂ <ᵇ y₂ → bplus x₁ x₂ <ᵇ⁺ bplus y₁ y₂
--
-- The implicit binders are pairwise distinct, so when the
-- irreflexivity proof unifies the LHS and RHS of `_<ᵇ⁺_` to a
-- shared carrier, no reflexive `ν = ν` (or `x = x`) equation is
-- forced through. The equality argument is left as a held hypothesis
-- and not pattern-matched on `refl` in irrefl (which would itself
-- trigger the K-restriction once the carrier identification has
-- fired); we thread it as `_` and use the strict-decrease witness
-- directly.
--
-- Status (2026-04-28):
--
--   * `<ᵇ⁺` includes every `<ᵇ` constructor verbatim plus the two
--     shared-binder cases.
--   * `<ᵇ⁺-irrefl`, `<ᵇ⁺-trans` are proved.
--   * Well-foundedness for `_<ᵇ⁺_` is OPEN — see
--     `docs/echo-types/buchholz-extended-wf.md` for the design
--     direction (single-mutual `wf` with `Acc _<ᵇ_ α` threaded
--     through a widened bundle, or rank-embedding via Brouwer
--     ordinals).

module Ordinal.Buchholz.OrderExtended where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; _≤Ω_
  ; _<Ω_
  ; ω
  ; ω≤ω
  ; fin
  ; <Ω-irrefl
  ; <Ω-trans
  ; <Ω→≤Ω
  ; ≤Ω-trans
  ; ≤Ω-<Ω-trans
  ; <Ω-≤Ω-trans
  )
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order using
  ( _<ᵇ_
  ; <ᵇ-0-Ω; <ᵇ-0-+; <ᵇ-0-ψ
  ; <ᵇ-ΩΩ; <ᵇ-Ωψ
  ; <ᵇ-ψΩ; <ᵇ-ψΩ≤
  ; <ᵇ-Ω+; <ᵇ-ψ+
  ; <ᵇ-+Ω; <ᵇ-+ψ
  ; <ᵇ-+1
  ; <ᵇ-irrefl; <ᵇ-trans
  )

----------------------------------------------------------------------
-- The extended order
----------------------------------------------------------------------

data _<ᵇ⁺_ : BT → BT → Set where
  -- Lift every constructor of `_<ᵇ_` verbatim.
  <ᵇ⁺-base : ∀ {x y} → x <ᵇ y → x <ᵇ⁺ y

  -- Shared-binder lex cases. The equality witness keeps all four
  -- implicits pairwise distinct so the K-free unifier never has to
  -- eliminate a reflexive `ν = ν` (or `x = x`) equation on its own.
  <ᵇ⁺-ψα : ∀ {ν₁ ν₂ α β}   → ν₁ ≡ ν₂ → α <ᵇ β → bpsi ν₁ α <ᵇ⁺ bpsi ν₂ β
  <ᵇ⁺-+2 : ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ <ᵇ y₂ → bplus x₁ x₂ <ᵇ⁺ bplus y₁ y₂

infix 4 _<ᵇ⁺_

----------------------------------------------------------------------
-- Irreflexivity
----------------------------------------------------------------------

-- The lifted `_<ᵇ_` part discharges via the existing `<ᵇ-irrefl`.
-- The two shared-binder cases recurse into `<ᵇ-irrefl` on the
-- strict-decrease witness; the equality argument is discarded
-- (matching it on `refl` would re-trigger the K-restricted
-- reflexive elimination once the LHS and RHS of `<ᵇ⁺` have
-- already been unified to a common carrier).

<ᵇ⁺-irrefl : ∀ {x} → x <ᵇ⁺ x → ⊥
<ᵇ⁺-irrefl (<ᵇ⁺-base x<x) = <ᵇ-irrefl x<x
<ᵇ⁺-irrefl (<ᵇ⁺-ψα _ α<α) = <ᵇ-irrefl α<α
<ᵇ⁺-irrefl (<ᵇ⁺-+2 _ y<y) = <ᵇ-irrefl y<y

----------------------------------------------------------------------
-- Transitivity (via four extension helpers)
----------------------------------------------------------------------

-- Helper extending the RHS of a base witness from `bpsi ν α` to
-- `bpsi ν β` when α <ᵇ β. The base constructors that put bpsi on
-- the RHS (<ᵇ-0-ψ, <ᵇ-Ωψ, <ᵇ-ψΩ, <ᵇ-+ψ) do not constrain the
-- ψ-argument α, so we can swap it for β by re-applying the
-- constructor at β.
private
  bpsi-extend-rhs : ∀ {ν α β x} → α <ᵇ β → x <ᵇ bpsi ν α → x <ᵇ bpsi ν β
  bpsi-extend-rhs _ <ᵇ-0-ψ        = <ᵇ-0-ψ
  bpsi-extend-rhs _ (<ᵇ-Ωψ μ<ν)   = <ᵇ-Ωψ μ<ν
  bpsi-extend-rhs _ (<ᵇ-ψΩ μ<ν)   = <ᵇ-ψΩ μ<ν
  bpsi-extend-rhs p (<ᵇ-+ψ q)     = <ᵇ-+ψ (bpsi-extend-rhs p q)

-- Helper extending the LHS of a base witness from `bpsi ν β` to
-- `bpsi ν α` when α <ᵇ β. The base constructors that put bpsi on
-- the LHS (<ᵇ-ψΩ, <ᵇ-ψΩ≤, <ᵇ-ψ+) do not constrain the ψ-argument
-- of the LHS, so we can swap β for α by re-applying.
  bpsi-extend-lhs : ∀ {ν α β z} → α <ᵇ β → bpsi ν β <ᵇ z → bpsi ν α <ᵇ z
  bpsi-extend-lhs _ (<ᵇ-ψΩ μ<ν)   = <ᵇ-ψΩ μ<ν
  bpsi-extend-lhs _ (<ᵇ-ψΩ≤ ν≤μ)  = <ᵇ-ψΩ≤ ν≤μ
  bpsi-extend-lhs p (<ᵇ-ψ+ q)     = <ᵇ-ψ+ (bpsi-extend-lhs p q)

-- Same helpers for bplus. The base constructors that put bplus on
-- one side leave the right summand of the bplus on that side
-- unconstrained, so we can swap it freely.
  bplus-extend-rhs : ∀ {x y z w} → y <ᵇ z → w <ᵇ bplus x y → w <ᵇ bplus x z
  bplus-extend-rhs _ <ᵇ-0-+      = <ᵇ-0-+
  bplus-extend-rhs _ (<ᵇ-Ω+ q)   = <ᵇ-Ω+ q
  bplus-extend-rhs _ (<ᵇ-ψ+ q)   = <ᵇ-ψ+ q
  bplus-extend-rhs _ (<ᵇ-+1 q)   = <ᵇ-+1 q

  bplus-extend-lhs : ∀ {x y z w} → y <ᵇ z → bplus x z <ᵇ w → bplus x y <ᵇ w
  bplus-extend-lhs _ (<ᵇ-+Ω q)   = <ᵇ-+Ω q
  bplus-extend-lhs _ (<ᵇ-+ψ q)   = <ᵇ-+ψ q
  bplus-extend-lhs _ (<ᵇ-+1 q)   = <ᵇ-+1 q

<ᵇ⁺-trans : ∀ {x y z} → x <ᵇ⁺ y → y <ᵇ⁺ z → x <ᵇ⁺ z
-- Both legs in the base relation: route through `<ᵇ-trans`.
<ᵇ⁺-trans (<ᵇ⁺-base p) (<ᵇ⁺-base q) = <ᵇ⁺-base (<ᵇ-trans p q)
-- Left leg base, right leg shared-ψ: extend p's RHS from bpsi ν α
-- to bpsi ν β via `bpsi-extend-rhs`.
<ᵇ⁺-trans (<ᵇ⁺-base p) (<ᵇ⁺-ψα refl q) = <ᵇ⁺-base (bpsi-extend-rhs q p)
-- Left leg base, right leg shared-+2: extend p's RHS from bplus x y
-- to bplus x z via `bplus-extend-rhs`.
<ᵇ⁺-trans (<ᵇ⁺-base p) (<ᵇ⁺-+2 refl q) = <ᵇ⁺-base (bplus-extend-rhs q p)
-- Left leg shared-ψ, right leg base: extend q's LHS from bpsi ν β
-- to bpsi ν α.
<ᵇ⁺-trans (<ᵇ⁺-ψα refl p) (<ᵇ⁺-base q) = <ᵇ⁺-base (bpsi-extend-lhs p q)
-- Left leg shared-+2, right leg base: extend q's LHS from bplus x z
-- to bplus x y.
<ᵇ⁺-trans (<ᵇ⁺-+2 refl p) (<ᵇ⁺-base q) = <ᵇ⁺-base (bplus-extend-lhs p q)
-- Both legs shared-ψ at the same Ω-index: chain the strict-decrease.
<ᵇ⁺-trans (<ᵇ⁺-ψα refl p) (<ᵇ⁺-ψα refl q) = <ᵇ⁺-ψα refl (<ᵇ-trans p q)
-- Both legs shared-+2 at the same left summand: chain the right strict-decrease.
<ᵇ⁺-trans (<ᵇ⁺-+2 refl p) (<ᵇ⁺-+2 refl q) = <ᵇ⁺-+2 refl (<ᵇ-trans p q)

----------------------------------------------------------------------
-- Convenience wrappers for the new shared-binder lex cases.
----------------------------------------------------------------------

-- Shared Ω-index ψ lex: `bpsi ν α <ᵇ⁺ bpsi ν β` whenever `α <ᵇ β`.
-- Use this rather than building `<ᵇ⁺-ψα refl ...` directly when
-- the Ω-index is concretely the same.

<ᵇ⁺-ψα-refl : ∀ {ν α β} → α <ᵇ β → bpsi ν α <ᵇ⁺ bpsi ν β
<ᵇ⁺-ψα-refl p = <ᵇ⁺-ψα refl p

-- Shared left-summand bplus lex.

<ᵇ⁺-+2-refl : ∀ {x y₁ y₂} → y₁ <ᵇ y₂ → bplus x y₁ <ᵇ⁺ bplus x y₂
<ᵇ⁺-+2-refl q = <ᵇ⁺-+2 refl q
