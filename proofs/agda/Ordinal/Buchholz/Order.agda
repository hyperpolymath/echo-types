{-# OPTIONS --safe --without-K #-}

-- Stage WF-0 of the Buchholz well-foundedness workstream
-- (docs/buchholz-plan.adoc, follow-up to E5–E7).
--
-- Defines the binary strict order `_<ᵇ_` on Buchholz terms (BT) and
-- establishes irreflexivity and transitivity across the cases that
-- the term heads naturally determine. Totality is *not* proved here
-- and neither is well-foundedness; those are WF-1 and WF-2.
--
-- Scope of this module. The constructors below cover the head
-- pairs marked ✓ in the matrix, with the lex-on-left-summand case
-- for bplus and the lex-on-Ω-index case for bpsi:
--
--   head of x \ head of y │ bzero │ bOmega │ bplus │ bpsi
--   ──────────────────────┼───────┼────────┼───────┼──────
--   bzero                 │   –   │   ✓    │   ✓   │  ✓
--   bOmega                │       │   ✓    │   ✓   │  ✓ (when μ <Ω ν)
--   bplus                 │       │        │   ✓   │
--   bpsi                  │       │   ✓    │   ✓   │  ✓ (when μ <Ω ν)
--
-- Open cases (no constructor yet; must be discharged in follow-ups
-- before `<ᵇ`-totality and well-foundedness can land):
--
--   * bplus vs bOmega (general case) — currently only the top-marker
--     bridge `<ᵇ-+ω` is admitted.
--   * bplus vs bpsi (general case) — currently only the top-marker
--     bridge `<ᵇ-+ψω` is admitted.
--   * Two same-binder sub-cases whose natural shapes run into Agda
--     2.6.3's `--without-K` restriction on reflexive-equation
--     elimination and are deferred pending a K-free reformulation:
--       - bpsi ν α <ᵇ bpsi ν β with α <ᵇ β (same Ω-index ν).
--       - bplus x y₂ <ᵇ bplus x z₂ with y₂ <ᵇ z₂ (same left summand).
--     In both cases the constructor shares a binder between the two
--     sides of `<ᵇ`, which `<ᵇ-irrefl`'s pattern unification cannot
--     reduce. A rank-embedding or heterogeneous-equality formulation
--     is the next follow-up on top of WF-0.

module Ordinal.Buchholz.Order where

open import Data.Empty using (⊥)

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

data _<ᵇ_ : BT → BT → Set where
  -- bzero is minimum against every non-bzero head.
  <ᵇ-0-Ω : ∀ {μ}   → bzero <ᵇ bOmega μ
  <ᵇ-0-+ : ∀ {x y} → bzero <ᵇ bplus x y
  <ᵇ-0-ψ : ∀ {ν α} → bzero <ᵇ bpsi ν α

  -- bOmega ordering by Ω-index.
  <ᵇ-ΩΩ  : ∀ {μ ν} → μ <Ω ν → bOmega μ <ᵇ bOmega ν

  -- Ω_μ < ψ_ν(α) whenever μ <Ω ν. This is the admissibility side:
  -- ψ-terms at higher index dominate Ω-markers at lower index.
  <ᵇ-Ωψ  : ∀ {μ ν α} → μ <Ω ν → bOmega μ <ᵇ bpsi ν α

  -- bpsi comparison by Ω-index only. The same-index sub-case (lex on
  -- the ψ-argument) is deferred pending a K-free formulation. The
  -- ψ→Ω bridge for ν ≤Ω μ is admitted separately as `<ᵇ-ψΩ≤`.
  <ᵇ-ψΩ  : ∀ {μ ν α β} → μ <Ω ν → bpsi μ α <ᵇ bpsi ν β
  <ᵇ-ψΩ≤ : ∀ {ν μ α}   → ν ≤Ω μ → bpsi ν α <ᵇ bOmega μ

  -- Left-summand bridge into additive terms.
  <ᵇ-Ω+  : ∀ {μ x y}    → bOmega μ <ᵇ x → bOmega μ <ᵇ bplus x y
  <ᵇ-ψ+  : ∀ {ν α x y}  → bpsi ν α <ᵇ x → bpsi ν α <ᵇ bplus x y

  -- bplus comparison by the left summand. The same-left sub-case
  -- (compare right summands when lefts agree) is deferred for the
  -- same `--without-K` reason as `<ᵇ-ψα` above: its natural shape
  -- `bplus x y₂ <ᵇ bplus x z₂` shares the binder `x` on both sides.
  <ᵇ-+ω  : ∀ {x y}     → x <ᵇ bOmega ω → bplus x y <ᵇ bOmega ω
  <ᵇ-+ψω : ∀ {x y α}   → x <ᵇ bpsi ω α → bplus x y <ᵇ bpsi ω α
  <ᵇ-+1  : ∀ {x₁ x₂ y₁ y₂} → x₁ <ᵇ y₁ → bplus x₁ x₂ <ᵇ bplus y₁ y₂

infix 4 _<ᵇ_

----------------------------------------------------------------------------
-- Irreflexivity
----------------------------------------------------------------------------

-- Every constructor of `_<ᵇ_` with equal LHS and RHS reduces to a
-- witness of irreflexivity at a strictly smaller structure (either
-- `_<Ω_` or `_<ᵇ_` on a subterm). Explicit binds on the `{x}` ensure
-- the K-free unifier does not get stuck on reflexive equations at the
-- shared Ω-index of `<ᵇ-ψα`.

<ᵇ-irrefl : ∀ {x} → x <ᵇ x → ⊥
<ᵇ-irrefl (<ᵇ-ΩΩ μ<μ)  = <Ω-irrefl μ<μ
<ᵇ-irrefl (<ᵇ-ψΩ μ<μ)  = <Ω-irrefl μ<μ
<ᵇ-irrefl (<ᵇ-+1 x<x)  = <ᵇ-irrefl x<x

----------------------------------------------------------------------------
-- Transitivity
----------------------------------------------------------------------------

-- Case analysis on the two ordering derivations, recursing on
-- `_<Ω_` or `_<ᵇ_` subterms as needed. Covers every pair of
-- constructors whose middle term has a compatible head; pairs with
-- incompatible middle heads are absurd by construction (no
-- constructor witnesses them).

<ᵇ-trans : ∀ {x y z} → x <ᵇ y → y <ᵇ z → x <ᵇ z
-- Left leg: <ᵇ-0-Ω (x = bzero, y = bOmega _)
<ᵇ-trans <ᵇ-0-Ω       (<ᵇ-ΩΩ _)            = <ᵇ-0-Ω
<ᵇ-trans <ᵇ-0-Ω       (<ᵇ-Ωψ _)            = <ᵇ-0-ψ
<ᵇ-trans <ᵇ-0-Ω       (<ᵇ-Ω+ _)            = <ᵇ-0-+
-- Left leg: <ᵇ-0-+ (x = bzero, y = bplus _ _)
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+1 _)            = <ᵇ-0-+
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+ω _)            = <ᵇ-0-Ω
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+ψω _)           = <ᵇ-0-ψ
-- Left leg: <ᵇ-0-ψ (x = bzero, y = bpsi _ _)
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψΩ _)            = <ᵇ-0-ψ
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψ+ _)            = <ᵇ-0-+
-- Left leg: <ᵇ-ΩΩ (x = bOmega _, y = bOmega _)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-ΩΩ q)            = <ᵇ-ΩΩ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-Ωψ q)            = <ᵇ-Ωψ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-Ω+ q)            = <ᵇ-Ω+ (<ᵇ-trans (<ᵇ-ΩΩ p) q)
-- Left leg: <ᵇ-Ωψ (x = bOmega _, y = bpsi _ _)
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψΩ q)            = <ᵇ-Ωψ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψ+ q)            = <ᵇ-Ω+ (<ᵇ-trans (<ᵇ-Ωψ p) q)
-- Left leg: <ᵇ-ψΩ (x = bpsi _ _, y = bpsi _ _)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψΩ q)            = <ᵇ-ψΩ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ψΩ≤ (≤Ω-trans (<Ω→≤Ω p) q)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψ+ q)            = <ᵇ-ψ+ (<ᵇ-trans (<ᵇ-ψΩ p) q)
-- Left leg: <ᵇ-ψΩ≤ (x = bpsi _ _, y = bOmega _)
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-ΩΩ q)            = <ᵇ-ψΩ≤ (≤Ω-trans p (<Ω→≤Ω q))
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-Ωψ q)            = <ᵇ-ψΩ (≤Ω-<Ω-trans p q)
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-Ω+ q)            = <ᵇ-ψ+ (<ᵇ-trans (<ᵇ-ψΩ≤ p) q)
-- Left leg: <ᵇ-+1 (x = bplus _ _, y = bplus _ _)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+1 q)            = <ᵇ-+1 (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+ω q)            = <ᵇ-+ω (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+ψω q)           = <ᵇ-+ψω (<ᵇ-trans p q)
-- Left leg: <ᵇ-Ω+ (x = bOmega _, y = bplus _ _)
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+1 q)            = <ᵇ-Ω+ (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+ω q)            = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+ψω q)           = <ᵇ-trans p q
-- Left leg: <ᵇ-ψ+ (x = bpsi _ _, y = bplus _ _)
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+1 q)            = <ᵇ-ψ+ (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+ω q)            = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+ψω q)           = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-+ω p)    (<ᵇ-Ω+ q)            = <ᵇ-+1 (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+ψω p)   (<ᵇ-ψ+ q)            = <ᵇ-+1 (<ᵇ-trans p q)
-- Left leg: <ᵇ-+ψω (x = bplus _ _, y = bpsi ω _)
<ᵇ-trans (<ᵇ-+ψω p)   (<ᵇ-ψΩ≤ ω≤ω)         = <ᵇ-+ω (<ᵇ-trans p (<ᵇ-ψΩ≤ ω≤ω))
-- Right leg: <ᵇ-ψΩ≤ (y = bpsi _ _, z = bOmega _)
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψΩ≤ _)           = <ᵇ-0-Ω
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ΩΩ (<Ω-≤Ω-trans p q)

----------------------------------------------------------------------------
-- WF-2 open-case inversions (Ω vs +)
----------------------------------------------------------------------------

-- The Ω→+ bridge is admitted (`<ᵇ-Ω+`), while the non-top
-- bplus→Ω case remains deferred.

<ᵇ-inv-Ω+ : ∀ {μ x y} → bOmega μ <ᵇ bplus x y → bOmega μ <ᵇ x
<ᵇ-inv-Ω+ (<ᵇ-Ω+ Ω<x) = Ω<x

<ᵇ-inv-+Ωfin : ∀ {x y n} → bplus x y <ᵇ bOmega (fin n) → ⊥
<ᵇ-inv-+Ωfin ()

-- Inversion for the admitted top-marker bridge.
<ᵇ-inv-+Ωω : ∀ {x y} → bplus x y <ᵇ bOmega ω → x <ᵇ bOmega ω
<ᵇ-inv-+Ωω (<ᵇ-+ω x<ω) = x<ω

----------------------------------------------------------------------------
-- WF-2 open-case inversions (ψ vs +)
----------------------------------------------------------------------------

-- The ψ→+ bridge is admitted (`<ᵇ-ψ+`), while the non-top
-- bplus→ψ case remains deferred.

<ᵇ-inv-ψ+ : ∀ {μ α x y} → bpsi μ α <ᵇ bplus x y → bpsi μ α <ᵇ x
<ᵇ-inv-ψ+ (<ᵇ-ψ+ ψ<x) = ψ<x

<ᵇ-inv-+ψfin : ∀ {x y n α} → bplus x y <ᵇ bpsi (fin n) α → ⊥
<ᵇ-inv-+ψfin ()

-- Inversion for the admitted top-marker bridge.
<ᵇ-inv-+ψω : ∀ {x y α} → bplus x y <ᵇ bpsi ω α → x <ᵇ bpsi ω α
<ᵇ-inv-+ψω (<ᵇ-+ψω x<ψω) = x<ψω

----------------------------------------------------------------------------
-- Strict-below-ψ examples, for downstream ordering checks
----------------------------------------------------------------------------

-- These use the pinned `Omega*` constants from OmegaMarkers to keep
-- the Buchholz example terms in a strict chain: bzero <ᵇ Ω₀ <ᵇ Ω₁
-- <ᵇ Ω_ω <ᵇ ψ_ω(bzero). The last strict inequality uses the cross-
-- constructor <ᵇ-Ωψ since ω <Ω ω is absent (ω is top).

open import Ordinal.OmegaMarkers using
  ( Omega0
  ; Omega1
  ; Omegaω
  ; Omega0<Omega1
  ; Omega0<Omegaω
  ; Omega1<Omegaω
  )

bzero<Ω0 : bzero <ᵇ bOmega Omega0
bzero<Ω0 = <ᵇ-0-Ω

Ω0<Ω1 : bOmega Omega0 <ᵇ bOmega Omega1
Ω0<Ω1 = <ᵇ-ΩΩ Omega0<Omega1

Ω1<Ωω : bOmega Omega1 <ᵇ bOmega Omegaω
Ω1<Ωω = <ᵇ-ΩΩ Omega1<Omegaω

Ω0<ψ1-zero : bOmega Omega0 <ᵇ bpsi Omega1 bzero
Ω0<ψ1-zero = <ᵇ-Ωψ Omega0<Omega1
