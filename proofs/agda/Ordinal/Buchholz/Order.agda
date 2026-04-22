{-# OPTIONS --safe --without-K #-}

-- Stage WF-0 of the Buchholz well-foundedness workstream
-- (docs/buchholz-plan.adoc, follow-up to E5–E7).
--
-- Defines the binary strict order `_<ᵇ_` on Buchholz terms (BT) and
-- establishes irreflexivity and transitivity across the cases that
-- the term heads naturally determine. Totality is *not* proved here
-- and neither is well-foundedness; those are WF-1 and WF-2.
--
-- Scope of this module. The 7 constructors below cover the head
-- pairs marked ✓ in the matrix, with the lex-on-left-summand case
-- for bplus and the lex-on-Ω-index case for bpsi:
--
--   head of x \ head of y │ bzero │ bOmega │ bplus │ bpsi
--   ──────────────────────┼───────┼────────┼───────┼──────
--   bzero                 │   –   │   ✓    │   ✓   │  ✓
--   bOmega                │       │   ✓    │       │  ✓ (when μ <Ω ν)
--   bplus                 │       │        │   ✓   │
--   bpsi                  │       │   ✓    │       │  ✓ (when μ <Ω ν)
--
-- Open cases (no constructor yet; must be discharged in follow-ups
-- before `<ᵇ`-totality and well-foundedness can land):
--
--   * bOmega vs bplus (either direction) — requires a comparison
--     between atomic heads and additive normal forms.
--   * bpsi vs bplus (either direction) — same reason, mediated by
--     the leading bpsi summand of a bplus in CNF.
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
  -- ψ-terms at higher index dominate Ω-markers at lower index. The
  -- reverse direction (bpsi ν α <ᵇ bOmega μ with ν ≤Ω μ) is deferred.
  <ᵇ-Ωψ  : ∀ {μ ν α} → μ <Ω ν → bOmega μ <ᵇ bpsi ν α

  -- bpsi comparison by Ω-index only. The same-index sub-case (lex on
  -- the ψ-argument) is deferred pending a K-free formulation.
  <ᵇ-ψΩ  : ∀ {μ ν α β} → μ <Ω ν → bpsi μ α <ᵇ bpsi ν β
  <ᵇ-ψΩ≤ : ∀ {ν μ α}   → ν ≤Ω μ → bpsi ν α <ᵇ bOmega μ

  -- bplus comparison by the left summand. The same-left sub-case
  -- (compare right summands when lefts agree) is deferred for the
  -- same `--without-K` reason as `<ᵇ-ψα` above: its natural shape
  -- `bplus x y₂ <ᵇ bplus x z₂` shares the binder `x` on both sides.
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
-- Left leg: <ᵇ-0-+ (x = bzero, y = bplus _ _)
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+1 _)            = <ᵇ-0-+
-- Left leg: <ᵇ-0-ψ (x = bzero, y = bpsi _ _)
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψΩ _)            = <ᵇ-0-ψ
-- Left leg: <ᵇ-ΩΩ (x = bOmega _, y = bOmega _)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-ΩΩ q)            = <ᵇ-ΩΩ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-Ωψ q)            = <ᵇ-Ωψ (<Ω-trans p q)
-- Left leg: <ᵇ-Ωψ (x = bOmega _, y = bpsi _ _)
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψΩ q)            = <ᵇ-Ωψ (<Ω-trans p q)
-- Left leg: <ᵇ-ψΩ (x = bpsi _ _, y = bpsi _ _)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψΩ q)            = <ᵇ-ψΩ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ψΩ≤ (≤Ω-trans (<Ω→≤Ω p) q)
-- Left leg: <ᵇ-ψΩ≤ (x = bpsi _ _, y = bOmega _)
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-ΩΩ q)            = <ᵇ-ψΩ≤ (≤Ω-trans p (<Ω→≤Ω q))
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-Ωψ q)            = <ᵇ-ψΩ (≤Ω-<Ω-trans p q)
-- Left leg: <ᵇ-+1 (x = bplus _ _, y = bplus _ _)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+1 q)            = <ᵇ-+1 (<ᵇ-trans p q)
-- Right leg: <ᵇ-ψΩ≤ (y = bpsi _ _, z = bOmega _)
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψΩ≤ _)           = <ᵇ-0-Ω
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ΩΩ (<Ω-≤Ω-trans p q)

----------------------------------------------------------------------------
-- WF-2 open-case inversions (Ω vs +)
----------------------------------------------------------------------------

-- The current 7-constructor core has no witness for either direction.
-- These inversion lemmas pin that fact explicitly for downstream case
-- splits while the comparison rule is still deferred.

<ᵇ-inv-Ω+ : ∀ {μ x y} → bOmega μ <ᵇ bplus x y → ⊥
<ᵇ-inv-Ω+ ()

<ᵇ-inv-+Ω : ∀ {x y μ} → bplus x y <ᵇ bOmega μ → ⊥
<ᵇ-inv-+Ω ()

----------------------------------------------------------------------------
-- WF-2 open-case inversions (ψ vs +)
----------------------------------------------------------------------------

-- Like Ω-vs-+, these comparisons are still deferred and currently
-- have no constructors in either direction.

<ᵇ-inv-ψ+ : ∀ {μ α x y} → bpsi μ α <ᵇ bplus x y → ⊥
<ᵇ-inv-ψ+ ()

<ᵇ-inv-+ψ : ∀ {x y μ α} → bplus x y <ᵇ bpsi μ α → ⊥
<ᵇ-inv-+ψ ()

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
