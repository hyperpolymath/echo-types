{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Earn-back of proof-debt ledger item B (Buchholz order), K-attributed
-- part. See `docs/echo-types/earn-back-plan.adoc` (ledger item B) and
-- `docs/retractions.adoc` (follow-up F-2026-05-18b).
--
-- Item B's standing claim was: the two same-binder Buchholz-order
-- sub-cases
--
--   * `bpsi ν α <ᵇ bpsi ν β` with `α <ᵇ β`   (same Ω-index ν)
--   * `bplus x y₂ <ᵇ bplus x z₂` with `y₂ <ᵇ z₂` (same left summand)
--
-- are "not constructible pending a K-free reformulation", because the
-- *naive* `<ᵇ-irrefl : x <ᵇ x → ⊥` pattern-matches `x <ᵇ x`, and the
-- shared binder (`ν`, resp. `x`) forces the unifier through a
-- reflexive equation `ν =?= ν` whose elimination is the K-restricted
-- *deletion* rule — rejected under `--without-K` (reconfirmed on
-- Agda 2.8; the Order.agda comment cited 2.6.3).
--
-- This module discharges that claim *positively*. The same-binder
-- constructors ARE constructible directly, and the core strict-order
-- metatheory (irreflexivity, transitivity) is proved K-free, with
-- *zero postulates and zero escape pragmas*, by:
--
--   * proving the generalised `<ᵇ⇒≢ : x <ᵇ y → x ≡ y → ⊥` by
--     induction on the *derivation* (indices `x`,`y` distinct — no
--     shared-binder unification ever arises), then
--   * discharging the explicit equation with no-confusion built only
--     from `cong` of total projections and the K-free *conflict* rule
--     (absurd patterns on equations between distinct constructors).
--     `refl` is never matched, so the K-restricted deletion rule is
--     never invoked.
--
-- Conservativity. `Ordinal.Buchholz.Order._<ᵇ_` (the K-free core)
-- embeds faithfully into this relation (`embed` below); this is a
-- strict extension, not a redefinition.
--
-- Scope / what is NOT claimed here. Well-foundedness of the *direct*
-- relation is a termination-checker matter (Routes A/B of
-- `docs/echo-types/buchholz-extended-wf.md`), orthogonal to K, and
-- remains delivered via the comparison *measure*
-- `Ordinal.Buchholz.ExtendedOrder._<ᵇ⁺_`, which stays load-bearing.
-- Trichotomy/totality is likewise out of scope here. This module
-- earns back exactly the K-attributed sub-claim of item B and no more.

module Ordinal.Buchholz.OrderExtendedDirect where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex ; ω ; _≤Ω_ ; _<Ω_ ; <Ω-irrefl
  ; <Ω-trans ; <Ω→≤Ω ; ≤Ω-trans ; ≤Ω-<Ω-trans ; <Ω-≤Ω-trans )
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order as Core using ()

----------------------------------------------------------------------
-- The extended direct relation: the K-free core constructors plus the
-- two same-binder constructors item B deferred.
----------------------------------------------------------------------

data _<ᵇᵈ_ : BT → BT → Set where
  <ᵇ-0-Ω : ∀ {μ}   → bzero <ᵇᵈ bOmega μ
  <ᵇ-0-+ : ∀ {x y} → bzero <ᵇᵈ bplus x y
  <ᵇ-0-ψ : ∀ {ν α} → bzero <ᵇᵈ bpsi ν α
  <ᵇ-ΩΩ  : ∀ {μ ν} → μ <Ω ν → bOmega μ <ᵇᵈ bOmega ν
  <ᵇ-Ωψ  : ∀ {μ ν α} → μ <Ω ν → bOmega μ <ᵇᵈ bpsi ν α
  <ᵇ-ψΩ  : ∀ {μ ν α β} → μ <Ω ν → bpsi μ α <ᵇᵈ bpsi ν β
  <ᵇ-ψΩ≤ : ∀ {ν μ α}   → ν ≤Ω μ → bpsi ν α <ᵇᵈ bOmega μ
  <ᵇ-Ω+  : ∀ {μ x y}    → bOmega μ <ᵇᵈ x → bOmega μ <ᵇᵈ bplus x y
  <ᵇ-ψ+  : ∀ {ν α x y}  → bpsi ν α <ᵇᵈ x → bpsi ν α <ᵇᵈ bplus x y
  <ᵇ-+Ω  : ∀ {x y μ}   → x <ᵇᵈ bOmega μ → bplus x y <ᵇᵈ bOmega μ
  <ᵇ-+ψ  : ∀ {x y ν α} → x <ᵇᵈ bpsi ν α → bplus x y <ᵇᵈ bpsi ν α
  <ᵇ-+1  : ∀ {x₁ x₂ y₁ y₂} → x₁ <ᵇᵈ y₁ → bplus x₁ x₂ <ᵇᵈ bplus y₁ y₂
  -- The two constructors item B reported "unconstructible pending a
  -- K-free reformulation" — directly constructible here:
  <ᵇ-ψα  : ∀ {ν α β}    → α <ᵇᵈ β → bpsi ν α <ᵇᵈ bpsi ν β
  <ᵇ-+2  : ∀ {x y₂ z₂}  → y₂ <ᵇᵈ z₂ → bplus x y₂ <ᵇᵈ bplus x z₂

infix 4 _<ᵇᵈ_

----------------------------------------------------------------------
-- K-free no-confusion for BT: `cong` of total projections, plus the
-- conflict rule. No `refl` is matched anywhere below.
----------------------------------------------------------------------

unΩ : BT → OmegaIndex
unΩ (bOmega μ) = μ
unΩ (bpsi ν _) = ν
unΩ _          = ω

unArg : BT → BT
unArg (bpsi _ α)  = α
unArg (bplus _ y) = y
unArg _           = bzero

unLeft : BT → BT
unLeft (bplus x _) = x
unLeft _           = bzero

bOmega-inj : ∀ {μ ν} → bOmega μ ≡ bOmega ν → μ ≡ ν
bOmega-inj e = cong unΩ e

bpsi-injΩ : ∀ {μ ν α β} → bpsi μ α ≡ bpsi ν β → μ ≡ ν
bpsi-injΩ e = cong unΩ e

bpsi-injArg : ∀ {μ ν α β} → bpsi μ α ≡ bpsi ν β → α ≡ β
bpsi-injArg e = cong unArg e

bplus-injL : ∀ {x₁ x₂ y₁ y₂} → bplus x₁ x₂ ≡ bplus y₁ y₂ → x₁ ≡ y₁
bplus-injL e = cong unLeft e

bplus-injR : ∀ {x₁ x₂ y₁ y₂} → bplus x₁ x₂ ≡ bplus y₁ y₂ → x₂ ≡ y₂
bplus-injR e = cong unArg e

----------------------------------------------------------------------
-- Irreflexivity, K-free. The generalised form keeps `x`,`y` distinct
-- so the constructor match never produces a shared-binder equation;
-- the supplied `x ≡ y` is discharged without ever matching `refl`.
----------------------------------------------------------------------

<ᵇ⇒≢ : ∀ {x y} → x <ᵇᵈ y → x ≡ y → ⊥
-- distinct-head constructors: K-free conflict rule.
<ᵇ⇒≢ <ᵇ-0-Ω ()
<ᵇ⇒≢ <ᵇ-0-+ ()
<ᵇ⇒≢ <ᵇ-0-ψ ()
<ᵇ⇒≢ (<ᵇ-Ωψ _) ()
<ᵇ⇒≢ (<ᵇ-ψΩ≤ _) ()
<ᵇ⇒≢ (<ᵇ-Ω+ _) ()
<ᵇ⇒≢ (<ᵇ-ψ+ _) ()
<ᵇ⇒≢ (<ᵇ-+Ω _) ()
<ᵇ⇒≢ (<ᵇ-+ψ _) ()
-- same-head constructors: cong-injectivity + subst, no refl-match.
<ᵇ⇒≢ (<ᵇ-ΩΩ p) e = <Ω-irrefl (subst (_ <Ω_) (sym (bOmega-inj e)) p)
<ᵇ⇒≢ (<ᵇ-ψΩ p) e = <Ω-irrefl (subst (_ <Ω_) (sym (bpsi-injΩ e)) p)
<ᵇ⇒≢ (<ᵇ-+1 p) e = <ᵇ⇒≢ p (bplus-injL e)
<ᵇ⇒≢ (<ᵇ-ψα p) e = <ᵇ⇒≢ p (bpsi-injArg e)
<ᵇ⇒≢ (<ᵇ-+2 p) e = <ᵇ⇒≢ p (bplus-injR e)

<ᵇ-irrefl : ∀ {x} → x <ᵇᵈ x → ⊥
<ᵇ-irrefl p = <ᵇ⇒≢ p refl

----------------------------------------------------------------------
-- Transitivity, K-free. `<ᵇ-trans` matches `x <ᵇᵈ y` / `y <ᵇᵈ z`
-- (distinct indices), so the shared-binder deletion never arises;
-- the two new constructors only add ordinary constructor-pair clauses.
----------------------------------------------------------------------

<ᵇ-trans : ∀ {x y z} → x <ᵇᵈ y → y <ᵇᵈ z → x <ᵇᵈ z
-- core legs (mirrors `Ordinal.Buchholz.Order.<ᵇ-trans`):
<ᵇ-trans <ᵇ-0-Ω       (<ᵇ-ΩΩ _)            = <ᵇ-0-Ω
<ᵇ-trans <ᵇ-0-Ω       (<ᵇ-Ωψ _)            = <ᵇ-0-ψ
<ᵇ-trans <ᵇ-0-Ω       (<ᵇ-Ω+ _)            = <ᵇ-0-+
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+1 _)            = <ᵇ-0-+
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+Ω _)            = <ᵇ-0-Ω
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+ψ _)            = <ᵇ-0-ψ
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψΩ _)            = <ᵇ-0-ψ
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψ+ _)            = <ᵇ-0-+
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-ΩΩ q)            = <ᵇ-ΩΩ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-Ωψ q)            = <ᵇ-Ωψ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ΩΩ p)    (<ᵇ-Ω+ q)            = <ᵇ-Ω+ (<ᵇ-trans (<ᵇ-ΩΩ p) q)
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψΩ q)            = <ᵇ-Ωψ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψ+ q)            = <ᵇ-Ω+ (<ᵇ-trans (<ᵇ-Ωψ p) q)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψΩ q)            = <ᵇ-ψΩ (<Ω-trans p q)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ψΩ≤ (≤Ω-trans (<Ω→≤Ω p) q)
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψ+ q)            = <ᵇ-ψ+ (<ᵇ-trans (<ᵇ-ψΩ p) q)
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-ΩΩ q)            = <ᵇ-ψΩ≤ (≤Ω-trans p (<Ω→≤Ω q))
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-Ωψ q)            = <ᵇ-ψΩ (≤Ω-<Ω-trans p q)
<ᵇ-trans (<ᵇ-ψΩ≤ p)   (<ᵇ-Ω+ q)            = <ᵇ-ψ+ (<ᵇ-trans (<ᵇ-ψΩ≤ p) q)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+1 q)            = <ᵇ-+1 (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+Ω q)            = <ᵇ-+Ω (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+ψ q)            = <ᵇ-+ψ (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+1 q)            = <ᵇ-Ω+ (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+Ω q)            = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+ψ q)            = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+1 q)            = <ᵇ-ψ+ (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+Ω q)            = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+ψ q)            = <ᵇ-trans p q
<ᵇ-trans (<ᵇ-+Ω p)    (<ᵇ-ΩΩ q)            = <ᵇ-+Ω (<ᵇ-trans p (<ᵇ-ΩΩ q))
<ᵇ-trans (<ᵇ-+Ω p)    (<ᵇ-Ωψ q)            = <ᵇ-+ψ (<ᵇ-trans p (<ᵇ-Ωψ q))
<ᵇ-trans (<ᵇ-+Ω p)    (<ᵇ-Ω+ q)            = <ᵇ-+1 (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+ψ p)    (<ᵇ-ψΩ q)            = <ᵇ-+ψ (<ᵇ-trans p (<ᵇ-ψΩ q))
<ᵇ-trans (<ᵇ-+ψ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-+Ω (<ᵇ-trans p (<ᵇ-ψΩ≤ q))
<ᵇ-trans (<ᵇ-+ψ p)    (<ᵇ-ψ+ q)            = <ᵇ-+1 (<ᵇ-trans p q)
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψΩ≤ _)           = <ᵇ-0-Ω
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ΩΩ (<Ω-≤Ω-trans p q)
-- `<ᵇ-ψα` as LEFT leg:
<ᵇ-trans (<ᵇ-ψα p)    (<ᵇ-ψα q)            = <ᵇ-ψα (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-ψα _)    (<ᵇ-ψΩ q)            = <ᵇ-ψΩ q
<ᵇ-trans (<ᵇ-ψα _)    (<ᵇ-ψΩ≤ q)           = <ᵇ-ψΩ≤ q
<ᵇ-trans (<ᵇ-ψα p)    (<ᵇ-ψ+ q)            = <ᵇ-ψ+ (<ᵇ-trans (<ᵇ-ψα p) q)
-- `<ᵇ-ψα` as RIGHT leg (left-leg head must land in `bpsi ν _`):
<ᵇ-trans <ᵇ-0-ψ       (<ᵇ-ψα _)            = <ᵇ-0-ψ
<ᵇ-trans (<ᵇ-Ωψ p)    (<ᵇ-ψα _)            = <ᵇ-Ωψ p
<ᵇ-trans (<ᵇ-ψΩ p)    (<ᵇ-ψα _)            = <ᵇ-ψΩ p
<ᵇ-trans (<ᵇ-+ψ p)    (<ᵇ-ψα q)            = <ᵇ-+ψ (<ᵇ-trans p (<ᵇ-ψα q))
-- `<ᵇ-+2` as LEFT leg:
<ᵇ-trans (<ᵇ-+2 p)    (<ᵇ-+2 q)            = <ᵇ-+2 (<ᵇ-trans p q)
<ᵇ-trans (<ᵇ-+2 _)    (<ᵇ-+1 q)            = <ᵇ-+1 q
<ᵇ-trans (<ᵇ-+2 _)    (<ᵇ-+Ω q)            = <ᵇ-+Ω q
<ᵇ-trans (<ᵇ-+2 _)    (<ᵇ-+ψ q)            = <ᵇ-+ψ q
-- `<ᵇ-+2` as RIGHT leg (left-leg head must land in `bplus x _`):
<ᵇ-trans <ᵇ-0-+       (<ᵇ-+2 _)            = <ᵇ-0-+
<ᵇ-trans (<ᵇ-Ω+ p)    (<ᵇ-+2 _)            = <ᵇ-Ω+ p
<ᵇ-trans (<ᵇ-ψ+ p)    (<ᵇ-+2 _)            = <ᵇ-ψ+ p
<ᵇ-trans (<ᵇ-+1 p)    (<ᵇ-+2 _)            = <ᵇ-+1 p

----------------------------------------------------------------------
-- Conservativity: the K-free core embeds faithfully (not redefined).
----------------------------------------------------------------------

embed : ∀ {x y} → x Core.<ᵇ y → x <ᵇᵈ y
embed Core.<ᵇ-0-Ω      = <ᵇ-0-Ω
embed Core.<ᵇ-0-+      = <ᵇ-0-+
embed Core.<ᵇ-0-ψ      = <ᵇ-0-ψ
embed (Core.<ᵇ-ΩΩ p)   = <ᵇ-ΩΩ p
embed (Core.<ᵇ-Ωψ p)   = <ᵇ-Ωψ p
embed (Core.<ᵇ-ψΩ p)   = <ᵇ-ψΩ p
embed (Core.<ᵇ-ψΩ≤ p)  = <ᵇ-ψΩ≤ p
embed (Core.<ᵇ-Ω+ p)   = <ᵇ-Ω+ (embed p)
embed (Core.<ᵇ-ψ+ p)   = <ᵇ-ψ+ (embed p)
embed (Core.<ᵇ-+Ω p)   = <ᵇ-+Ω (embed p)
embed (Core.<ᵇ-+ψ p)   = <ᵇ-+ψ (embed p)
embed (Core.<ᵇ-+1 p)   = <ᵇ-+1 (embed p)
