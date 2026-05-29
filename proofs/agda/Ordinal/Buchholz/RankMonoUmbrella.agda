{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- The umbrella `rank-pow-mono` theorem (Item 3 of the path-1 unblock).
--
-- Defines a *rank-soundness-ready* relation `_<ᵇ⁰_` mirroring the
-- 10 closeable constructors of `Ordinal.Buchholz.Order._<ᵇ_` with
-- rank-soundness side conditions (the WfCNF tail bounds) baked in.
-- Proves the umbrella theorem on this self-contained subset:
--
--   `rank-pow-mono-<ᵇ⁰ : x <ᵇ⁰ y → rank-pow x <′ rank-pow y`.
--
-- No external WfCNF carrier is needed — the tail bounds are wired
-- into the constructors of `<ᵇ⁰` itself, so the umbrella is a
-- direct structural recursion on the proof.  Consumers wishing to
-- discharge a `<ᵇ⁻`-style umbrella construct `<ᵇ⁰` derivations and
-- apply this theorem.
--
-- ## What's in / what's out
--
-- IN (10 constructors):
--
--   * `<ᵇ⁰-0-Ω`, `<ᵇ⁰-0-ψ`, `<ᵇ⁰-ΩΩ`, `<ᵇ⁰-Ωψ`, `<ᵇ⁰-ψΩ`
--     — no recursive premise, no WfCNF dependency
--   * `<ᵇ⁰-Ω+`, `<ᵇ⁰-ψ+` — recurse on premise (left of target bplus)
--   * `<ᵇ⁰-+Ω`, `<ᵇ⁰-+ψ` — recurse on premise + carry tail bound
--   * `<ᵇ⁰-+1-Ω`, `<ᵇ⁰-+1-ψ` — joint-bplus, atomic target;
--                              recurse on premise + carry source tail bound
--
-- OUT (3 structurally-blocked cases of `_<ᵇ_`, documented in
-- `buchholz-rank-obstruction.adoc`):
--
--   * `<ᵇ-0-+`  — `bplus bzero bzero` edge case
--   * `<ᵇ-ψα`   — needs ψ-admissibility refinement
--   * `<ᵇ-ψΩ≤`  — same admissibility blocker (ν = μ sub-case)
--   * `<ᵇ-+1`   — bplus-target sub-case (rank not additive principal)
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `_<ᵇ⁰_`               -- the closeable subset relation
--   * `_≤ᵇ⁰_`               -- non-strict companion
--   * `≤ᵇ⁰-refl`            -- propositional reflexivity
--   * `rank-pow-mono-<ᵇ⁰`   -- THE UMBRELLA (strict)
--   * `rank-pow-mono-≤ᵇ⁰`   -- non-strict companion

module Ordinal.Buchholz.RankMonoUmbrella where

open import Data.Sum.Base                         using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers                  using (OmegaIndex; _<Ω_)
open import Ordinal.Buchholz.Syntax               using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Brouwer                       using (Ord; oz; osuc)
open import Ordinal.Brouwer.Phase13               using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-trans
  ; ≤′-self-osuc
  )
open import Ordinal.Buchholz.RankPow              using
  ( rank-pow
  ; ω-rank-pow
  ; rank-mono-<ᵇ-0-Ω
  ; rank-mono-<ᵇ-0-ψ
  ; rank-mono-<ᵇ-ΩΩ
  ; rank-mono-<ᵇ-Ωψ
  ; rank-mono-<ᵇ-ψΩ
  ; rank-mono-<ᵇ-Ω+
  ; rank-mono-<ᵇ-ψ+
  ; rank-mono-<ᵇ-+Ω
  ; rank-mono-<ᵇ-+ψ
  ; rank-mono-<ᵇ-+1-Ω-target
  ; rank-mono-<ᵇ-+1-ψ-target
  )

----------------------------------------------------------------------
-- The rank-soundness-ready subset `_<ᵇ⁰_`
----------------------------------------------------------------------

-- The 10 closeable constructors of `_<ᵇ_`, with rank-soundness side
-- conditions baked in.  Recursion is on `_<ᵇ⁰_` and `_≤ᵇ⁰_`, both
-- mutually defined below.

mutual

  data _<ᵇ⁰_ : BT → BT → Set where
    -- Trivial cases
    <ᵇ⁰-0-Ω : ∀ {μ}     → bzero <ᵇ⁰ bOmega μ
    <ᵇ⁰-0-ψ : ∀ {ν α}   → bzero <ᵇ⁰ bpsi ν α
    <ᵇ⁰-ΩΩ  : ∀ {μ ν}   → μ <Ω ν → bOmega μ <ᵇ⁰ bOmega ν
    <ᵇ⁰-Ωψ  : ∀ {μ ν α} → μ <Ω ν → bOmega μ <ᵇ⁰ bpsi ν α
    <ᵇ⁰-ψΩ  : ∀ {μ ν α β} → μ <Ω ν → bpsi μ α <ᵇ⁰ bpsi ν β

    -- Via-left
    <ᵇ⁰-Ω+  : ∀ {μ x y}   → bOmega μ <ᵇ⁰ x → bOmega μ <ᵇ⁰ bplus x y
    <ᵇ⁰-ψ+  : ∀ {ν α x y} → bpsi ν α <ᵇ⁰ x → bpsi ν α <ᵇ⁰ bplus x y

    -- Source-bplus (premise on left summand + WfCNF tail bound on source)
    <ᵇ⁰-+Ω  : ∀ {x y μ}
      → x <ᵇ⁰ bOmega μ
      → y ≤ᵇ⁰ x
      → bplus x y <ᵇ⁰ bOmega μ
    <ᵇ⁰-+ψ  : ∀ {x y ν α}
      → x <ᵇ⁰ bpsi ν α
      → y ≤ᵇ⁰ x
      → bplus x y <ᵇ⁰ bpsi ν α

    -- Joint-bplus, atomic target (additive-principal at y₁'s rank)
    <ᵇ⁰-+1-Ω : ∀ {x₁ x₂ μ y₂}
      → x₁ <ᵇ⁰ bOmega μ
      → x₂ ≤ᵇ⁰ x₁
      → bplus x₁ x₂ <ᵇ⁰ bplus (bOmega μ) y₂
    <ᵇ⁰-+1-ψ : ∀ {x₁ x₂ ν α y₂}
      → x₁ <ᵇ⁰ bpsi ν α
      → x₂ ≤ᵇ⁰ x₁
      → bplus x₁ x₂ <ᵇ⁰ bplus (bpsi ν α) y₂

  -- Non-strict companion.  Used for the tail bounds; the `inj₂ refl`
  -- branch carries equal terms (rank-pow ≡ rank-pow).

  _≤ᵇ⁰_ : BT → BT → Set
  x ≤ᵇ⁰ y = (x <ᵇ⁰ y) ⊎ (x ≡ y)

infix 4 _<ᵇ⁰_ _≤ᵇ⁰_

≤ᵇ⁰-refl : ∀ {x} → x ≤ᵇ⁰ x
≤ᵇ⁰-refl = inj₂ refl

----------------------------------------------------------------------
-- The umbrella theorem
----------------------------------------------------------------------

-- Structural recursion on `_<ᵇ⁰_`; the `<′ / ≤′` mutual recursion
-- threads through the tail bounds.  Each case dispatches to the
-- matching primitive in `RankPow`.

mutual

  rank-pow-mono-<ᵇ⁰ : ∀ {s t} → s <ᵇ⁰ t → rank-pow s <′ rank-pow t
  rank-pow-mono-<ᵇ⁰ {.bzero}      {bOmega μ}     <ᵇ⁰-0-Ω    = rank-mono-<ᵇ-0-Ω {μ}
  rank-pow-mono-<ᵇ⁰ {.bzero}      {bpsi ν α}     <ᵇ⁰-0-ψ    = rank-mono-<ᵇ-0-ψ {ν} {α}
  rank-pow-mono-<ᵇ⁰ (<ᵇ⁰-ΩΩ {μ = μ} {ν = ν} p) = rank-mono-<ᵇ-ΩΩ {μ} {ν} p
  rank-pow-mono-<ᵇ⁰ (<ᵇ⁰-Ωψ {μ = μ} {ν = ν} {α = α} p) = rank-mono-<ᵇ-Ωψ {μ} {ν} {α} p
  rank-pow-mono-<ᵇ⁰ (<ᵇ⁰-ψΩ {μ = μ} {ν = ν} {α = α} {β = β} p) = rank-mono-<ᵇ-ψΩ {μ} {ν} {α} {β} p
  rank-pow-mono-<ᵇ⁰ {bOmega μ}    {bplus x y}    (<ᵇ⁰-Ω+ p) =
    rank-mono-<ᵇ-Ω+ {μ} {x} {y} (rank-pow-mono-<ᵇ⁰ p)
  rank-pow-mono-<ᵇ⁰ {bpsi ν α}    {bplus x y}    (<ᵇ⁰-ψ+ p) =
    rank-mono-<ᵇ-ψ+ {ν} {α} {x} {y} (rank-pow-mono-<ᵇ⁰ p)
  rank-pow-mono-<ᵇ⁰ {bplus x y}   {bOmega μ}     (<ᵇ⁰-+Ω p y≤x) =
    rank-mono-<ᵇ-+Ω {x} {y} {μ}
      (rank-pow-mono-<ᵇ⁰ p)
      (rank-pow-mono-≤ᵇ⁰ y≤x)
  rank-pow-mono-<ᵇ⁰ {bplus x y}   {bpsi ν α}     (<ᵇ⁰-+ψ p y≤x) =
    rank-mono-<ᵇ-+ψ {x} {y} {ν} {α}
      (rank-pow-mono-<ᵇ⁰ p)
      (rank-pow-mono-≤ᵇ⁰ y≤x)
  rank-pow-mono-<ᵇ⁰ {bplus x₁ x₂} {bplus .(bOmega μ) y₂} (<ᵇ⁰-+1-Ω {μ = μ} p x₂≤x₁) =
    rank-mono-<ᵇ-+1-Ω-target {x₁} {x₂} {μ} {y₂}
      (rank-pow-mono-<ᵇ⁰ p)
      (rank-pow-mono-≤ᵇ⁰ x₂≤x₁)
  rank-pow-mono-<ᵇ⁰ {bplus x₁ x₂} {bplus .(bpsi ν α) y₂} (<ᵇ⁰-+1-ψ {ν = ν} {α = α} p x₂≤x₁) =
    rank-mono-<ᵇ-+1-ψ-target {x₁} {x₂} {ν} {α} {y₂}
      (rank-pow-mono-<ᵇ⁰ p)
      (rank-pow-mono-≤ᵇ⁰ x₂≤x₁)

  rank-pow-mono-≤ᵇ⁰ : ∀ {x y} → x ≤ᵇ⁰ y → rank-pow x ≤′ rank-pow y
  rank-pow-mono-≤ᵇ⁰ {x} {y} (inj₁ p) =
    ≤′-trans {rank-pow x} {osuc (rank-pow x)} {rank-pow y}
      (≤′-self-osuc (rank-pow x))
      (rank-pow-mono-<ᵇ⁰ p)
  rank-pow-mono-≤ᵇ⁰ {x} {.x} (inj₂ refl) = ≤′-refl {rank-pow x}
