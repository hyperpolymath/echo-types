{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- A concrete `Tolerance` + `PseudoMetric` instance for `EchoApprox.Approx`,
-- whose sole purpose is to give `Smoke.agda` a typeable identifier per
-- headline lemma of the parameterised `EchoApprox.Approx` module.
--
-- Repo invariant (`CLAUDE.md`, "Working rules"):
--
--     "Every headline theorem must be pinned in `Smoke.agda` via
--      `using` clause."
--
-- Lemmas living inside the parameterised submodule `EchoApprox.Approx`
-- cannot be named in `Smoke.agda` until *some* `PseudoMetric` is
-- supplied, so the invariant is silently violated for every
-- `echo-approx-*` and `echo-strict→approx` lemma. This module closes
-- that gap.
--
-- Design call: the trivial / collapse-to-strict pseudometric on `⊤`.
--
--   * `Tol`     := `⊤`,  `zero` := `tt`,  `_+_` := `λ _ _ → tt`
--   * `_≤_`     := `λ _ _ → ⊤`
--   * `dist`    := `λ _ _ → tt` on the carrier `B := ⊤`
--
-- Every order / monotonicity / triangle obligation discharges to `tt`.
-- Every approximate echo `EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)`
-- collapses to `Σ A (λ _ → ⊤)`, so each pinned lemma here is a trivial
-- sanity check that the parameterised module's term is well-typed at
-- *some* instance. That is exactly the hygiene contract the invariant
-- asks for — proof-of-life, not new content.
--
-- We choose `A := ⊤` and `B := ⊤` so each pinned name resolves to a
-- single top-level identifier with no remaining type parameters, which
-- lets `Smoke.agda` enumerate them in a `using` clause one-for-one.
--
-- A non-trivial pseudometric (e.g. the discrete metric over `Bool`)
-- would also work, but adds nothing the trivial one does not give for
-- the purposes of `Smoke.agda` pinning. When a genuine metric instance
-- lands in the repo, the per-lemma pins below can be re-pointed at it.

module EchoApproxInstance where

open import Level                                 using (Level)
open import Data.Unit.Base                        using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import EchoApprox using (Tolerance; PseudoMetric; BalancedTolerance; module Approx)

----------------------------------------------------------------------
-- The trivial tolerance carrier
----------------------------------------------------------------------

-- All fields are tt / Unit; every law obligation is met by `tt`.
trivialTolerance : Tolerance Level.zero
trivialTolerance = record
  { Tol      = ⊤
  ; zero     = tt
  ; _+_      = λ _ _ → tt
  ; _≤_      = λ _ _ → ⊤
  ; ≤-refl   = tt
  ; ≤-trans  = λ _ _ → tt
  ; +-mono-≤ = λ _ _ → tt
  }

----------------------------------------------------------------------
-- The trivial pseudometric on the carrier `⊤`
----------------------------------------------------------------------

-- Distance is constantly `tt`; self-distance is `refl`; triangle is `tt`.
trivialPseudoMetric : PseudoMetric ⊤ trivialTolerance
trivialPseudoMetric = record
  { dist      = λ _ _ → tt
  ; dist-self = λ _   → refl
  ; dist-tri  = λ _ _ _ → tt
  }

----------------------------------------------------------------------
-- The trivial BalancedTolerance instance on `trivialTolerance`
----------------------------------------------------------------------

-- On `Tol := ⊤`, both `+`-identity laws reduce to `tt ≡ tt`, which is
-- `refl`. Pinned alongside `trivialTolerance` so `Smoke.agda` can
-- enumerate the post-PR-#74 Rung-C lemmas at a typeable instance, in
-- the same spirit as the per-lemma pins below.
trivialBalancedTolerance : BalancedTolerance trivialTolerance
trivialBalancedTolerance = record
  { +-identityˡ = λ _ → refl
  ; +-identityʳ = λ _ → refl
  }

----------------------------------------------------------------------
-- Per-lemma proof-of-life pins for `Approx` at the trivial instance.
--
-- Top-level identifiers, one per `EchoApprox.Approx` headline, with
-- `A := ⊤` and `B := ⊤` so each is a closed term that `Smoke.agda`
-- can enumerate in a `using` clause. Definitions use `=` (no explicit
-- type signature) so the original term's type is inferred — which is
-- exactly the typeability check the hygiene invariant asks for.
----------------------------------------------------------------------

private
  open module ApproxT⊤ =
    Approx {A = ⊤} {B = ⊤} {T = trivialTolerance} trivialPseudoMetric

approx-EchoR              = EchoR
approx-intro              = echo-approx-intro
approx-strict→approx      = echo-strict→approx
approx-relax              = echo-approx-relax
approx-NonExpansive       = NonExpansive
approx-compose            = echo-approx-compose
approx-comp-sound         = echo-approx-comp-sound
approx-comp-retract-to    = echo-approx-comp-retract-to
approx-comp-retract-A     = echo-approx-comp-retract-A
approx-comp-retract-B     = echo-approx-comp-retract-B
approx-comp-retract-budget = echo-approx-comp-retract-budget
approx-comp-retract-from-to = echo-approx-comp-retract-from-to
approx-subst-A-invariant  = subst-A-invariant
approx-Separated          = Separated
approx-zero-collapses-strict = echo-approx-zero-collapses-strict
approx-shadow-A           = echo-shadow-A
approx-shadow-iso-to      = echo-shadow-iso-to
approx-shadow-iso-from    = echo-shadow-iso-from
approx-strict→approx-shadow-A = echo-strict→approx-shadow-A
approx-strict→approx-collapse-shadow-A = echo-strict→approx-collapse-shadow-A
