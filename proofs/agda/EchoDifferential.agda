{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoDifferential: the audience-facing perturbation-tracking
-- theorem for sensitivity-flavoured Echo content.
--
-- !! HONEST BOUND, STATED UP FRONT !!
--
-- This module is a TYPE-LEVEL formalisation of "a blurred query
-- loses which perturbation was applied to the input". It is NOT
-- differential privacy, NOT a Lipschitz / sensitivity-bound
-- argument, NOT a noise-calibration result, NOT a
-- privacy-vs-utility tradeoff, NOT an adversary model. The
-- audience-side message is:
--
--   For ANY value type and ANY perturbation type with two
--   distinguishable perturbations, the "blur" map that collapses
--   perturbed inputs to a common output forgets the perturbation
--   — its Echo carries the discarded perturbation identity,
--   exactly the content sensitivity / DP discourse uses to define
--   the "lost information" intuition.
--
-- The structural fact is the same as `EchoProvenance` and
-- `EchoProbabilisticSupport`: a non-injective forgetful map with
-- distinguishable preimages. What changes is the audience-side
-- framing: differential / sensitivity discourse cares about
-- perturbation-sensitivity / neighbouring-input / ε-budget
-- annotations on values; the lost annotation is the perturbation
-- the blur applied.
--
-- *Closes Tier 3 fourth audience move per the GPT-recommended
-- order.* Independent of EchoProbabilisticSupport. Lower priority
-- per the original sequencing; useful for the
-- "perturbation tracking ≠ DP" honest-scope statement.
--
-- *Echo-specific properties used.* This module leans on:
--
--   * `Echo.echo-intro` — the canonical fibre inhabitation.
--   * `Echo.Echo` — the fibre carrier.
--   * `EchoResidue.echo-to-residue` — the lowering to a residue
--     showing perturbation-distinguishing echoes become residue-
--     indistinguishable.
--
-- Same Echo-vs-Σ clearance argument as `EchoProvenance` /
-- `EchoProbabilisticSupport`. Falsifier per the matched-negative
-- block at the bottom.
--
-- Headlines (pinned in Smoke.agda):
--
--   * Sensitivity                            -- the abstract setup record
--   * module SensitivityTheorems              -- parametric in S : Sensitivity
--   * blur-collapses-perturbations-at         -- non-injectivity at v
--   * echo-pert₁ / echo-pert₂                 -- concrete fibre inhabitants
--   * echo-carries-perturbation               -- carriers distinguish perturbations
--   * echo-pert₁≢echo-pert₂                   -- the echoes themselves differ
--   * residue-loses-perturbation              -- lowering loses the perturbation
--   * bool-perturbed-nat-sensitivity          -- the worked concrete instance
--
-- Scope guardrail (HONEST BOUND, per R-2026-05-18). The matched-
-- negative `NotProved-*` aliases at the bottom of this file pin
-- the audience-facing scope explicitly. This module is about
-- TYPE-LEVEL perturbation tracking — what gets lost when a blur
-- erases the perturbation — NOT about ε-DP, Lipschitz constants,
-- or noise calibration.

module EchoDifferential where

open import Echo
open import EchoResidue using (EchoR; echo-to-residue)

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

----------------------------------------------------------------------
-- The abstract sensitivity setup.
--
-- A `Sensitivity` is the data of a value type, a perturbation
-- type, two distinguishable perturbations, and the constructive
-- distinguishability witness. `Set₁` because of the `Set`-valued
-- fields.
----------------------------------------------------------------------

record Sensitivity : Set₁ where
  field
    Value         : Set
    Perturbation  : Set
    pert₁         : Perturbation
    pert₂         : Perturbation
    pert-distinct : pert₁ ≢ pert₂

----------------------------------------------------------------------
-- The headline theorems, parametric in the sensitivity setup.
----------------------------------------------------------------------

module SensitivityTheorems (S : Sensitivity) where
  open Sensitivity S

  ------------------------------------------------------------
  -- A "perturbed value" pairs a value with the perturbation
  -- applied to it. The blur forgets the perturbation, keeping
  -- only the value.
  ------------------------------------------------------------

  Perturbed : Set
  Perturbed = Value × Perturbation

  -- The blur: project to the value, forget the perturbation.
  -- Echo of this is where the lost perturbation lives.
  blur : Perturbed → Value
  blur (v , _) = v

  ------------------------------------------------------------
  -- Two perturbed values at any value, differing only in
  -- the applied perturbation.
  ------------------------------------------------------------

  perturbed-pert₁ : (v : Value) → Perturbed
  perturbed-pert₁ v = v , pert₁

  perturbed-pert₂ : (v : Value) → Perturbed
  perturbed-pert₂ v = v , pert₂

  ------------------------------------------------------------
  -- Headline 1: blur is non-injective.
  --
  -- At every value, two different-perturbation inputs collapse
  -- to the same blurred output.
  ------------------------------------------------------------

  blur-collapses-perturbations-at :
    (v : Value) →
    Σ Perturbed (λ p₁ → Σ Perturbed (λ p₂ →
      proj₂ p₁ ≢ proj₂ p₂ × blur p₁ ≡ blur p₂))
  blur-collapses-perturbations-at v =
    perturbed-pert₁ v , perturbed-pert₂ v , pert-distinct , refl

  ------------------------------------------------------------
  -- Headline 2: concrete Echo carriers per perturbation.
  ------------------------------------------------------------

  echo-pert₁ : (v : Value) → Echo blur v
  echo-pert₁ v = echo-intro blur (perturbed-pert₁ v)

  echo-pert₂ : (v : Value) → Echo blur v
  echo-pert₂ v = echo-intro blur (perturbed-pert₂ v)

  ------------------------------------------------------------
  -- Headline 3: Echo carries which perturbation produced the
  -- value — the precise content the blur discards.
  ------------------------------------------------------------

  echo-carries-perturbation :
    (v : Value) →
    proj₂ (proj₁ (echo-pert₁ v)) ≢ proj₂ (proj₁ (echo-pert₂ v))
  echo-carries-perturbation _ = pert-distinct

  echo-pert₁≢echo-pert₂ :
    (v : Value) → echo-pert₁ v ≢ echo-pert₂ v
  echo-pert₁≢echo-pert₂ v eq =
    pert-distinct (cong (λ e → proj₂ (proj₁ e)) eq)

  ------------------------------------------------------------
  -- Headline 4: residue lowering loses the perturbation.
  ------------------------------------------------------------

  TrivCert : ⊤ → Value → Set
  TrivCert _ _ = ⊤

  blur-kappa : Perturbed → ⊤
  blur-kappa _ = tt

  blur-sound : ∀ p → TrivCert (blur-kappa p) (blur p)
  blur-sound _ = tt

  blur-to-residue :
    ∀ {v : Value} → Echo blur v → EchoR ⊤ TrivCert v
  blur-to-residue {v} =
    echo-to-residue blur blur-kappa TrivCert blur-sound

  residue-loses-perturbation :
    (v : Value) →
    blur-to-residue (echo-pert₁ v) ≡ blur-to-residue (echo-pert₂ v)
  residue-loses-perturbation _ = refl

----------------------------------------------------------------------
-- Worked concrete instance: Bool-perturbed ℕ sensitivity.
--
-- The minimum-non-trivial sensitivity setup: ℕ values, Bool
-- perturbations (a 1-bit "did we perturb up or down"
-- annotation). Distinguishability of `true`/`false` is the
-- standard `λ ()`.
----------------------------------------------------------------------

bool-perturbed-nat-sensitivity : Sensitivity
bool-perturbed-nat-sensitivity = record
  { Value         = ℕ
  ; Perturbation  = Bool
  ; pert₁         = true
  ; pert₂         = false
  ; pert-distinct = λ ()
  }

----------------------------------------------------------------------
-- Matched-negative block (HONEST BOUND, per R-2026-05-18 discipline).
----------------------------------------------------------------------

NotProved-epsilon-DP : Set
NotProved-epsilon-DP = ⊤

NotProved-Lipschitz-bound : Set
NotProved-Lipschitz-bound = ⊤

NotProved-noise-calibrated : Set
NotProved-noise-calibrated = ⊤

NotProved-privacy-vs-utility : Set
NotProved-privacy-vs-utility = ⊤

NotProved-adversary-model : Set
NotProved-adversary-model = ⊤

----------------------------------------------------------------------
-- Companion remark.
--
-- The four headlines of `SensitivityTheorems` capture the
-- structural fact of perturbation information loss at the
-- audience level:
--
--   1. The blur is non-injective on different-perturbation inputs.
--   2. The Echo at any output has at least two carriers, one per
--      perturbation value.
--   3. The Echo's carriers distinguish the lost perturbation.
--   4. The residue lowering forgets the perturbation —
--      distinguishable echoes become residue-indistinguishable.
--
-- *Why this differs from `EchoProvenance` / `EchoProbabilisticSupport`
-- despite the same formal shape.* The three modules share one Σ-
-- with-tag pattern; the audience-side framings are:
--
--   * EchoProvenance — "where did this value come from?" lineage
--     annotations on database tuples;
--   * EchoProbabilisticSupport — "which draw produced this
--     outcome?" sample-id annotations on randomised computations;
--   * EchoDifferential (this module) — "which perturbation
--     produced this output?" sensitivity annotations on blurred
--     queries.
--
-- All three are about the same theorem: the forgetful map loses
-- the tag, the Echo recovers it. They sit in the repo as
-- separate audience-facing modules because the audiences are
-- different — a database engineer, a probabilistic-programming
-- researcher, and a sensitivity / DP-adjacent practitioner find
-- the same content under names matching their discourse, and
-- that's the audience-move tier's purpose.
--
-- *Why this is NOT differential privacy.* The `Sensitivity`
-- record has no ε-budget, no metric / sensitivity-bound on
-- `Value`, no noise distribution, no adversary capabilities, no
-- composition theorems. It is a TYPE-LEVEL perturbation-tag
-- tracking. The matched-negative block above pins this scope
-- explicitly: claims about ε-DP, Lipschitz bounds, noise
-- calibration, privacy-vs-utility tradeoffs, or adversary
-- models are out of scope. Future audience-extensions (e.g.
-- `EchoDP.agda` adding ε-budget + noise + composition theorems)
-- can layer additional theorems on top, with `Sensitivity` as
-- the minimum-fact baseline.
--
-- This closes the Tier 3 audience-move spine (Provenance →
-- Security → ProbabilisticSupport → Differential). The narrative
-- deliverable is `EchoCanonicalIdentitySuite.agda` — the
-- curated suite pulling the Tier-1+2+3 named theorems into one
-- file as the "why Echo deserves a name" demo.
----------------------------------------------------------------------
