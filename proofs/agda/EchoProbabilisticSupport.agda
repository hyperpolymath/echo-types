{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoProbabilisticSupport: the audience-facing support-tracking
-- theorem for sampling-flavoured Echo content.
--
-- !! HONEST BOUND, STATED UP FRONT !!
--
-- This module is a TYPE-LEVEL formalisation of "the marginal of a
-- sample loses which index produced it". It is NOT a measure-
-- theoretic probability theory, a probability monad, a coupling /
-- Kantorovich setup, or a randomness-extractor argument. The
-- audience-side message is:
--
--   For ANY outcome type and ANY index type with two
--   distinguishable indices, the marginal projection (forgetting
--   the index, keeping the outcome) loses the index — its Echo
--   carries the discarded sample identity, exactly the content
--   support-tracking discourse uses.
--
-- The structural fact is the same as `EchoProvenance` (a non-
-- injective forgetful map with distinguishable preimages). What
-- changes is the audience-side framing: provenance discourse cares
-- about lineage / where-from / why-from annotations; sampling /
-- support-tracking discourse cares about which-sample / draw-id /
-- run-instance annotations. The formalism is one shape; the
-- audience matters.
--
-- *Closes Tier 3 third audience move per the GPT-recommended
-- order.* Independent of EchoProvenance / EchoSecurity; lower-
-- priority per the original sequencing but useful for the
-- "support-tracking ≠ probability theory" honest-scope statement
-- the module pins.
--
-- *Echo-specific properties used.* This module leans on:
--
--   * `Echo.echo-intro` — the canonical fibre inhabitation.
--   * `Echo.Echo` — the fibre carrier.
--   * `EchoResidue.echo-to-residue` — the lowering to a residue
--     showing index-distinguishing echoes become residue-
--     indistinguishable.
--
-- None of these reduce to plain Σ + ≡: each carries the
-- residue/witness/no-section content that `EchoProvenance` /
-- `EchoResidue` have already pinned. The audience rephrasing
-- here is packaging, not generalisation past it.
--
-- Headlines (pinned in Smoke.agda):
--
--   * Sampling                              -- the abstract setup record
--   * module SamplingTheorems                -- parametric in S : Sampling
--   * support-collapses-at                   -- non-injectivity at o
--   * echo-idx₁ / echo-idx₂                  -- concrete fibre inhabitants
--   * echo-carries-which-index               -- carriers distinguish indices
--   * echo-idx₁≢echo-idx₂                    -- the echoes themselves differ
--   * residue-loses-index                    -- lowering loses the index
--   * bool-indexed-nat-sampling              -- the worked concrete instance
--
-- Scope guardrail (HONEST BOUND, per R-2026-05-18). The matched-
-- negative `NotProved-*` aliases at the bottom of this file pin
-- the audience-facing scope explicitly. This module is about
-- TYPE-LEVEL support tracking — what gets lost when a marginal
-- erases the sample index — NOT about measure theory, monad
-- laws, or distributional invariants.

module EchoProbabilisticSupport where

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
-- The abstract sampling setup.
--
-- A `Sampling` is the data of an outcome type, an index type, two
-- distinguishable indices, and the constructive distinguishability
-- witness. `Set₁` because of the `Set`-valued fields.
----------------------------------------------------------------------

record Sampling : Set₁ where
  field
    Outcome      : Set
    Index        : Set
    idx₁         : Index
    idx₂         : Index
    idx-distinct : idx₁ ≢ idx₂

----------------------------------------------------------------------
-- The headline theorems, parametric in the sampling setup.
----------------------------------------------------------------------

module SamplingTheorems (S : Sampling) where
  open Sampling S

  ------------------------------------------------------------
  -- A "sample" pairs an outcome with the sampling index that
  -- produced it. The marginal forgets the index.
  ------------------------------------------------------------

  Sample : Set
  Sample = Outcome × Index

  -- The marginal: project to the outcome, forget the sampling
  -- index. Echo of this is where the lost index lives.
  marginal : Sample → Outcome
  marginal (o , _) = o

  ------------------------------------------------------------
  -- Two samples at any outcome, differing only in sampling index.
  ------------------------------------------------------------

  sample-idx₁ : (o : Outcome) → Sample
  sample-idx₁ o = o , idx₁

  sample-idx₂ : (o : Outcome) → Sample
  sample-idx₂ o = o , idx₂

  ------------------------------------------------------------
  -- Headline 1: marginal is non-injective.
  --
  -- At every outcome, two different-index samples collapse to
  -- the same marginal.
  ------------------------------------------------------------

  support-collapses-at :
    (o : Outcome) →
    Σ Sample (λ s₁ → Σ Sample (λ s₂ →
      proj₂ s₁ ≢ proj₂ s₂ × marginal s₁ ≡ marginal s₂))
  support-collapses-at o =
    sample-idx₁ o , sample-idx₂ o , idx-distinct , refl

  ------------------------------------------------------------
  -- Headline 2: concrete Echo carriers per sampling index.
  ------------------------------------------------------------

  echo-idx₁ : (o : Outcome) → Echo marginal o
  echo-idx₁ o = echo-intro marginal (sample-idx₁ o)

  echo-idx₂ : (o : Outcome) → Echo marginal o
  echo-idx₂ o = echo-intro marginal (sample-idx₂ o)

  ------------------------------------------------------------
  -- Headline 3: Echo carries which sample index produced the
  -- outcome — the precise content the marginal discards.
  ------------------------------------------------------------

  echo-carries-which-index :
    (o : Outcome) →
    proj₂ (proj₁ (echo-idx₁ o)) ≢ proj₂ (proj₁ (echo-idx₂ o))
  echo-carries-which-index _ = idx-distinct

  echo-idx₁≢echo-idx₂ :
    (o : Outcome) → echo-idx₁ o ≢ echo-idx₂ o
  echo-idx₁≢echo-idx₂ o eq =
    idx-distinct (cong (λ e → proj₂ (proj₁ e)) eq)

  ------------------------------------------------------------
  -- Headline 4: residue lowering loses the index.
  ------------------------------------------------------------

  TrivCert : ⊤ → Outcome → Set
  TrivCert _ _ = ⊤

  marg-kappa : Sample → ⊤
  marg-kappa _ = tt

  marg-sound : ∀ s → TrivCert (marg-kappa s) (marginal s)
  marg-sound _ = tt

  marginal-to-residue :
    ∀ {o : Outcome} → Echo marginal o → EchoR ⊤ TrivCert o
  marginal-to-residue {o} =
    echo-to-residue marginal marg-kappa TrivCert marg-sound

  residue-loses-index :
    (o : Outcome) →
    marginal-to-residue (echo-idx₁ o) ≡ marginal-to-residue (echo-idx₂ o)
  residue-loses-index _ = refl

----------------------------------------------------------------------
-- Worked concrete instance: Bool-indexed sampling over ℕ outcomes.
--
-- The minimum-non-trivial sampling setup: ℕ outcomes (the value a
-- consumer reads), Bool sample indices (a 1-bit run identifier).
-- Distinguishability of `true`/`false` is the standard `λ ()`.
----------------------------------------------------------------------

bool-indexed-nat-sampling : Sampling
bool-indexed-nat-sampling = record
  { Outcome      = ℕ
  ; Index        = Bool
  ; idx₁         = true
  ; idx₂         = false
  ; idx-distinct = λ ()
  }

----------------------------------------------------------------------
-- Matched-negative block (HONEST BOUND, per R-2026-05-18 discipline).
--
-- The following properties are deliberately NOT proved by this
-- module. `⊤`-aliased so `grep NotProved` catches them.
----------------------------------------------------------------------

NotProved-measure-preserving : Set
NotProved-measure-preserving = ⊤

NotProved-probability-monad : Set
NotProved-probability-monad = ⊤

NotProved-Kantorovich-distance : Set
NotProved-Kantorovich-distance = ⊤

NotProved-coupling-aware : Set
NotProved-coupling-aware = ⊤

NotProved-randomness-extraction : Set
NotProved-randomness-extraction = ⊤

----------------------------------------------------------------------
-- Companion remark.
--
-- The four headlines of `SamplingTheorems` capture the structural
-- fact of support information loss at the audience level:
--
--   1. The marginal is non-injective on different-index samples.
--   2. The Echo at any outcome has at least two carriers, one per
--      sampling-index value.
--   3. The Echo's carriers distinguish the lost index.
--   4. The residue lowering forgets the index — distinguishable
--      echoes become residue-indistinguishable.
--
-- *Why this differs from `EchoProvenance` despite the same
-- formal shape.* Provenance discourse cares about "where this
-- value came from" annotations on tuples in databases. Support-
-- tracking discourse cares about "which draw produced this
-- outcome" annotations on samples in randomised computations.
-- The mathematical content is the same Σ-with-tag pattern; the
-- audience-side meaning differs. Both modules sit in this repo
-- because audience reach matters — a database engineer reading
-- `EchoProvenance` and a probabilistic-programming researcher
-- reading `EchoProbabilisticSupport` find the same theorem
-- under different names, and that's the point of the audience-
-- move tier.
--
-- *Why this is NOT probability theory.* The `Sampling` record
-- has no measure on `Outcome`, no measurable structure on
-- `Index`, no probability-monad / Giry-monad / probabilistic-
-- powerdomain operations, no almost-everywhere quantifiers, no
-- distributional equivalences. It is a TYPE-LEVEL support-set
-- tracking. The matched-negative block above pins this scope
-- explicitly: claims about measure preservation, Kantorovich
-- distance, coupling, randomness extraction, or probabilistic-
-- monad laws are out of scope. Future audience-extensions (e.g.
-- `EchoMeasure.agda` adding measure structure, or
-- `EchoCoupling.agda` adding two-sample reasoning) can layer
-- additional theorems on top, with `Sampling` as the minimum-
-- fact baseline.
--
-- The next audience-facing module per the GPT-recommended order
-- is `EchoDifferential.agda` (sensitivity / perturbation
-- tracking — independent of EchoProbabilisticSupport).
----------------------------------------------------------------------
