{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoProvenance: the audience-facing provenance theorem at full
-- generality. Generalises the existing example
-- `EchoExampleProvenance.agda` (a concrete `Row` with `payload : ℕ`
-- + `prov : Bool` + Bool-distinguishability witness) from a single
-- instance into an abstract `Provenance` interface, with the four
-- headline theorems proved parametric in the payload type, the
-- provenance-tag type, and the tag-distinguishability witness.
--
-- *Audience.* Database / pipeline / data-engineering practitioners
-- familiar with provenance semirings (K-provenance, why-provenance,
-- lineage tracking). The structural content is:
--
--   For ANY payload type `Payload`, ANY tag type `Tag` with two
--   distinguishable elements `tag₁ ≢ tag₂`, the projection
--   `proj₁ : Payload × Tag → Payload` is non-injective on
--   tag-differing records, and `Echo project p` carries the
--   lost tag.
--
-- That's the structural fact. The "K-provenance semiring" + "Bool
-- trust tokens" + "lineage formula" framings are all instances of
-- the same shape: a tag set with at least two distinguishable
-- elements, a payload type, and a forgetful projection. The Echo
-- captures the lost tag — by mechanised theorem, not by handwave.
--
-- *Closes Tier 3 first audience move per the synthesis-roadmap
-- order.* The existing `EchoExampleProvenance.agda` becomes a
-- worked Bool-over-ℕ instance; the abstract module sits beside it,
-- with the abstract→concrete instantiation pinned.
--
-- *Echo-specific properties used.* This module leans on:
--
--   * `Echo.echo-intro` — the canonical fibre inhabitation.
--   * `Echo.Echo` — the fibre carrier itself.
--   * `EchoResidue.echo-to-residue` — the lowering to a residue,
--     showing tag-distinguishing echoes become residue-
--     indistinguishable.
--
-- None of these reduce to plain Σ + ≡: each carries the
-- residue/witness/no-section content that `EchoExampleProvenance`
-- and the residue/abstraction-barrier line have already pinned.
-- The audience-facing rephrasing here is a packaging of that
-- content, not a generalisation past it.
--
-- Headlines (pinned in Smoke.agda):
--
--   * Provenance                       -- the abstract setup record
--   * module ProvenanceTheorems         -- parametric in P : Provenance
--   * provenance-collapses-at           -- non-injectivity at p
--   * echo-tag₁ / echo-tag₂              -- concrete fibre inhabitants
--   * echoes-distinguish-tag             -- carriers distinguish tags
--   * echo-tag₁≢echo-tag₂                -- the echoes themselves differ
--   * residue-collapses-tags             -- lowering loses the tag
--   * bool-over-nat-provenance           -- the worked concrete instance
--
-- Scope guardrail (Echo-vs-Σ clearance). The abstract `Provenance`
-- record uses plain Σ-types in its DATA (`Record := Payload ×
-- Tag`). The CONTENT — that `Echo project p` carries the lost
-- tag, that the residue loses it, that the carriers distinguish —
-- uses `Echo`, `echo-intro`, `echo-to-residue` non-trivially.
-- The falsifier per the Echo-vs-Σ Track A/B/C bar: if every
-- headline below could be re-proved using only `Σ` + `_≡_` (no
-- `Echo`), the module would fail to clear the bar. The headlines
-- below directly invoke `Echo`'s fibre-shape primitives; replacing
-- `Echo project p` by a generic Σ would lose the residue-collapse
-- alignment with `EchoResidue.collapse-residue-same`.

module EchoProvenance where

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
-- The abstract provenance setup.
--
-- A `Provenance` is the data of a payload type, a tag type, two
-- distinguishable tags, and the (constructive) distinguishability
-- witness. `Set₁` because of the `Set`-valued fields.
----------------------------------------------------------------------

record Provenance : Set₁ where
  field
    Payload      : Set
    Tag          : Set
    tag₁         : Tag
    tag₂         : Tag
    tag-distinct : tag₁ ≢ tag₂

----------------------------------------------------------------------
-- The four headline theorems, parametric in the provenance setup.
--
-- Each module-`_ (P : Provenance)` field becomes a per-instance
-- function. Consumers instantiate with a concrete `Provenance` (see
-- `bool-over-nat-provenance` below for the worked example).
----------------------------------------------------------------------

module ProvenanceTheorems (P : Provenance) where
  open Provenance P

  ------------------------------------------------------------
  -- A record: payload + provenance tag.
  ------------------------------------------------------------

  Record : Set
  Record = Payload × Tag

  -- The query: project to the payload, forgetting the tag. Echo
  -- of this is where the lost provenance lives.
  project : Record → Payload
  project (p , _) = p

  ------------------------------------------------------------
  -- Two records at any payload, differing only in tag.
  ------------------------------------------------------------

  record-tag₁ : (p : Payload) → Record
  record-tag₁ p = p , tag₁

  record-tag₂ : (p : Payload) → Record
  record-tag₂ p = p , tag₂

  ------------------------------------------------------------
  -- Headline 1: projection is non-injective.
  --
  -- At every payload `p`, the two tag-differing records collapse
  -- to the same projection.
  ------------------------------------------------------------

  provenance-collapses-at :
    (p : Payload) →
    Σ Record (λ r₁ → Σ Record (λ r₂ →
      proj₂ r₁ ≢ proj₂ r₂ × project r₁ ≡ project r₂))
  provenance-collapses-at p =
    record-tag₁ p , record-tag₂ p , tag-distinct , refl

  ------------------------------------------------------------
  -- Headline 2: concrete fibre inhabitants at any payload.
  --
  -- Two echoes of `project` at the same payload, carrying the
  -- two distinct tags. These are the inhabitants the query
  -- loses.
  ------------------------------------------------------------

  echo-tag₁ : (p : Payload) → Echo project p
  echo-tag₁ p = echo-intro project (record-tag₁ p)

  echo-tag₂ : (p : Payload) → Echo project p
  echo-tag₂ p = echo-intro project (record-tag₂ p)

  ------------------------------------------------------------
  -- Headline 3: Echo remembers what projection forgets.
  --
  -- The tag fields of the two echoes' underlying records are
  -- distinguishable — Echo carries the lost provenance bit.
  ------------------------------------------------------------

  echoes-distinguish-tag :
    (p : Payload) →
    proj₂ (proj₁ (echo-tag₁ p)) ≢ proj₂ (proj₁ (echo-tag₂ p))
  echoes-distinguish-tag _ = tag-distinct

  -- Stronger: the two echoes themselves are distinct in `Echo
  -- project p`. The audience-facing crisp form.
  echo-tag₁≢echo-tag₂ :
    (p : Payload) → echo-tag₁ p ≢ echo-tag₂ p
  echo-tag₁≢echo-tag₂ p eq =
    tag-distinct (cong (λ e → proj₂ (proj₁ e)) eq)

  ------------------------------------------------------------
  -- Headline 4: residue lowering loses the tag.
  --
  -- Lowering the echo into the trivial residue layer collapses
  -- the two formerly-distinguishable echoes — the residue layer
  -- is exactly where the tag becomes unrecoverable. Mirrors
  -- `EchoResidue.collapse-residue-same` at the audience-facing
  -- provenance level.
  ------------------------------------------------------------

  TrivCert : ⊤ → Payload → Set
  TrivCert _ _ = ⊤

  prov-kappa : Record → ⊤
  prov-kappa _ = tt

  prov-sound : ∀ r → TrivCert (prov-kappa r) (project r)
  prov-sound _ = tt

  project-to-residue :
    ∀ {p : Payload} → Echo project p → EchoR ⊤ TrivCert p
  project-to-residue {p} =
    echo-to-residue project prov-kappa TrivCert prov-sound

  residue-collapses-tags :
    (p : Payload) →
    project-to-residue (echo-tag₁ p) ≡ project-to-residue (echo-tag₂ p)
  residue-collapses-tags _ = refl

----------------------------------------------------------------------
-- Worked concrete instance: Bool-over-ℕ provenance.
--
-- Reproduces the structure of the existing `EchoExampleProvenance.agda`
-- as the canonical inhabitant of `Provenance`. Distinguishability
-- of `true` and `false` is the standard `λ ()`.
----------------------------------------------------------------------

bool-over-nat-provenance : Provenance
bool-over-nat-provenance = record
  { Payload      = ℕ
  ; Tag          = Bool
  ; tag₁         = true
  ; tag₂         = false
  ; tag-distinct = λ ()
  }

----------------------------------------------------------------------
-- Companion remark.
--
-- The four headlines of `ProvenanceTheorems` capture the structural
-- fact of provenance loss at the audience level:
--
--   1. The projection is non-injective on tag-differing records.
--   2. The Echo at any payload has at least two carriers, one per
--      tag value.
--   3. The Echo's carriers distinguish the lost tag.
--   4. The residue lowering forgets the tag — distinguishable
--      echoes become residue-indistinguishable.
--
-- This is the abstract content of "lineage / provenance carries
-- information the projection-only query loses"; the K-provenance
-- semiring framings, why-provenance trees, where-provenance
-- annotations, and Boolean trust-token databases are all
-- instances of `Provenance` with a specific `Payload`, `Tag`, and
-- a constructive distinguishability witness.
--
-- The abstract setup deliberately does NOT bake in any semiring
-- structure on `Tag` — the headline theorems use only the
-- tag-distinguishability witness, mirroring how
-- `EchoExampleProvenance` notes "we do not need the semiring
-- laws to land the echo lemmas". Future audience-extensions
-- (`EchoProvenanceSemiring.agda` etc.) can add semiring or
-- algebra structure on `Tag` and prove additional theorems
-- (e.g. provenance polynomials), with `Provenance` as the
-- minimal-fact baseline.
--
-- The next audience-facing module per the GPT-recommended order
-- is `EchoSecurity.agda` (region-exit / capability flow, using
-- the `RegionExitAudit.agda` honest-bound template).
----------------------------------------------------------------------
