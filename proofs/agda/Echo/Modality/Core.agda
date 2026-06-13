{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo.Modality.Core — the stable exported interface for the *Echo
-- modality*: the proof-relevant residual structure indexed by a thin
-- echo index (`Echo.Index.ThinPoset`).
--
-- This is the second curated public-surface module of the Echo
-- foundation (see `FOUNDATION_CONTRACT.md`). Importing it gives, under
-- one stable API:
--
--   * the fibre functor `Echo` (the measure-independent kernel root);
--   * the concrete index-graded modality `GEcho` with its `degrade`
--     reindexing action and the degradation laws `degrade-id`,
--     `degrade-comp`, `degrade-compose`;
--   * the generic no-section / irreversibility theorem;
--   * the abstract `EchoModality` contract (re-exported from
--     `Echo.Modality.Interface`) that downstream languages instantiate,
--     together with the canonical instance `grade-echoModality`.
--
-- Naming. The bare names `degrade` / `degrade-id` / `degrade-compose`
-- in this module are the CONCRETE operations on `GEcho`. The abstract
-- record's same-named projections are reached qualified as
-- `EchoModality.degrade` (etc.); downstream code that `open`s an
-- `EchoModality` instance recovers the bare names in its own scope.
--
-- MEASURE-INDEPENDENCE INVARIANT (load-bearing). This module imports
-- NO semiring / resource-algebra machinery. Its entire cone is
-- `Echo`, `EchoGraded`, `EchoNoSectionGeneric` (+ their stdlib-only
-- dependencies) and the `Echo.Index.ThinPoset` / `Echo.Modality.Interface`
-- interfaces. The Echo modality is defined and its laws are proved
-- WITHOUT any residue *measure*. A resource algebra may later
-- *observe* residues (`Echo.Measure.Interface`), but it is never
-- imported here and never defines the modality.
--
--   Echo IS-NOT a resource instance.
--
-- The proof-relevant content of `degrade` is carried by the thin
-- order of the index, not by any semiring-valued grade. The
-- separating evidence is in `Echo.Separation.NotResourceInstance`.

module Echo.Modality.Core where

open import Level using (Level; suc; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

----------------------------------------------------------------------
-- Re-export the echo index interface and the abstract modality
-- contract (the record TYPE only — its bare projections are kept out
-- of scope so the concrete `degrade` below owns the bare name).
----------------------------------------------------------------------

open import Echo.Index.ThinPoset public
open import Echo.Modality.Interface public using (EchoModality)

----------------------------------------------------------------------
-- Re-export the fibre modality (the measure-independent kernel root).
--
-- `Echo f y := Σ (x : A) , (f x ≡ y)` — the structured remainder of
-- an information-losing `f`. This is the funext-free kernel
-- (`EchoKernel`); we surface the load-bearing fibre API here so the
-- foundation contract has a single public entry point.
----------------------------------------------------------------------

open import Echo public
  using ( Echo ; echo-intro
        ; MapOver ; map-over ; map-over-id ; map-over-comp
        ; map-square
        )

----------------------------------------------------------------------
-- Re-export the concrete index-graded modality from `EchoGraded`.
--
--   GEcho           : Grade → Set         -- the index-graded carrier
--   degrade         : g₁ ≤g g₂ → GEcho g₁ → GEcho g₂
--   degrade-comp    : associativity of degrade along a chosen factoring
--   degrade-compose : path-INDEPENDENCE of degrade (the characteristic
--                     law; carried by thinness of the index)
--   degrade-via-join: join-action specialisation
----------------------------------------------------------------------

open import EchoGraded public
  using ( GEcho
        ; degrade
        ; degrade-comp
        ; degrade-compose
        ; degrade-via-join
        )

----------------------------------------------------------------------
-- degrade-id (the identity / unit law for degradation).
--
-- `EchoGraded` proves `degrade-comp` and `degrade-compose` but does
-- not name the unit law. The stable interface needs it: degrading
-- along ANY reflexive index arrow is the identity. By thinness
-- (`≤g-prop`) every `p : g ≤g g` equals the canonical reflexive
-- constructor, on which `degrade` is definitionally the identity.
----------------------------------------------------------------------

degrade-id :
  ∀ {g : Grade} (p : g ≤g g) (x : GEcho g) → degrade p x ≡ x
degrade-id {keep}    p x rewrite ≤g-prop p keep≤keep       = refl
degrade-id {residue} p x rewrite ≤g-prop p residue≤residue = refl
degrade-id {forget}  p x rewrite ≤g-prop p forget≤forget   = refl

----------------------------------------------------------------------
-- Re-export the generic no-section / irreversibility theorem.
--
-- `no-section-of-collapsing-map`: any collapsing map (two distinct
-- elements landing on the same image) admits NO section. This is the
-- structural source of Echo's irreversibility — and it is a property
-- of NON-INJECTIVITY, proved without any measure. No-section holds
-- "where applicable": degradation arrows that genuinely lose
-- information (e.g. `keep → forget`) have no section, while reflexive
-- arrows (`keep → keep`) are identities and trivially do.
----------------------------------------------------------------------

open import EchoNoSectionGeneric public
  using ( no-section-of-collapsing-map
        ; no-section-when-non-injective-at-y
        )

----------------------------------------------------------------------
-- The canonical instance of the abstract `EchoModality` contract:
-- the three-point loss modality over the canonical echo index.
-- Witnesses that the abstract interface is inhabitable by the proven
-- `EchoGraded` structure — the concrete `degrade` / `degrade-id` /
-- `degrade-compose` above ARE the fields.
----------------------------------------------------------------------

grade-echoModality : EchoModality grade-thinPoset 0ℓ
grade-echoModality = record
  { ⟦_⟧             = GEcho
  ; degrade         = degrade
  ; degrade-id      = degrade-id
  ; degrade-compose = degrade-compose
  }
