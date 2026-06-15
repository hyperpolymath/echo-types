{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo.Separation.NotResourceInstance — the anti-collapse module.
--
-- This is the curated public statement of the foundation's boundary
-- invariant:
--
--   Echo IS-NOT a resource instance.
--
-- Echo is an orthogonal indexed/residual modality. A resource algebra
-- may *measure* Echo residues, but it does not *define* Echo. This
-- module establishes that invariant in two complementary, mechanised
-- ways — it does NOT claim the impossible universal "no semiring can
-- ever encode any echo-like quotient"; it claims the useful project
-- invariant that the proof-relevant Echo structure is not determined
-- by any semiring-valued grade/measure, so any such measure is a
-- lossy observation.
--
-- Pillar 1 (structural — the index axis is real).
--   The characteristic degradation law `degrade-compose` is carried
--   PRECISELY by thinness of the echo index, not by generic
--   Σ-functoriality. The separating model `EchoSeparating` keeps the
--   generic Σ laws (`map-over-id` / `map-over-comp`) but drops
--   thinness, and composition then breaks at a checked `true ≢ false`.
--   So the graded Echo structure is genuine structure, not bookkeeping
--   reducible to a measure. Re-exported here as the stable name
--   `echo-degrade-not-generic-sigma`.
--
-- Pillar 2 (measure axis — the measure is lossy).
--   A residue measure (here the canonical trivial-residue projection)
--   sends two genuinely-distinct Echo residues to the SAME value,
--   while the Echo modality keeps them apart. Equal residue measure
--   therefore does NOT imply equal Echo: the measure is a lossy
--   observation, not the definition of Echo.

module Echo.Separation.NotResourceInstance where

open import Level using (Level)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Echo using (Echo)
open import EchoCharacteristic
  using ( collapse; echo-true; echo-false; echo-true≢echo-false
        ; visible; state₁; state₂; state₁≢state₂
        )
open import EchoResidue
  using (EchoR; TrivialCert; collapse-to-residue; collapse-residue-same)

----------------------------------------------------------------------
-- Pillar 1 — structural separation (re-exported from EchoSeparating).
--
-- The separating model and the checked failure of `degrade-compose`
-- when thinness is removed. Re-exported under stable names so the
-- anti-collapse argument has a single discoverable home.
----------------------------------------------------------------------

open import EchoSeparating public
  using ( SepDegradeCompose
        ; sep-degrade-compose-fails
        ; sep-order-not-prop
        ; sep-map-over-id
        ; sep-map-over-comp
        )

-- Stable, discoverable name for the structural separation: degrading
-- is NOT a generic Σ-consequence — drop thinness of the index (the
-- only hypothesis the separating model removes) and the
-- characteristic path-independence law `degrade-compose` is refuted
-- at a concrete `true ≢ false` witness. The graded Echo structure is
-- therefore carried by the *index*, an axis no semiring grade
-- supplies.
echo-degrade-not-generic-sigma : ¬ SepDegradeCompose
echo-degrade-not-generic-sigma = sep-degrade-compose-fails

----------------------------------------------------------------------
-- Pillar 2 — measure separation (the residue measure is lossy).
--
-- The canonical residue measure is the trivial-residue projection
-- `collapse-to-residue : Echo collapse tt → EchoR ⊤ TrivialCert tt`.
-- It is a lossy observation: it forgets the proof-relevant witness,
-- so it cannot tell `echo-true` from `echo-false`.
----------------------------------------------------------------------

residue-measure : Echo collapse tt → EchoR ⊤ TrivialCert tt
residue-measure = collapse-to-residue

-- Two genuinely-distinct Echo residues over the same visible output.
E₁ E₂ : Echo collapse tt
E₁ = echo-true
E₂ = echo-false

-- (a) Their residue measures are EQUAL.
measure-agrees : residue-measure E₁ ≡ residue-measure E₂
measure-agrees = collapse-residue-same

-- (b) Yet they are distinguished by an Echo-observable property:
--     they are unequal as echoes.
echo-distinguishes : E₁ ≢ E₂
echo-distinguishes = echo-true≢echo-false

----------------------------------------------------------------------
-- Headline anti-collapse theorem (Target shape of the contract).
--
-- There exist two Echo residues E₁, E₂ with
--     residue-measure E₁ ≡ residue-measure E₂
-- but
--     E₁ ≢ E₂.
-- Equal residue measure does not imply equal Echo. This is the
-- precise reason `Echo IS-NOT a resource instance`: a measure cannot
-- be the identity criterion of Echo, because it already identifies
-- residues that Echo keeps apart.
----------------------------------------------------------------------

equal-measure-does-not-imply-equal-echo :
  Σ (Echo collapse tt) (λ e₁ →
  Σ (Echo collapse tt) (λ e₂ →
    (residue-measure e₁ ≡ residue-measure e₂) × (e₁ ≢ e₂)))
equal-measure-does-not-imply-equal-echo =
  E₁ , E₂ , measure-agrees , echo-distinguishes

----------------------------------------------------------------------
-- Generalised form: NO measure that agrees on `echo-true` and
-- `echo-false` can be injective on Echo residues.
--
-- For any observation `m : Echo collapse tt → M` into any target `M`
-- (in particular any semiring-/resource-algebra-valued residue
-- measure that factors through the trivial residue), if `m` agrees on
-- the two distinct echoes then it identifies two distinct residues.
-- So a residue measure is always a lossy observation of Echo, never a
-- faithful encoding of it.
----------------------------------------------------------------------

measure-not-injective :
  ∀ {ℓ} {M : Set ℓ} (m : Echo collapse tt → M) →
  m echo-true ≡ m echo-false →
  Σ (Echo collapse tt) (λ e₁ →
  Σ (Echo collapse tt) (λ e₂ →
    (m e₁ ≡ m e₂) × (e₁ ≢ e₂)))
measure-not-injective m agree =
  echo-true , echo-false , agree , echo-true≢echo-false

----------------------------------------------------------------------
-- Sharper witness: the measure is lossy even when it is genuinely
-- INFORMATIVE.
--
-- The witnesses above use the trivial-residue projection, whose target
-- `EchoR ⊤ TrivialCert tt` is a one-point set — a referee could object
-- that "of course a measure into a point can't separate anything".
-- This sharper witness rebuts that. It uses the structured-loss
-- example `visible : Bool × Bool → Bool` (forget the second bit) and a
-- measure that actually READS the residue and lands in a TWO-point
-- carrier `Bool`:
--
--   visible-measure ((b , _) , _) = b
--
-- This measure is genuinely informative — `visible-measure-informative`
-- exhibits two echoes it separates (it recovers the visible bit). Yet
-- it CANNOT separate `state₁` from `state₂`, two residues that agree on
-- the visible bit but differ on the forgotten one. So even a measure
-- that inspects the residue and discriminates elsewhere is a lossy
-- observation of Echo: equal measure still does not imply equal Echo.
----------------------------------------------------------------------

visible-measure : ∀ {y : Bool} → Echo visible y → Bool
visible-measure ((b , _) , _) = b

-- The measure is non-degenerate: it returns different values at
-- different visible outputs (so it is not the constant-into-a-point
-- map that the trivial residue measure is).
visible-measure-informative :
  Σ (Echo visible true) (λ e₁ →
  Σ (Echo visible false) (λ e₂ →
    visible-measure e₁ ≢ visible-measure e₂))
visible-measure-informative =
  state₁ , ((false , true) , refl) , λ ()

-- Yet at a fixed visible output it identifies two distinct residues.
visible-measure-agrees : visible-measure state₁ ≡ visible-measure state₂
visible-measure-agrees = refl

equal-informative-measure-does-not-imply-equal-echo :
  Σ (Echo visible true) (λ e₁ →
  Σ (Echo visible true) (λ e₂ →
    (visible-measure e₁ ≡ visible-measure e₂) × (e₁ ≢ e₂)))
equal-informative-measure-does-not-imply-equal-echo =
  state₁ , state₂ , visible-measure-agrees , state₁≢state₂
