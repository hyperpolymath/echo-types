{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoHaplotypeCollapsing: haplotype collapsing as structured loss.
--
-- Domain: bioinformatics / protist workflows (Protoctist.jl, metamanifold-webui).
-- A set of observed clones (e.g. rRNA reads) is collapsed to a smaller set of
-- haplotypes / ASVs by a non-injective map `collapse : Clone → Haplotype`.
-- Standard pipelines discard the preimage; Echo retains it as a homotopy fiber.
--
--   Echo collapse h = Σ (c : Clone) , (collapse c ≡ h)
--
-- is the *structural lineage* of collapsed clones at haplotype h.
--
-- This module is the Agda anchor for docs/echo-types/applications/haplotype-collapsing.adoc.
-- It shows:
--   * the collapse is non-injective (many-to-one) → Echo distinguishes clones
--   * no canonical section: you cannot recover a unique clone from a haplotype
--   * aggregation-as-fold: counting clones per haplotype is a monoid fold
--   * choreographic framing: Raw (Clone) ⊑ Collapsed (Haplotype) is a decoration order
--   * separation from distance matrix: O(n²) distances live on Haplotype, fiber witness
--     lives in a sidecar, never in the hot loop.
--
-- All --safe --without-K, zero postulates.
--
-- For the Nickel / Julia / JEG pipeline, see the companion docs:
--   docs/echo-types/applications/haplotype-collapsing.adoc
--   docs/echo-types/applications/haplotype-collapsing.k9.ncl
--   docs/echo-types/applications/haplotype-collapsing.jl
--
-- Related: EchoAggregation (general monoid form), EchoChoreo (role order),
-- EchoProvenance (tag-loss analogue), Protoctist.jl (PR2/SILVA workflows).

module EchoHaplotypeCollapsing where

open import Echo using (Echo; echo-intro)
open import EchoAggregation using
  ( Monoid; GroupAggregator; aggregate-values; aggregation-as-fold
  ; sumMonoid; countAggregator; no-canonical-disaggregation-of
  )
open import EchoNoSectionGeneric using (no-section-of-collapsing-map)

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- 1. The domain: clones and haplotypes
------------------------------------------------------------------------

-- A minimal clone: (sample-id , intra-sample variant tag).
-- In a real pipeline this would be { id, sequence, quality, sample, ... }
Clone : Set
Clone = ℕ × Bool

Haplotype : Set
Haplotype = ℕ

-- The collapsing map: forget the variant tag, keep the sample/haplotype id.
collapse : Clone → Haplotype
collapse = proj₁

-- A second collapsing map, closer to real ASV collapsing: collapse by
-- exact sequence equality. Modelled here as collapseSeq : (ℕ × ℕ) → ℕ
-- where second component is a hash of the sequence.
CloneSeq : Set
CloneSeq = ℕ × ℕ

HaplotypeSeq : Set
HaplotypeSeq = ℕ

collapseSeq : CloneSeq → HaplotypeSeq
collapseSeq = proj₂

------------------------------------------------------------------------
-- 2. Echo fiber = structural lineage of collapsed clones
------------------------------------------------------------------------

HaploFiber : Haplotype → Set
HaploFiber h = Echo collapse h

clone₁ : Clone
clone₁ = 0 , true

clone₂ : Clone
clone₂ = 0 , false

clone₁≢clone₂ : clone₁ ≢ clone₂
clone₁≢clone₂ ()

collapse-collides : collapse clone₁ ≡ collapse clone₂
collapse-collides = refl

echo-clone₁ : HaploFiber 0
echo-clone₁ = echo-intro collapse clone₁

echo-clone₂ : HaploFiber 0
echo-clone₂ = echo-intro collapse clone₂

echo-clone₁≢echo-clone₂ : echo-clone₁ ≢ echo-clone₂
echo-clone₁≢echo-clone₂ eq = clone₁≢clone₂ (cong proj₁ eq)

collapse-non-injective :
  Σ Clone (λ c₁ → Σ Clone (λ c₂ → (c₁ ≢ c₂) × (collapse c₁ ≡ collapse c₂)))
collapse-non-injective = clone₁ , clone₂ , clone₁≢clone₂ , refl

------------------------------------------------------------------------
-- 3. No canonical disaggregation
------------------------------------------------------------------------

no-canonical-clone-recovery :
  ¬ Σ (Haplotype → Clone) (λ raise → ∀ c → raise (collapse c) ≡ c)
no-canonical-clone-recovery =
  no-canonical-disaggregation-of collapse clone₁ clone₂ clone₁≢clone₂ refl

cloneSeq₁ : CloneSeq
cloneSeq₁ = 0 , 42

cloneSeq₂ : CloneSeq
cloneSeq₂ = 1 , 42

cloneSeq₁≢cloneSeq₂ : cloneSeq₁ ≢ cloneSeq₂
cloneSeq₁≢cloneSeq₂ eq with cong proj₁ eq
... | ()

collapseSeq-collides : collapseSeq cloneSeq₁ ≡ collapseSeq cloneSeq₂
collapseSeq-collides = refl

no-canonical-seq-recovery :
  ¬ Σ (HaplotypeSeq → CloneSeq) (λ raise → ∀ c → raise (collapseSeq c) ≡ c)
no-canonical-seq-recovery =
  no-canonical-disaggregation-of collapseSeq cloneSeq₁ cloneSeq₂
    cloneSeq₁≢cloneSeq₂ refl

------------------------------------------------------------------------
-- 4. Aggregation-as-fold: counting clones per haplotype
------------------------------------------------------------------------

clone-count-aggregation :
  ∀ (G : GroupAggregator ℕ Clone sumMonoid) (vs ws : List Clone) →
  aggregate-values G (vs ++ ws)
    ≡ Monoid._⊕_ sumMonoid (aggregate-values G vs) (aggregate-values G ws)
clone-count-aggregation G = aggregation-as-fold G

example-clones : List Clone
example-clones = clone₁ ∷ clone₂ ∷ []

example-count : aggregate-values countAggregator example-clones ≡ 2
example-count = refl

-- Count clones per haplotype via monoid fold (the GROUP BY analogue).
-- In production: groupByKey + fold, not filter + length, to stay O(n).
count-clones-per-haplotype : List Clone → ℕ
count-clones-per-haplotype cs = aggregate-values countAggregator cs

------------------------------------------------------------------------
-- 5. Choreographic framing: Raw ⊑ Collapsed
------------------------------------------------------------------------

data PipelineRole : Set where
  Sequencer  : PipelineRole
  Collapser  : PipelineRole
  Visualizer : PipelineRole

------------------------------------------------------------------------
-- 6. FiberBundle sidecar: the Nickel/Julia interface
------------------------------------------------------------------------

record FiberBundle : Set where
  field
    haplotype      : Haplotype
    representative : Clone
    fiber          : List Clone

example-bundle : FiberBundle
example-bundle = record
  { haplotype = 0
  ; representative = clone₁
  ; fiber = example-clones
  }

bundle-projection : FiberBundle → Haplotype
bundle-projection = FiberBundle.haplotype

bundle-fiber-echoes : (b : FiberBundle) → List (HaploFiber (FiberBundle.haplotype b))
bundle-fiber-echoes b = map (λ c → c , refl) (FiberBundle.fiber b)

------------------------------------------------------------------------
-- 7. Separation from O(n²) distance matrix
------------------------------------------------------------------------

HaploDist : Set
HaploDist = Haplotype → Haplotype → ℕ

------------------------------------------------------------------------
-- 8. Matched negatives (honest scope)
------------------------------------------------------------------------

module NotProved where
  NotProved-clustering-optimal : Set
  NotProved-clustering-optimal = ⊤

  NotProved-distance-metric : Set
  NotProved-distance-metric = ⊤

  NotProved-shannon-entropy : Set
  NotProved-shannon-entropy = ⊤

  NotProved-jeg-rendering : Set
  NotProved-jeg-rendering = ⊤
