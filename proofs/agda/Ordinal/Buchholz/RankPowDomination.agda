{-# OPTIONS --safe --without-K #-}

-- Slice 2-bplus of the head-Ω domination route — the full WfCNF-
-- carrier domination lemma.
--
-- Composes the abstractions and per-marker dominances from Slice 1
-- + Slice 2 + Slice 2-omega in `Ordinal.Buchholz.RankPow` with the
-- option-(b) head-Ω inversion lemmas from
-- `Ordinal.Buchholz.HeadOmegaInversion` into:
--
--   rank-pow-dominated-by-head-Ω :
--     ∀ {t} → WfCNF t → rank-pow t <′ ω-rank-pow-succ (head-Ω t)
--
-- The bzero case discharges directly via `ω-rank-pow-succ-pos`
-- (no `NonBzero` premise needed); the atomic cases bOmega/bpsi
-- collapse to `ω-rank-pow-<-succ`; the bplus case structurally
-- recurses on the WfCNF carrier and combines an IH bound on the
-- left summand with a head-Ω-inversion-driven bound on the right
-- summand via the additive-principal closure of `ω-rank-pow-succ`.
--
-- ## What lands
--
--   * `ω-rank-pow-mono-≤Ω`             — `≤Ω → ≤′` lifting.
--   * `ω-rank-pow-succ-pos`            — positivity at both branches.
--   * `additive-principal-ω-rank-pow-succ`
--                                       — additive-principal closure
--                                         of `ω-rank-pow-succ` at both
--                                         branches.
--   * `rank-pow-dominated-by-head-Ω`   — THE HEADLINE.
--
-- ## What's deferred
--
--   * The headline `<ᵇ-+1` joint-bplus discharge
--     (`rank-mono-<ᵇ-+1-via-head-Ω`) — Slice 3.
--   * Full `rank-pow-mono-<ᵇ⁻` umbrella composition — Slice 4.
--
-- ## Design notes
--
-- * The `NonBzero` premise originally planned in `RankPow.agda`'s
--   Slice 2-bplus TODO turned out unnecessary — `rank-pow bzero =
--   oz` is *strictly* below `ω-rank-pow-succ (fin 0) = ω^2` via
--   `ω^_-pos 2`, so the bzero case is covered uniformly without a
--   discriminator.  This simplifies the structural recursion's
--   bplus case (no special handling for `x = bzero` of `bplus x y`).
-- * The bplus case feeds `additive-principal-ω-rank-pow-succ {head-Ω x}`
--   the IH on `x` plus a per-atomic-y bound from `rank-y-bound`.
--   The atomic-y bound uses `head-Ω-inv-bOmega` / `head-Ω-inv-bpsi`
--   to convert the WfCNF tail bound `y ≤ᵇ x` into a head-Ω
--   inequality on the target, with no rank-mono dependency at any
--   point in the chain (option (b) discipline preserved).
-- * The `additive-principal-ω-rank-pow-succ` ω-branch proof mirrors
--   `Ordinal.Brouwer.OmegaPow.additive-principal` (lines 363–401) with
--   `ω^ n` replaced by `ω-rank-pow ω` and `·ℕ-add-≤` consumed at
--   the new base.

module Ordinal.Buchholz.RankPowDomination where

open import Data.Nat.Base    using (ℕ; suc; _+_; s≤s)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base    using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; fin
  ; ω
  ; _<Ω_
  ; _≤Ω_
  ; fin≤fin
  ; fin≤ω
  ; ω≤ω
  )
open import Ordinal.Brouwer using
  ( Ord
  ; oz
  ; osuc
  )
open import Ordinal.Brouwer.Arithmetic using (_⊕_)
open import Ordinal.Brouwer.Phase13 using
  ( _≤′_
  ; _<′_
  ; ≤′-refl
  ; ≤′-trans
  ; ≤′-self-osuc
  ; f-in-lim′
  ; ⊕-mono-≤-left
  ; ⊕-mono-<-right
  )
open import Ordinal.Brouwer.OmegaPow using
  ( ω^_
  ; ω^_-pos
  ; ω^-mono-≤
  ; _·ℕ_
  ; additive-principal
  ; ·ℕ-add-≤
  )
open import Ordinal.Buchholz.Syntax using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.Order using (_<ᵇ_)
open import Ordinal.Buchholz.WellFormedCNF using
  ( Atomic
  ; atomic-bzero
  ; atomic-bomega
  ; atomic-bpsi
  ; _≤ᵇ_
  ; WfCNF
  ; wf-cnf-bzero
  ; wf-cnf-bomega
  ; wf-cnf-bpsi
  ; wf-cnf-bplus
  )
open import Ordinal.Buchholz.HeadOmega using (head-Ω)
open import Ordinal.Buchholz.HeadOmegaInversion using
  ( head-Ω-inv-bOmega
  ; head-Ω-inv-bpsi
  )
open import Ordinal.Buchholz.RankPow using
  ( ω-rank-pow
  ; ω-rank-pow-pos
  ; ω-rank-pow-mono
  ; rank-pow
  ; ω-rank-pow-succ
  ; ω-rank-pow-<-succ
  )

----------------------------------------------------------------------
-- Inline utilities: <′→≤′  +  ≤′-<′-trans
----------------------------------------------------------------------

-- Lift a strict ordering to non-strict.  Definitional: `α <′ β` is
-- `osuc α ≤′ β`, and `α ≤′ osuc α` chains to give `α ≤′ β`.
<′→≤′ : ∀ {α β} → α <′ β → α ≤′ β
<′→≤′ {α} {β} p = ≤′-trans {α} {osuc α} {β} (≤′-self-osuc α) p

-- Compose `α ≤′ β` with `β <′ γ` to get `α <′ γ`.  Under the
-- recursive `_≤′_`, `α ≤′ β` is definitionally `osuc α ≤′ osuc β`
-- via the `osuc/osuc` clause, so this is literally `≤′-trans` at
-- the lifted indices.
≤′-<′-trans : ∀ {α β γ} → α ≤′ β → β <′ γ → α <′ γ
≤′-<′-trans {α} {β} {γ} p q = ≤′-trans {osuc α} {osuc β} {γ} p q

-- Compose two strict orderings.  α <′ β and β <′ γ chain via
-- `≤′-self-osuc` at β.
<′-trans : ∀ {α β γ} → α <′ β → β <′ γ → α <′ γ
<′-trans {α} {β} {γ} p q =
  ≤′-trans {osuc α} {β} {γ}
    p
    (≤′-trans {β} {osuc β} {γ} (≤′-self-osuc β) q)

----------------------------------------------------------------------
-- `ω-rank-pow` is monotone in the `≤Ω` direction
----------------------------------------------------------------------

-- The non-strict analogue of `ω-rank-pow-mono`.  Case on the `≤Ω`
-- derivation:
--   * `fin≤fin m≤n`: ω^(suc m) ≤′ ω^(suc n) via `ω^-mono-≤` at the
--     shifted index.
--   * `fin≤ω`:       ω^(suc m) ≤′ olim (λ k → ω^(suc k)) via `f-in-lim′`.
--   * `ω≤ω`:         reflexive.

ω-rank-pow-mono-≤Ω : ∀ {μ ν} → μ ≤Ω ν → ω-rank-pow μ ≤′ ω-rank-pow ν
ω-rank-pow-mono-≤Ω (fin≤fin m≤n) = ω^-mono-≤ (s≤s m≤n)
ω-rank-pow-mono-≤Ω {fin m} fin≤ω = f-in-lim′ (λ k → ω^ (suc k)) m
ω-rank-pow-mono-≤Ω ω≤ω           = ≤′-refl

----------------------------------------------------------------------
-- Positivity of `ω-rank-pow-succ`
----------------------------------------------------------------------

-- `oz <′ ω-rank-pow-succ μ` for both branches.  Compose
-- `oz <′ ω-rank-pow μ` (the existing `ω-rank-pow-pos`) with
-- `ω-rank-pow μ <′ ω-rank-pow-succ μ` (`ω-rank-pow-<-succ`) via
-- `<′-trans`.

ω-rank-pow-succ-pos : ∀ μ → oz <′ ω-rank-pow-succ μ
ω-rank-pow-succ-pos μ =
  <′-trans {oz} {ω-rank-pow μ} {ω-rank-pow-succ μ}
    (ω-rank-pow-pos μ)
    (ω-rank-pow-<-succ μ)

----------------------------------------------------------------------
-- Additive-principal closure of `ω-rank-pow-succ`
----------------------------------------------------------------------

-- For each Ω-marker μ, `ω-rank-pow-succ μ` is closed under ordinal
-- addition: for any α, β strictly below, the sum α ⊕ β is also
-- strictly below.
--
-- * Fin branch.  `ω-rank-pow-succ (fin n) = ω^(suc(suc n))` IS one
--   of the additive-principal ω-powers, so this dispatches to
--   `additive-principal {suc n}` from `OmegaPow`.
-- * ω branch.  Mirrors the `OmegaPow.additive-principal` proof
--   (lines 363–401) with `ω^ n` replaced by `ω-rank-pow ω`:
--   pick branch `kβ + kα` in the target; chain `⊕-mono-≤-left`
--   (using `α ≤′ ω-rank-pow ω ·ℕ kα` from weakening sα with
--   `≤′-self-osuc α`), `⊕-mono-<-right` (using `sβ` directly), and
--   `·ℕ-add-≤` (generic over its base, instantiated at
--   `ω-rank-pow ω`).

additive-principal-ω-rank-pow-succ : ∀ {μ α β}
  → α <′ ω-rank-pow-succ μ
  → β <′ ω-rank-pow-succ μ
  → α ⊕ β <′ ω-rank-pow-succ μ
additive-principal-ω-rank-pow-succ {fin n} pα pβ =
  additive-principal {suc n} pα pβ
additive-principal-ω-rank-pow-succ {ω} {α} {β} (kα , sα) (kβ , sβ) =
  kβ + kα , proof
  where
  α≤′kα : α ≤′ ω-rank-pow ω ·ℕ kα
  α≤′kα = ≤′-trans {α} {osuc α} {ω-rank-pow ω ·ℕ kα}
            (≤′-self-osuc α)
            sα

  step1 : α ⊕ β ≤′ (ω-rank-pow ω ·ℕ kα) ⊕ β
  step1 = ⊕-mono-≤-left {α} {ω-rank-pow ω ·ℕ kα} {β} α≤′kα

  step2 : osuc ((ω-rank-pow ω ·ℕ kα) ⊕ β) ≤′ (ω-rank-pow ω ·ℕ kα) ⊕ (ω-rank-pow ω ·ℕ kβ)
  step2 = ⊕-mono-<-right {ω-rank-pow ω ·ℕ kα} {β} {ω-rank-pow ω ·ℕ kβ} sβ

  step3 : (ω-rank-pow ω ·ℕ kα) ⊕ (ω-rank-pow ω ·ℕ kβ) ≤′ ω-rank-pow ω ·ℕ (kβ + kα)
  step3 = ·ℕ-add-≤ {ω-rank-pow ω} kα kβ

  proof : osuc (α ⊕ β) ≤′ ω-rank-pow ω ·ℕ (kβ + kα)
  proof = ≤′-trans
            {osuc (α ⊕ β)}
            {(ω-rank-pow ω ·ℕ kα) ⊕ (ω-rank-pow ω ·ℕ kβ)}
            {ω-rank-pow ω ·ℕ (kβ + kα)}
            (≤′-trans
              {osuc (α ⊕ β)}
              {osuc ((ω-rank-pow ω ·ℕ kα) ⊕ β)}
              {(ω-rank-pow ω ·ℕ kα) ⊕ (ω-rank-pow ω ·ℕ kβ)}
              step1
              step2)
            step3

----------------------------------------------------------------------
-- bplus right-summand bound
----------------------------------------------------------------------

-- Auxiliary lemma for the bplus case of the main lemma.  Given a
-- WfCNF tail bound `y ≤ᵇ x` plus `Atomic y`, the right summand's
-- rank is bounded by `ω-rank-pow-succ (head-Ω x)`.
--
-- Three cases on the Atomic derivation × two cases on the ≤ᵇ
-- direction (= six sub-cases total, several collapsing to the same
-- discharge shape):
--
--   * y = bzero: rank y = oz, dispatch to `ω-rank-pow-succ-pos`.
--   * y = bOmega ν, y <ᵇ x: `head-Ω-inv-bOmega` gives `ν <Ω head-Ω x`;
--     `ω-rank-pow-mono` lifts to `ω-rank-pow ν <′ ω-rank-pow (head-Ω x)`;
--     chain with `ω-rank-pow-<-succ` via `<′-trans`.
--   * y = bOmega ν, y ≡ x: x = bOmega ν, head-Ω x = ν;
--     `ω-rank-pow-<-succ ν` discharges.
--   * y = bpsi ν α, y <ᵇ x: `head-Ω-inv-bpsi` gives `ν ≤Ω head-Ω x`;
--     `ω-rank-pow-mono-≤Ω` lifts; chain with `ω-rank-pow-<-succ`
--     via `≤′-<′-trans`.
--   * y = bpsi ν α, y ≡ x: x = bpsi ν α, head-Ω x = ν;
--     `ω-rank-pow-<-succ ν` discharges.

rank-y-bound : ∀ {x y} → Atomic y → y ≤ᵇ x →
               rank-pow y <′ ω-rank-pow-succ (head-Ω x)
rank-y-bound {x} atomic-bzero _ =
  ω-rank-pow-succ-pos (head-Ω x)

rank-y-bound {x} (atomic-bomega {μ = ν}) (inj₁ y<x) =
  <′-trans {ω-rank-pow ν} {ω-rank-pow (head-Ω x)} {ω-rank-pow-succ (head-Ω x)}
    (ω-rank-pow-mono (head-Ω-inv-bOmega y<x))
    (ω-rank-pow-<-succ (head-Ω x))
rank-y-bound (atomic-bomega {μ = ν}) (inj₂ refl) =
  ω-rank-pow-<-succ ν

rank-y-bound {x} (atomic-bpsi {ν = ν} {α = α}) (inj₁ y<x) =
  ≤′-<′-trans {ω-rank-pow ν} {ω-rank-pow (head-Ω x)} {ω-rank-pow-succ (head-Ω x)}
    (ω-rank-pow-mono-≤Ω (head-Ω-inv-bpsi y<x))
    (ω-rank-pow-<-succ (head-Ω x))
rank-y-bound (atomic-bpsi {ν = ν}) (inj₂ refl) =
  ω-rank-pow-<-succ ν

----------------------------------------------------------------------
-- THE HEADLINE: rank-pow domination by ω-rank-pow-succ ∘ head-Ω
----------------------------------------------------------------------

-- Structural recursion on the WfCNF carrier:
--
--   * `wf-cnf-bzero`: rank = oz, head-Ω = fin 0,
--     target = ω-rank-pow-succ (fin 0) = ω^2.
--     Discharge: `ω-rank-pow-succ-pos (fin 0)`.
--   * `wf-cnf-bomega`: rank = ω-rank-pow ν, head-Ω = ν,
--     target = ω-rank-pow-succ ν.
--     Discharge: `ω-rank-pow-<-succ ν`.
--   * `wf-cnf-bpsi`: same as bOmega via the provisional
--     `rank-pow (bpsi ν _) = ω-rank-pow ν` shape.
--   * `wf-cnf-bplus`: rank = rank x ⊕ rank y, head-Ω = head-Ω x,
--     target = ω-rank-pow-succ (head-Ω x).
--     Discharge: `additive-principal-ω-rank-pow-succ {head-Ω x}`
--     fed by the structural recursion on x (the IH) and the
--     atomic-y bound from `rank-y-bound`.
--
-- Termination is on the WfCNF carrier — every recursive call passes
-- a strictly-smaller sub-derivation.  No funext, no postulates, no
-- rank-mono dependency anywhere in the chain.

rank-pow-dominated-by-head-Ω : ∀ {t} → WfCNF t →
                               rank-pow t <′ ω-rank-pow-succ (head-Ω t)
rank-pow-dominated-by-head-Ω wf-cnf-bzero =
  ω-rank-pow-succ-pos (fin 0)
rank-pow-dominated-by-head-Ω (wf-cnf-bomega {μ = ν} _) =
  ω-rank-pow-<-succ ν
rank-pow-dominated-by-head-Ω (wf-cnf-bpsi {ν = ν} _ _) =
  ω-rank-pow-<-succ ν
rank-pow-dominated-by-head-Ω (wf-cnf-bplus {x = x} wfx _ aty y≤x) =
  additive-principal-ω-rank-pow-succ {head-Ω x}
    (rank-pow-dominated-by-head-Ω wfx)
    (rank-y-bound {x} aty y≤x)
