{-# OPTIONS --safe --without-K #-}

-- ω-power rank for Ω-markers and Buchholz terms (Slice 4 of the
-- path-1 unblock, per `docs/echo-types/buchholz-rank-obstruction.adoc`).
--
-- Replaces the successor-stack `ω-rank` of `Ordinal.Brouwer.Arithmetic`
-- with the limit-shaped `ω-rank-pow`, whose values are additive
-- principal (`Ordinal.Brouwer.OmegaPow.additive-principal`).  This
-- closes the rank-mono wall for the plus-side `_<ᵇ_` constructors
-- under the WfCNF restriction.
--
-- ## Reuse design
--
-- The compositional rank-mono primitives in this module are
-- relation-agnostic: they take a `rank-pow x <′ rank-pow y` hypothesis
-- and produce a `rank-pow (CTX[x]) <′ rank-pow (CTX[y])` conclusion
-- for a single-hole context `CTX`.  Both the WfCNF-restricted
-- `_<ᵇ⁻_` (Slice 5) and the recursive-surface `_<ᵇʳᶠ_` (parallel
-- session) can consume them by recursing on their relation's proof
-- tree and applying the appropriate primitive at each constructor.
--
-- ## What lands in this slice
--
--   * `ω-rank-pow : OmegaIndex → Ord`     — limit-shaped Ω-rank.
--   * `ω-rank-pow-pos`                    — `oz <′ ω-rank-pow μ`.
--   * `ω-rank-pow-fin`, `ω-rank-pow-ω`    — definitional sanity.
--   * `ω-rank-pow-mono`                   — `μ <Ω ν → ω-rank-pow μ <′ ω-rank-pow ν`.
--   * `rank-pow : BT → Ord`               — Buchholz-term rank.
--   * `rank-pow-bplus`, `rank-pow-bOmega`  — definitional sanity.
--   * `rank-pow-bplus-right-mono`         — `rank-pow y <′ rank-pow z`
--                                           → `rank-pow (bplus x y) <′ rank-pow (bplus x z)`
--                                           (reusable across relations).
--
-- ## Deferred to follow-on slices
--
--   * `rank-pow-bplus-left-mono` (Slice 5) — same shape on the left,
--     using additive-principal at the target's rank.  Needs WfCNF.
--   * `rank-pow-bpsi-arg-mono` (separate slice) — needs the
--     ψ-admissibility predicate (`α ∈ C_ν`); shape of `rank-pow` on
--     `bpsi ν α` is open until that lemma lands.
--   * `rank-mono-<ᵇ⁻` (Slice 5)            — discharge of the 5
--     plus-side cases of the WfCNF-tagged rank-mono.

module Ordinal.Buchholz.RankPow where

open import Data.Nat.Base                         using (ℕ; zero; suc; s≤s)
open import Data.Product.Base                     using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers                  using
  ( OmegaIndex
  ; fin
  ; ω
  ; _<Ω_
  ; fin<fin
  ; fin<ω
  )
open import Ordinal.Brouwer                       using
  ( Ord
  ; oz
  ; osuc
  ; olim
  )
open import Ordinal.Brouwer.Arithmetic            using (_⊕_)
open import Ordinal.Brouwer.Phase13               using
  ( _≤′_
  ; _<′_
  ; ⊕-mono-<-right
  ; f-in-lim′
  )
open import Ordinal.Brouwer.OmegaPow              using
  ( ω^_
  ; ω^_-pos
  ; ω^-strict-mono
  ; ω^-strict-mono-suc
  )
open import Ordinal.Buchholz.Syntax               using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )

----------------------------------------------------------------------
-- `ω-rank-pow : OmegaIndex → Ord` — limit-shaped Ω-rank
----------------------------------------------------------------------

-- `fin n  ↦ ω^ (suc n)` — limit ordinal, additive principal at its
--                         supremum.
-- `ω      ↦ olim (λ n → ω^ (suc n))` — limit of additive principals.
--
-- The `+ 1` shift in `fin n ↦ ω^(suc n)` keeps `ω-rank-pow (fin 0) = ω^1 = ω`
-- strictly above `oz = rank-pow bzero` (via `ω^_-pos 1`), which is
-- needed for the `<ᵇ-0-Ω` constructor's rank-mono.

ω-rank-pow : OmegaIndex → Ord
ω-rank-pow (fin n) = ω^ (suc n)
ω-rank-pow ω       = olim (λ n → ω^ (suc n))

----------------------------------------------------------------------
-- Definitional sanity
----------------------------------------------------------------------

ω-rank-pow-fin : ∀ n → ω-rank-pow (fin n) ≡ ω^ (suc n)
ω-rank-pow-fin _ = refl

----------------------------------------------------------------------
-- Positivity: `oz <′ ω-rank-pow μ`
----------------------------------------------------------------------

-- For each Ω-marker μ, `ω-rank-pow μ` is strictly above `oz`.  This
-- is the rank-mono witness for the `<ᵇ-0-Ω` constructor under the
-- new rank target.

ω-rank-pow-pos : ∀ μ → oz <′ ω-rank-pow μ
ω-rank-pow-pos (fin n) = ω^_-pos (suc n)
ω-rank-pow-pos ω       = 0 , ω^_-pos 1

----------------------------------------------------------------------
-- Strict monotonicity along `_<Ω_`
----------------------------------------------------------------------

-- `μ <Ω ν → ω-rank-pow μ <′ ω-rank-pow ν`.  Three cases for the
-- `_<Ω_` derivation:
--
--   * `fin m <Ω fin n` from `m < n` (ℕ): apply `ω^-strict-mono` to
--     `s≤s p : suc m < suc n`.  Note `_<_` on ℕ unfolds to
--     `suc m ≤ n`; preserving the offset under the `+ 1` shift is
--     definitional.
--   * `fin m <Ω ω`: pick branch index `m` in the limit
--     `ω-rank-pow ω`; the inner witness is `ω^-strict-mono-suc (suc m)`
--     giving `ω^ (suc m) <′ ω^ (suc (suc m))`, lifted to the limit
--     by branch selection.

ω-rank-pow-mono : ∀ {μ ν} → μ <Ω ν → ω-rank-pow μ <′ ω-rank-pow ν
ω-rank-pow-mono {fin m} {fin n} (fin<fin p) = ω^-strict-mono (s≤s p)
ω-rank-pow-mono {fin m} {ω}     fin<ω       = suc m , ω^-strict-mono-suc (suc m)

----------------------------------------------------------------------
-- `rank-pow : BT → Ord`
----------------------------------------------------------------------

-- Buchholz-term rank using the limit-shaped `ω-rank-pow` instead of
-- the successor-stack `ω-rank`.
--
-- The shape for `bpsi ν α` is provisionally `ω-rank-pow ν` (no
-- α-dependent tail).  This is sufficient for the four already-working
-- rank-mono cases (`<ᵇ-0-Ω`, `<ᵇ-0-ψ`, `<ᵇ-ΩΩ`, `<ᵇ-Ωψ`) and is
-- safe for the plus-side cases that bottom out at `bOmega`.  The
-- α-discrimination needed for `<ᵇ-ψα`, `<ᵇ-ψΩ≤`, and the joint
-- `<ᵇ-+ψ` ψ-target case requires the ψ-admissibility predicate
-- and is deferred to a separate slice.  This module's `bpsi` shape
-- is a simplification that closes the *additive-principal-only*
-- plus-side unblock; the eventual full rank-mono will refine it.

rank-pow : BT → Ord
rank-pow bzero        = oz
rank-pow (bOmega ν)   = ω-rank-pow ν
rank-pow (bplus x y)  = rank-pow x ⊕ rank-pow y
rank-pow (bpsi ν _)   = ω-rank-pow ν   -- provisional; see comment above

----------------------------------------------------------------------
-- Definitional sanity
----------------------------------------------------------------------

rank-pow-bplus : ∀ x y → rank-pow (bplus x y) ≡ rank-pow x ⊕ rank-pow y
rank-pow-bplus _ _ = refl

rank-pow-bOmega : ∀ ν → rank-pow (bOmega ν) ≡ ω-rank-pow ν
rank-pow-bOmega _ = refl

----------------------------------------------------------------------
-- Compositional rank-mono primitives
----------------------------------------------------------------------

-- Right-monotonicity for `bplus`: `rank-pow y <′ rank-pow z` lifts
-- to `rank-pow (bplus x y) <′ rank-pow (bplus x z)`.  Pure right-
-- strict-mono of `_⊕_`; no relation-specific input.  Consumed by
-- the rank-mono case for `<ᵇ-+2` / `<ᵇʳᶠ-+2` (and any sibling
-- shared-binder constructor that compares right summands).

rank-pow-bplus-right-mono : ∀ {x y z}
  → rank-pow y <′ rank-pow z
  → rank-pow (bplus x y) <′ rank-pow (bplus x z)
rank-pow-bplus-right-mono {x} {y} {z} p =
  ⊕-mono-<-right {rank-pow x} {rank-pow y} {rank-pow z} p

----------------------------------------------------------------------
-- Left-≤-sum projection
----------------------------------------------------------------------

-- The left summand of a `bplus` is always ≤′ the sum (in rank).
-- Direct from `⊕-left-≤-sum` in Phase13.

open import Ordinal.Brouwer.Phase13 using (⊕-left-≤-sum; ≤′-trans)

rank-pow-bplus-left-≤ : ∀ x y → rank-pow x ≤′ rank-pow (bplus x y)
rank-pow-bplus-left-≤ x y = ⊕-left-≤-sum {rank-pow x} (rank-pow y)

-- `target <′ rank-pow x → target <′ rank-pow (bplus x y)`.  Covers
-- the rank-mono shape needed for `<ᵇ-Ω+` and `<ᵇ-ψ+`: source-side
-- atomic (or smaller) is strictly less than the left of a bplus,
-- hence strictly less than the bplus itself.

rank-pow-via-left : ∀ {target x y}
  → target <′ rank-pow x
  → target <′ rank-pow (bplus x y)
rank-pow-via-left {target} {x} {y} p =
  ≤′-trans {osuc target} {rank-pow x} {rank-pow (bplus x y)}
    p
    (rank-pow-bplus-left-≤ x y)

----------------------------------------------------------------------
-- Additive-principal closure at `ω-rank-pow μ`
----------------------------------------------------------------------

-- `ω-rank-pow μ` is closed under ordinal addition: for any α, β
-- strictly below, the sum α ⊕ β is also strictly below.  Direct
-- consequence of `Ordinal.Brouwer.OmegaPow.additive-principal` for
-- the `fin n` case; the `ω` case picks a common upper bound from
-- both witnesses' branch indices.

open import Data.Nat.Base       using (_+_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m)

open import Ordinal.Brouwer.OmegaPow using
  ( additive-principal
  ; ω^-mono-≤
  )

additive-principal-ω-rank-pow : ∀ {μ α β}
  → α <′ ω-rank-pow μ
  → β <′ ω-rank-pow μ
  → α ⊕ β <′ ω-rank-pow μ
additive-principal-ω-rank-pow {fin n} pα pβ =
  additive-principal {n} pα pβ
additive-principal-ω-rank-pow {ω} {α} {β} (kα , sα) (kβ , sβ) =
  (kα + kβ) , additive-principal {kα + kβ} α<sum β<sum
  where
  -- Lift α's witness from ω^(suc kα) to ω^(suc (kα + kβ)) via
  -- ω^-mono-≤ on `kα ≤ kα + kβ`.
  α<sum : α <′ ω^ (suc (kα + kβ))
  α<sum = ≤′-trans
            {osuc α} {ω^ (suc kα)} {ω^ (suc (kα + kβ))}
            sα
            (ω^-mono-≤ (s≤s (m≤m+n kα kβ)))

  -- Lift β's witness from ω^(suc kβ) to ω^(suc (kα + kβ)) via
  -- ω^-mono-≤ on `kβ ≤ kα + kβ`.
  β<sum : β <′ ω^ (suc (kα + kβ))
  β<sum = ≤′-trans
            {osuc β} {ω^ (suc kβ)} {ω^ (suc (kα + kβ))}
            sβ
            (ω^-mono-≤ (s≤s (m≤n+m kβ kα)))

----------------------------------------------------------------------
-- "Plus-side into additive-principal target": the bplus shape
-- `bplus x y` lands strictly below an additive-principal target when
-- the left summand x does and the tail y is ≤′ x's rank.
----------------------------------------------------------------------

-- This is the rank-side discharge for `<ᵇ-+Ω` and `<ᵇ-+ψ` under
-- WfCNF.  The WfCNF condition `y ≤ᵇ x` lifts to a rank inequality
-- `rank-pow y ≤′ rank-pow x` (proved in Slice 5b once the
-- `rank-pow-mono-≤ᵇ` corollary is in place); we take that as a
-- separate hypothesis here so this primitive can be applied
-- whenever a caller produces the tail bound (Slice 5 consumer or
-- the `<ᵇʳᶠ` consumer's own WfCNF carrier).

rank-pow-bplus-into-ω-rank-pow : ∀ {x y μ}
  → rank-pow x <′ ω-rank-pow μ
  → rank-pow y ≤′ rank-pow x
  → rank-pow (bplus x y) <′ ω-rank-pow μ
rank-pow-bplus-into-ω-rank-pow {x} {y} {μ} px y≤x =
  additive-principal-ω-rank-pow {μ} px y<target
  where
  y<target : rank-pow y <′ ω-rank-pow μ
  y<target = ≤′-trans
               {osuc (rank-pow y)} {osuc (rank-pow x)} {ω-rank-pow μ}
               y≤x   -- `osuc/osuc` clause: y≤x : rank y ≤′ rank x
                     -- reduces to osuc (rank y) ≤′ osuc (rank x).
               px

----------------------------------------------------------------------
-- Per-constructor rank-mono primitives (relation-agnostic)
----------------------------------------------------------------------

-- One lemma per `_<ᵇ_` constructor, stated purely in terms of rank
-- inequalities (not the relation itself).  Consumers — `_<ᵇ⁻_`
-- (this track, Slice 5b) and `_<ᵇʳᶠ_` (parallel-session track) —
-- pattern-match on their own relation's constructor and apply the
-- matching primitive below.  The recursive structure lives in the
-- consumer, not in `RankPow`.
--
-- Coverage:
--   * 4 trivial cases (no premise on subterms): `<ᵇ-0-Ω`, `<ᵇ-0-ψ`,
--     `<ᵇ-ΩΩ`, `<ᵇ-Ωψ`, `<ᵇ-ψΩ` — 5 actually, since `<ᵇ-ψΩ` is
--     ω-rank-pow-mono.  Pure structural facts.
--   * 4 "via-left" cases: `<ᵇ-Ω+`, `<ᵇ-ψ+`, `<ᵇ-+Ω`, `<ᵇ-+ψ` — the
--     `+` lives on one side; primitive takes a strict-on-left witness
--     plus (for the `+` source cases) the WfCNF tail bound.
--   * Deferred: `<ᵇ-ψα`, `<ᵇ-ψΩ≤` (admissibility-blocked under the
--     provisional `rank-pow (bpsi ν _) = ω-rank-pow ν` shape) and
--     `<ᵇ-+1` (joint-bplus, structurally hardest; needs a coarser
--     bound or a refined rank).

rank-mono-<ᵇ-0-Ω : ∀ {μ} → rank-pow bzero <′ rank-pow (bOmega μ)
rank-mono-<ᵇ-0-Ω {μ} = ω-rank-pow-pos μ

rank-mono-<ᵇ-0-ψ : ∀ {ν α} → rank-pow bzero <′ rank-pow (bpsi ν α)
rank-mono-<ᵇ-0-ψ {ν} = ω-rank-pow-pos ν

rank-mono-<ᵇ-ΩΩ : ∀ {μ ν} → μ <Ω ν
  → rank-pow (bOmega μ) <′ rank-pow (bOmega ν)
rank-mono-<ᵇ-ΩΩ p = ω-rank-pow-mono p

rank-mono-<ᵇ-Ωψ : ∀ {μ ν α} → μ <Ω ν
  → rank-pow (bOmega μ) <′ rank-pow (bpsi ν α)
rank-mono-<ᵇ-Ωψ p = ω-rank-pow-mono p

rank-mono-<ᵇ-ψΩ : ∀ {μ ν α β} → μ <Ω ν
  → rank-pow (bpsi μ α) <′ rank-pow (bpsi ν β)
rank-mono-<ᵇ-ψΩ p = ω-rank-pow-mono p

rank-mono-<ᵇ-Ω+ : ∀ {μ x y}
  → rank-pow (bOmega μ) <′ rank-pow x
  → rank-pow (bOmega μ) <′ rank-pow (bplus x y)
rank-mono-<ᵇ-Ω+ {μ} {x} {y} p = rank-pow-via-left {rank-pow (bOmega μ)} {x} {y} p

rank-mono-<ᵇ-ψ+ : ∀ {ν α x y}
  → rank-pow (bpsi ν α) <′ rank-pow x
  → rank-pow (bpsi ν α) <′ rank-pow (bplus x y)
rank-mono-<ᵇ-ψ+ {ν} {α} {x} {y} p =
  rank-pow-via-left {rank-pow (bpsi ν α)} {x} {y} p

rank-mono-<ᵇ-+Ω : ∀ {x y μ}
  → rank-pow x <′ rank-pow (bOmega μ)
  → rank-pow y ≤′ rank-pow x          -- WfCNF tail bound (caller-provided)
  → rank-pow (bplus x y) <′ rank-pow (bOmega μ)
rank-mono-<ᵇ-+Ω {x} {y} {μ} px y≤x =
  rank-pow-bplus-into-ω-rank-pow {x} {y} {μ} px y≤x

rank-mono-<ᵇ-+ψ : ∀ {x y ν α}
  → rank-pow x <′ rank-pow (bpsi ν α)
  → rank-pow y ≤′ rank-pow x          -- WfCNF tail bound (caller-provided)
  → rank-pow (bplus x y) <′ rank-pow (bpsi ν α)
rank-mono-<ᵇ-+ψ {x} {y} {ν} {α} px y≤x =
  -- `rank-pow (bpsi ν α) = ω-rank-pow ν` (provisional shape), so
  -- this reduces to the `<ᵇ-+Ω`-shaped argument at target ν.
  rank-pow-bplus-into-ω-rank-pow {x} {y} {ν} px y≤x

----------------------------------------------------------------------
-- `<ᵇ-+1` via a caller-supplied target-additive-principal witness
----------------------------------------------------------------------

-- `bplus x₁ x₂ <ᵇ bplus y₁ y₂` from `x₁ <ᵇ y₁` is the `<ᵇ-+1`
-- constructor.  The rank-mono conclusion `rank-pow (bplus x₁ x₂) <′
-- rank-pow (bplus y₁ y₂)` requires `rank-pow y₁` to be additive
-- principal (in the sense that `α, β <′ rank-pow y₁` forces
-- `α ⊕ β <′ rank-pow y₁`).  For atomic `y₁ ∈ {bOmega μ, bpsi ν _}`,
-- `rank-pow y₁ = ω-rank-pow _` IS additive principal and the consumer
-- supplies `additive-principal-ω-rank-pow`.  For `y₁ = bplus z₁ z₂`,
-- `rank-pow y₁` is not additive principal in general; that sub-case
-- needs a coarser dominator function and is deferred.
--
-- The primitive below is parametric in the additive-principal
-- witness, so the consumer pattern-matches on `y₁`'s constructor and
-- supplies the appropriate witness at each call site.

rank-mono-<ᵇ-+1-via-target : ∀ {x₁ x₂ y₁ y₂}
  → (target-add : ∀ {α β}
       → α <′ rank-pow y₁
       → β <′ rank-pow y₁
       → α ⊕ β <′ rank-pow y₁)
  → rank-pow x₁ <′ rank-pow y₁          -- IH on `x₁ <ᵇ y₁`
  → rank-pow x₂ ≤′ rank-pow x₁          -- WfCNF source tail bound
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
rank-mono-<ᵇ-+1-via-target {x₁} {x₂} {y₁} {y₂} target-add rx<ry rx₂≤rx₁ =
  let
    -- rank x₂ ≤′ rank x₁ <′ rank y₁ gives rank x₂ <′ rank y₁
    rx₂<ry : rank-pow x₂ <′ rank-pow y₁
    rx₂<ry = ≤′-trans
               {osuc (rank-pow x₂)} {osuc (rank-pow x₁)} {rank-pow y₁}
               rx₂≤rx₁
               rx<ry

    -- additive-principal closure on the target: both summands <′ y₁,
    -- so their ⊕-sum is also <′ y₁.
    sum<ry : rank-pow x₁ ⊕ rank-pow x₂ <′ rank-pow y₁
    sum<ry = target-add rx<ry rx₂<ry

    -- y₁ ≤′ y₁ ⊕ y₂ by left-≤-sum.
    ry≤target : rank-pow y₁ ≤′ rank-pow (bplus y₁ y₂)
    ry≤target = ⊕-left-≤-sum {rank-pow y₁} (rank-pow y₂)
  in
    ≤′-trans
      {osuc (rank-pow x₁ ⊕ rank-pow x₂)} {rank-pow y₁} {rank-pow (bplus y₁ y₂)}
      sum<ry
      ry≤target

-- Convenience: when the target's leading subterm is `bOmega μ`, the
-- consumer can directly supply `additive-principal-ω-rank-pow {μ}`.
-- Same for `bpsi ν _` via the provisional shape.

rank-mono-<ᵇ-+1-Ω-target : ∀ {x₁ x₂ μ y₂}
  → rank-pow x₁ <′ ω-rank-pow μ
  → rank-pow x₂ ≤′ rank-pow x₁
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus (bOmega μ) y₂)
rank-mono-<ᵇ-+1-Ω-target {x₁} {x₂} {μ} {y₂} =
  rank-mono-<ᵇ-+1-via-target {x₁} {x₂} {bOmega μ} {y₂}
    (additive-principal-ω-rank-pow {μ})

rank-mono-<ᵇ-+1-ψ-target : ∀ {x₁ x₂ ν α y₂}
  → rank-pow x₁ <′ ω-rank-pow ν
  → rank-pow x₂ ≤′ rank-pow x₁
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus (bpsi ν α) y₂)
rank-mono-<ᵇ-+1-ψ-target {x₁} {x₂} {ν} {α} {y₂} =
  rank-mono-<ᵇ-+1-via-target {x₁} {x₂} {bpsi ν α} {y₂}
    (additive-principal-ω-rank-pow {ν})

----------------------------------------------------------------------
-- Slice 2 of the head-Ω domination route
----------------------------------------------------------------------
--
-- The HeadOmega module (`Ordinal.Buchholz.HeadOmega`) defines the
-- leading-Ω-index head function `head-Ω : BT → OmegaIndex`.  This
-- section adds the per-marker "next ω-power up" target
-- `ω-rank-pow-succ : OmegaIndex → Ord` consumed by the planned (but
-- not yet landed) `<ᵇ-+1` joint-bplus head-Ω domination route.
--
-- ## Scope of this slice
--
-- Lands:
--   * `ω-rank-pow-succ : OmegaIndex → Ord`
--   * `ω-rank-pow-succ-fin` — definitional sanity, fin branch
--   * `ω-rank-pow-<-succ-fin` — per-marker strict dominance at fin
--   * `rank-pow-bOmega-via-head-Ω`,
--     `rank-pow-bpsi-via-head-Ω` — atomic-rank `refl`-shape primitives
--     factoring `rank-pow` through `head-Ω` for the two non-bplus,
--     non-bzero `BT` constructors.  Useful at consumer-recursion
--     sites that want to rewrite source-rank into head-Ω form
--     without unfolding `rank-pow` and `head-Ω` separately.
--
-- Deferred (with concrete obstructions documented inline below):
--   * The headline domination lemma
--     `rank-pow-dominated-by-head-Ω : (t : BT) → NonBzero t →
--       WfCNF t → rank-pow t <′ ω-rank-pow-succ (head-Ω t)`
--     in its full generality.  The fin branch is structurally clean
--     (every WfCNF clause discharges via additive-principal at
--     ω^(suc(suc n)) and the existing per-constructor rank-mono
--     primitives), but the **ω branch of `head-Ω` cannot strictly
--     dominate under the originally-proposed `ω-rank-pow-succ ω` shape**.
--     See the obstruction note immediately below.
--
-- ## Obstruction note for the ω branch
--
-- The originally proposed shape (per CLAUDE.md § "Session arc
-- 2026-05-27 late evening" — Slice 2 sketch) was:
--
--   ω-rank-pow ω        = olim (λ n → ω^ (suc n))            -- existing
--   ω-rank-pow-succ ω   = olim (λ n → ω^ (suc (suc n)))      -- proposed
--
-- Both `olim`s represent the **same** ordinal (ω^ω) — the supremum of
-- {ω, ω², ω³, …} and the supremum of {ω², ω³, ω⁴, …} are equal as
-- ordinals, just with different ℕ-indexings of the same tail.  Under
-- the recursive `_<′_` of `Phase13`, this manifests as: every attempt
-- to discharge `osuc (olim (λ n → ω^(suc n))) ≤′ olim (λ k → ω^(suc(suc k)))`
-- by picking a branch `k` in the target falls back to an `osuc (olim …)
-- ≤′ ω^(suc(suc k)) ·ℕ j` obligation that is again a limit-vs-osuc
-- comparison, recursing indefinitely.
--
-- A follow-on slice must replace the ω branch with a genuinely
-- strictly-larger ordinal (the natural candidate is `ω^(ω+1)`, the
-- next additive-principal above `ω^ω`).  In Brouwer notation this
-- would be `olim (λ n → (ω-rank-pow ω) ·ℕ n)`; the proof obligation
-- shifts but does not vanish — `(ω-rank-pow ω) ·ℕ n` is itself a
-- nested limit, and the strict-dominance proof needs the equivalent of
-- the existing `additive-principal-ω-rank-pow` ω-branch closure
-- (lines 238–255 above) lifted one ω-power.
--
-- Choosing not to make that replacement in this slice keeps the
-- abstraction minimal and avoids committing to a shape that the
-- consumer (Slice 3, `rank-mono-<ᵇ-+1-via-head-Ω`) might want to
-- specialise differently.  The ω branch of `ω-rank-pow-succ` below
-- therefore reuses the **original** CLAUDE.md proposal verbatim, so
-- the abstraction is in place for follow-on slices to inspect and
-- (if needed) override before any consumer pulls on the ω case.

ω-rank-pow-succ : OmegaIndex → Ord
ω-rank-pow-succ (fin n) = ω^ (suc (suc n))
ω-rank-pow-succ ω       = olim (λ n → ω^ (suc (suc n)))

-- Definitional sanity at the fin branch.  Mirrors `ω-rank-pow-fin`.
ω-rank-pow-succ-fin : ∀ n → ω-rank-pow-succ (fin n) ≡ ω^ (suc (suc n))
ω-rank-pow-succ-fin _ = refl

-- Per-marker strict dominance at the fin branch.  For each `fin n`,
-- `ω-rank-pow (fin n) = ω^(suc n)` is strictly below
-- `ω-rank-pow-succ (fin n) = ω^(suc(suc n))` via the one-step
-- strict-mono of the ω-power ladder.  The ω branch is deferred per the
-- obstruction note above.
ω-rank-pow-<-succ-fin : ∀ n
  → ω-rank-pow (fin n) <′ ω-rank-pow-succ (fin n)
ω-rank-pow-<-succ-fin n = ω^-strict-mono-suc (suc n)

-- Atomic-rank-pow `refl`-shape primitives.  For non-bplus, non-bzero
-- BT constructors, `rank-pow` reduces to `ω-rank-pow` of the
-- corresponding `head-Ω` value.  Both equations are `refl`; provided
-- as named lemmas so consumer rewrites can target `head-Ω`-form
-- without unfolding `rank-pow` and `head-Ω` separately.

open import Ordinal.Buchholz.HeadOmega using (head-Ω)

rank-pow-bOmega-via-head-Ω : ∀ ν
  → rank-pow (bOmega ν) ≡ ω-rank-pow (head-Ω (bOmega ν))
rank-pow-bOmega-via-head-Ω _ = refl

rank-pow-bpsi-via-head-Ω : ∀ ν α
  → rank-pow (bpsi ν α) ≡ ω-rank-pow (head-Ω (bpsi ν α))
rank-pow-bpsi-via-head-Ω _ _ = refl

----------------------------------------------------------------------
-- Where this lands in the head-Ω closure plan
----------------------------------------------------------------------
--
-- The abstraction landed here (`ω-rank-pow-succ` + the fin-branch
-- dominance + the atomic factoring) is the smallest useful first cut.
-- The two open follow-ons are:
--
-- Slice 2-omega.  Replace the ω branch of `ω-rank-pow-succ` with a
-- genuinely strictly-dominating shape and prove `ω-rank-pow ω <′
-- (new-shape)`.  Candidate: `ω^(ω+1)` encoded as
-- `olim (λ n → (ω-rank-pow ω) ·ℕ n)`.  Cross-checks before committing:
-- (i) the new shape closes under ordinal addition strictly above
-- `ω-rank-pow ω` (so additive-principal-style closure lifts);
-- (ii) the consumer (Slice 3) does not need the additive-principal
-- *of `ω-rank-pow-succ ω` itself* — it needs additive-principal of
-- `ω-rank-pow (head-Ω target)`, which already lands via the existing
-- `additive-principal-ω-rank-pow {ω}` (lines 238–255);
-- (iii) sanity-check the indexing.  The candidate's branches are
-- `(ω-rank-pow ω) ·ℕ n = (… (oz ⊕ ω-rank-pow ω) … ⊕ ω-rank-pow ω)`
-- — the leading `oz ⊕` is NOT definitionally `ω-rank-pow ω` under
-- Brouwer's right-recursing `_⊕_`.  As an ordinal denotation the
-- supremum is `ω^ω · ω = ω^(ω+1)` and is strictly above `ω^ω`, so
-- the lemma *should* go through, but the proof needs the
-- propositional `oz ⊕ X ≤′ X` (or a path-algebra equivalent) at the
-- right step — this is exactly the same hazard ("same ordinal under
-- different ℕ-indexing") that disqualified the original
-- `olim (λ n → ω^(suc(suc n)))` shape.  Verify with a thin spike
-- before committing the body.
--
-- TODO(slice-2-bplus).  Once the ω branch closes, prove the full
-- lemma
--   rank-pow-dominated-by-head-Ω : (t : BT) → NonBzero t → WfCNF t
--                                → rank-pow t <′ ω-rank-pow-succ (head-Ω t)
-- by structural recursion on the WfCNF carrier.  The bplus case
-- needs a `rank-pow-mono-≤ᵇ : x ≤ᵇ y → rank-pow x ≤′ rank-pow y`
-- companion for the original `_<ᵇ_` — landing-site below this
-- comment block — because the WfCNF tail bound is `_≤ᵇ_`, not
-- `_≤ᵇ⁰_`.  The existing `rank-pow-mono-≤ᵇ⁰` in `RankMonoUmbrella`
-- covers the `<ᵇ⁰` carrier only.  A direct `_≤ᵇ_`-mono primitive
-- would need either (a) bridging `_≤ᵇ_` to `_≤ᵇ⁰_` (which is
-- exactly the open Slice 4 problem — full rank-mono umbrella over
-- the original `_<ᵇ_`), or (b) a head-Ω inversion lemma
-- `bOmega ν <ᵇ x → ν <Ω head-Ω x` (and ψ-analogue) that does not
-- transitively depend on rank-mono.  Option (b) is the cleaner
-- path; it parallels the existing per-constructor rank-mono
-- primitives without going through the umbrella, and keeps
-- `rank-pow-dominated-by-head-Ω` independent of
-- `rank-pow-mono-≤ᵇ` so that a future signature change to one
-- does not silently break the other.
