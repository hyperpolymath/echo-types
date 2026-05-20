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
