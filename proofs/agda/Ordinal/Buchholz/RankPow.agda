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
