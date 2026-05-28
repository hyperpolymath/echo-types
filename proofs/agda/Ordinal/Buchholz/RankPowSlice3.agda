{-# OPTIONS --safe --without-K #-}

-- Slice 3 prerequisites for the `<ᵇ-+1` joint-bplus headline
-- `rank-mono-<ᵇ-+1-via-head-Ω`.  Three primitives land here:
--
--   * `NonBzero` — left-spine non-bzero predicate (rules out the
--     degenerate `bplus bzero bzero` chains that WfCNF technically
--     allows but CNF normalisation excludes).
--   * `ω-rank-pow-succ-≤-via-<Ω` — strict-jump bridge from
--     `μ <Ω ν` to `ω-rank-pow-succ μ ≤′ ω-rank-pow ν`.  Closes the
--     gap between Slice 2-bplus's upper bound on the source's rank
--     (`rank-pow t <′ ω-rank-pow-succ (head-Ω t)`) and the lower
--     bound on the target's rank.
--   * `head-Ω-lower-bound` — head-Ω LOWER bound under WfCNF +
--     NonBzero.  Dual of `rank-pow-dominated-by-head-Ω` (which is
--     the corresponding upper).
--
-- ## What this does NOT close
--
-- The Slice 3 HEADLINE `rank-mono-<ᵇ-+1-via-head-Ω` itself requires
-- a STRICT-jump on `head-Ω x₁ <Ω head-Ω y₁` from `x₁ <ᵇ y₁`.  The
-- existing `head-Ω-inv-bpsi` only gives `≤Ω` (via the `<ᵇ-ψΩ≤`
-- constructor — bpsi can be `<ᵇ` an Ω at equal marker), so the
-- ψ-source bpsi sub-case `bpsi ν α <ᵇ y₁` at `ν = head-Ω y₁` does
-- NOT close under the head-Ω route alone.  The strict jump there
-- must come from `α`'s rank (rank-adm refinement on the second
-- component, or a rank-lex combination).  Documented at the bottom
-- of this file as the open follow-on.
--
-- ## Headlines (pin in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `NonBzero` (data type)
--   * `nz-bOmega`, `nz-bpsi`, `nz-bplus` (constructors)
--   * `ω-rank-pow-succ-≤-via-<Ω`
--   * `head-Ω-lower-bound`

module Ordinal.Buchholz.RankPowSlice3 where

open import Data.Nat.Base using (suc; s≤s)

open import Ordinal.Brouwer.Arithmetic using (_⊕_)
open import Ordinal.Brouwer.Phase13 using
  ( _≤′_
  ; ≤′-refl
  ; ≤′-trans
  ; f-in-lim′
  ; ⊕-left-≤-sum
  )
open import Ordinal.Brouwer.OmegaPow using
  ( ω^_
  ; ω^-mono-≤
  )
open import Ordinal.OmegaMarkers using
  ( fin
  ; ω
  ; _<Ω_
  ; fin<fin
  ; fin<ω
  )
open import Ordinal.Buchholz.Syntax using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.WellFormedCNF using
  ( WfCNF
  ; wf-cnf-bomega
  ; wf-cnf-bpsi
  ; wf-cnf-bplus
  )
open import Ordinal.Buchholz.HeadOmega using (head-Ω)
open import Ordinal.Buchholz.RankPow using
  ( rank-pow
  ; ω-rank-pow
  ; ω-rank-pow-succ
  )

----------------------------------------------------------------------
-- NonBzero: left-spine non-bzero predicate
----------------------------------------------------------------------

-- WfCNF allows the degenerate `bplus bzero bzero` (the right
-- summand bzero is ≤ᵇ the left bzero via `<ᵇ`-reflexivity on the
-- bzero atomic), so the head-Ω lower bound needs an extra
-- discriminator to exclude that case.  `NonBzero` walks the
-- leftmost spine and demands at least one non-bzero atomic head
-- — which is exactly what makes `head-Ω t` informative (else
-- `head-Ω t = head-Ω bzero = fin 0` is a default whose rank
-- `ω-rank-pow (fin 0) = ω^1 = ω` is NOT below `rank-pow t = oz`).
--
-- `NonBzero` is monotone in the leftmost-spine constructor:
-- `bplus x y` is NonBzero iff `x` is.  This matches `head-Ω`'s
-- own leftmost-spine recursion.

data NonBzero : BT → Set where
  nz-bOmega : ∀ {μ}   → NonBzero (bOmega μ)
  nz-bpsi   : ∀ {ν α} → NonBzero (bpsi ν α)
  nz-bplus  : ∀ {x y} → NonBzero x → NonBzero (bplus x y)

----------------------------------------------------------------------
-- Strict-jump bridge
----------------------------------------------------------------------

-- The "next ω-power up" target `ω-rank-pow-succ μ` is below the
-- NEXT marker's `ω-rank-pow ν` whenever `μ <Ω ν`.  Two cases on
-- the `<Ω` derivation:
--
--   * `fin m <Ω fin n` from `m < n` (= `suc m ≤ n`):
--     `ω-rank-pow-succ (fin m) = ω^(suc(suc m))`,
--     `ω-rank-pow (fin n) = ω^(suc n)`.  `s≤s p : suc(suc m) ≤
--     suc n`, `ω^-mono-≤ (s≤s p)` discharges.
--   * `fin m <Ω ω`:
--     `ω-rank-pow-succ (fin m) = ω^(suc(suc m))`,
--     `ω-rank-pow ω = olim (λ k → ω^(suc k))`.  Pick branch
--     `suc m` in the limit: `f-in-lim′ (λ k → ω^(suc k)) (suc m)`
--     gives `ω^(suc(suc m)) ≤′ olim ...`.
--   * `ω <Ω _`: impossible (ω is top of `OmegaIndex`; no `_<Ω_`
--     constructor takes ω on the left).

ω-rank-pow-succ-≤-via-<Ω : ∀ {μ ν} → μ <Ω ν → ω-rank-pow-succ μ ≤′ ω-rank-pow ν
ω-rank-pow-succ-≤-via-<Ω {fin m} {fin n} (fin<fin p) = ω^-mono-≤ (s≤s p)
ω-rank-pow-succ-≤-via-<Ω {fin m} {ω}     fin<ω       =
  f-in-lim′ (λ k → ω^ (suc k)) (suc m)

----------------------------------------------------------------------
-- head-Ω LOWER bound under WfCNF + NonBzero
----------------------------------------------------------------------

-- For any WfCNF + NonBzero term `t`, the leading marker's
-- `ω-rank-pow` is BELOW the full `rank-pow t`.  Dual of
-- `rank-pow-dominated-by-head-Ω : rank-pow t <′ ω-rank-pow-succ
-- (head-Ω t)` (the same form with `succ` and `<′` for the upper).
--
-- Structural recursion on the WfCNF derivation, with NonBzero
-- supplying the leftmost-spine non-degeneracy:
--
--   * `bOmega ν`: head-Ω = ν, rank-pow = ω-rank-pow ν.  `≤′-refl`.
--   * `bpsi ν α`: head-Ω = ν, rank-pow = ω-rank-pow ν (provisional
--     shape from `RankPow.agda`).  `≤′-refl`.
--   * `bplus x y`: head-Ω = head-Ω x, rank-pow = rank-pow x ⊕
--     rank-pow y.  IH on x (with `NonBzero x` extracted from
--     `nz-bplus nzx`) gives `ω-rank-pow (head-Ω x) ≤′ rank-pow x`;
--     chain through `⊕-left-≤-sum (rank-pow y) : rank-pow x ≤′
--     rank-pow x ⊕ rank-pow y` via `≤′-trans`.
--
-- Termination: structural recursion on the `WfCNF` carrier (each
-- recursive call passes `wfx`, a strictly-smaller sub-derivation).
-- No funext, no postulates, no rank-mono dependency.

head-Ω-lower-bound : ∀ {t} → WfCNF t → NonBzero t →
                     ω-rank-pow (head-Ω t) ≤′ rank-pow t
head-Ω-lower-bound {bOmega μ}        (wf-cnf-bomega _)             nz-bOmega      =
  ≤′-refl {ω-rank-pow μ}
head-Ω-lower-bound {bpsi ν α}        (wf-cnf-bpsi _ _)             nz-bpsi        =
  ≤′-refl {ω-rank-pow ν}
head-Ω-lower-bound {bplus x y}       (wf-cnf-bplus wfx _ _ _)      (nz-bplus nzx) =
  ≤′-trans {ω-rank-pow (head-Ω x)} {rank-pow x} {rank-pow x ⊕ rank-pow y}
    (head-Ω-lower-bound wfx nzx)
    (⊕-left-≤-sum {rank-pow x} (rank-pow y))

----------------------------------------------------------------------
-- Slice 3 design note (informal)
----------------------------------------------------------------------

-- The intended Slice 3 headline:
--
--   rank-mono-<ᵇ-+1-via-head-Ω : ∀ {x₁ x₂ y₁ y₂}
--     → WfCNF (bplus x₁ x₂) → NonBzero x₁
--     → WfCNF (bplus y₁ y₂) → NonBzero y₁
--     → x₁ <ᵇ y₁
--     → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
--
-- Strategy (chain):
--
--   rank-pow (bplus x₁ x₂)
--     <′ ω-rank-pow-succ (head-Ω x₁)    -- by rank-pow-dominated-by-head-Ω
--                                       --    + head-Ω-bplus
--     ≤′ ω-rank-pow (head-Ω y₁)         -- by ω-rank-pow-succ-≤-via-<Ω
--                                       --    + STRICT-JUMP head-Ω x₁ <Ω head-Ω y₁
--     ≤′ rank-pow y₁                    -- by head-Ω-lower-bound
--     ≤′ rank-pow (bplus y₁ y₂)         -- by ⊕-left-≤-sum
--
-- The STRICT-JUMP step is the pinch.  By cases on x₁ (NonBzero
-- guarantees not bzero):
--
--   * x₁ = bOmega μ: `head-Ω-inv-bOmega : bOmega μ <ᵇ y₁ →
--     μ <Ω head-Ω y₁` is STRICT.  Closes directly.
--   * x₁ = bpsi ν α: `head-Ω-inv-bpsi : bpsi ν α <ᵇ y₁ →
--     ν ≤Ω head-Ω y₁` is NON-STRICT (tracks `<ᵇ-ψΩ≤` which
--     permits equal markers between ψ-source and Ω-target).
--     When `ν = head-Ω y₁`, the strict jump must come from α's
--     rank — which lives in the rank-adm refinement, NOT the
--     head-Ω route.
--   * x₁ = bplus a b: `head-Ω (bplus a b) = head-Ω a`; needs
--     recursive inversion on the leading-leaf shape.  When the
--     leading leaf is bOmega, closes via the bOmega case.  When
--     bpsi, hits the same pinch as above.
--
-- The Slice 3 closure path under design:
--
--   (A) Combine the head-Ω route with rank-lex (`Ordinal.Buchholz.
--       RankLex`) for the bpsi-source-at-equality sub-case.  The
--       rank-lex second component carries α-rank information that
--       discharges the equality case via `<ᵇ-+ψ` / `<ᵇ-ψα`-style
--       admissibility, mirroring the `<ᵇ-ψΩ≤` boundary closure
--       (RankLex.agda, 2026-05-27).
--
--   (B) Refine `head-Ω-inv-bpsi` to split on the source constructor:
--       report `<Ω` (strict) for `<ᵇ-ψΩ` and `<ᵇ-ψ+`, `≤Ω`
--       (non-strict) only for `<ᵇ-ψΩ≤`.  Then chain the equality
--       case through admissibility separately.
--
-- Both routes preserve the head-Ω discipline (no rank-mono
-- dependency in the inversion family — option (b) from
-- `RankPow.agda`'s Slice 2-bplus follow-on plan).  Route (A) is
-- cleaner: it composes existing landed primitives rather than
-- refining an inversion lemma.  Implementation is a follow-on
-- slice.
