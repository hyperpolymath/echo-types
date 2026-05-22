{-# OPTIONS --safe --without-K #-}

-- Cantor-Normal-Form well-formedness for Buchholz terms.
--
-- Strengthens `Ordinal.Buchholz.WellFormed.WfBT` (which only
-- structurally recurses through subterms) with the CNF tail
-- constraint on `bplus`: in `bplus x y`, the right summand `y`
-- must be *atomic* (not itself a `bplus`) AND `y ≤ᵇ x` under the
-- existing K-free core order `_<ᵇ_`.
--
-- ## Why this matters for the Buchholz unbudgeted-WF unblock
--
-- Per `buchholz-rank-obstruction.adoc`, the SA-recommended
-- additive rank-mono `rank-mono-<ᵇ : x <ᵇ y → rank x <′ rank y`
-- is impossible because 9 of `_<ᵇ_`'s 13 constructors are
-- ordinally unsound when the right summand of a `bplus` (or the
-- ψ-argument of a `bpsi`) is unconstrained.  Concrete witness:
-- `<ᵇ-+Ω <ᵇ-0-Ω : bplus bzero (bOmega (fin 1)) <ᵇ bOmega (fin 0)`,
-- but additive rank gives `two <′ one`, which is `⊥`.
--
-- The CNF tail constraint — `bplus x y` admits only `y ≤ᵇ x` with
-- `y` atomic — eliminates exactly this class of witnesses:
-- `bplus bzero (bOmega (fin 1))` is no longer WfCNF (the right
-- summand outsizes the left).  Under the WfCNF restriction, the
-- 5 `bplus`-related failing constructors (`<ᵇ-Ω+`, `<ᵇ-ψ+`,
-- `<ᵇ-+Ω`, `<ᵇ-+ψ`, `<ᵇ-+1`) become ordinally sound: their
-- premises imply both summands are below the target.
--
-- This module ships the *predicate* and basic *projection lemmas*.
-- The full unblock — the WfCNF-restricted relation `_<ᵇ⁻_`, its
-- transitivity / well-foundedness re-proofs, and the WfCNF-tagged
-- rank-mono lemmas for the 5 newly-discharged cases — is the next
-- multi-session step.
--
-- ## ψ-admissibility deferred
--
-- The remaining 2 unsound constructors (`<ᵇ-ψΩ`, `<ᵇ-ψΩ≤`) are
-- the ψ-side analogues: ψ_ν(α) at fixed ν with α unbounded.  Their
-- repair requires a *ψ-admissibility* constraint — α must lie in
-- the Ω-closure C_ν of {Ω_κ : κ ≤ ν} ∪ smaller-ranked terms.  This
-- is the standard Buchholz collapsing condition; it is genuinely
-- complex (multi-pass closure operator, ≈80 lines of Agda) and is
-- deferred to a follow-on module `WellFormedAdmissible.agda`.
-- This module's `wf-cnf-bpsi` constructor uses the basic
-- structural recursion (matching `WellFormed.WfBT`); upgrading
-- to admissibility is the next step.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * Atomic            -- the "not a bplus" predicate
--   * WfCNF             -- the stronger well-formedness
--   * wfcnf-to-wfbt     -- WfCNF refines WfBT (projection)
--   * wfcnf-leading-atomic — leading subterm of a WfCNF is atomic
--   * BH-wf-cnf         -- the Bachmann-Howard marker is WfCNF

module Ordinal.Buchholz.WellFormedCNF where

open import Data.Sum.Base                         using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Ordinal.OmegaMarkers                  using
  ( OmegaIndex
  ; Omega0
  ; Omegaω
  )
open import Ordinal.Buchholz.Syntax               using (BT; bzero; bOmega; bplus; bpsi)
open import Ordinal.Buchholz.Order                using (_<ᵇ_)
open import Ordinal.Buchholz.WellFormed           using
  ( WfΩ
  ; wf-fin
  ; wf-ω
  ; WfBT
  ; wf-bzero
  ; wf-bomega
  ; wf-bplus
  ; wf-bpsi
  )

----------------------------------------------------------------------
-- Atomic terms: bzero, bOmega μ, or bpsi ν α — the not-a-bplus heads
----------------------------------------------------------------------

-- Atomic = "not a `bplus`".  In Cantor normal form, the right
-- summand of a `bplus` is always atomic; nested `bplus` chains go
-- left-only.  Three constructors match the three non-bplus heads
-- of BT.

data Atomic : BT → Set where
  atomic-bzero  : Atomic bzero
  atomic-bomega : ∀ {μ} → Atomic (bOmega μ)
  atomic-bpsi   : ∀ {ν α} → Atomic (bpsi ν α)

----------------------------------------------------------------------
-- Non-strict order: _≤ᵇ_ = _<ᵇ_ ⊎ _≡_
----------------------------------------------------------------------

-- The non-strict version of `_<ᵇ_`, used for the CNF tail bound.
-- A bare sum disjunction is enough — we don't need a constructor-
-- based shape here since the only consumer is the CNF predicate's
-- single tail-bound field.

_≤ᵇ_ : BT → BT → Set
x ≤ᵇ y = (x <ᵇ y) ⊎ (x ≡ y)

infix 4 _≤ᵇ_

----------------------------------------------------------------------
-- The CNF well-formedness predicate
----------------------------------------------------------------------

-- WfCNF strengthens `WfBT`:
--   * bzero, bOmega μ, bpsi ν α: structural (same as WfBT).
--   * bplus x y: y must be atomic AND y ≤ᵇ x.
--
-- The atomicity constraint forces nested `bplus` chains to lean
-- left; the order constraint forces the right summand to not
-- outsize the left.  Together these are the classical Cantor-
-- normal-form discipline.

data WfCNF : BT → Set where
  wf-cnf-bzero  : WfCNF bzero
  wf-cnf-bomega : ∀ {μ} → WfΩ μ → WfCNF (bOmega μ)
  wf-cnf-bpsi   : ∀ {ν α} → WfΩ ν → WfCNF α → WfCNF (bpsi ν α)
  wf-cnf-bplus  :
    ∀ {x y}
    → WfCNF x
    → WfCNF y
    → Atomic y
    → y ≤ᵇ x
    → WfCNF (bplus x y)

----------------------------------------------------------------------
-- Projection: WfCNF refines WfBT
----------------------------------------------------------------------

-- Every WfCNF term is also WfBT.  The reverse is false — `WfBT`
-- admits `bplus (bplus _ _) _` (rightward-nested bplus) and
-- `bplus bzero (bOmega ω)` (right summand exceeds left), neither
-- of which is WfCNF.

wfcnf-to-wfbt : ∀ {t} → WfCNF t → WfBT t
wfcnf-to-wfbt wf-cnf-bzero               = wf-bzero
wfcnf-to-wfbt (wf-cnf-bomega wfμ)        = wf-bomega wfμ
wfcnf-to-wfbt (wf-cnf-bpsi wfν wfα)      = wf-bpsi wfν (wfcnf-to-wfbt wfα)
wfcnf-to-wfbt (wf-cnf-bplus wfx wfy _ _) =
  wf-bplus (wfcnf-to-wfbt wfx) (wfcnf-to-wfbt wfy)

----------------------------------------------------------------------
-- Leading subterm
----------------------------------------------------------------------

-- The "leading" (leftmost non-bplus) subterm.  For a CNF term, the
-- leading subterm is the dominant ordinal exponent — what classical
-- arithmetic calls `α₁` in `α = α₁ + α₂ + … + αₙ`.

leading : BT → BT
leading bzero        = bzero
leading (bOmega μ)   = bOmega μ
leading (bpsi ν α)   = bpsi ν α
leading (bplus x _)  = leading x

----------------------------------------------------------------------
-- For a WfCNF term, the leading subterm is atomic.
----------------------------------------------------------------------

-- Structural recursion on the WfCNF derivation.  The bzero/bOmega/
-- bpsi cases are immediate (the term itself is atomic); the bplus
-- case recurses on the left summand's WfCNF, which is itself a
-- WfCNF term whose leading is atomic by IH.

wfcnf-leading-atomic : ∀ {t} → WfCNF t → Atomic (leading t)
wfcnf-leading-atomic wf-cnf-bzero               = atomic-bzero
wfcnf-leading-atomic (wf-cnf-bomega _)          = atomic-bomega
wfcnf-leading-atomic (wf-cnf-bpsi _ _)          = atomic-bpsi
wfcnf-leading-atomic (wf-cnf-bplus wfx _ _ _)   = wfcnf-leading-atomic wfx

----------------------------------------------------------------------
-- The Bachmann-Howard marker is WfCNF
----------------------------------------------------------------------

-- `BH = bpsi Omega0 (bOmega Omegaω)` is the stage-S2 target.  It is
-- structurally simple (bpsi-of-bOmega), so WfCNF lands trivially.

BH-wf-cnf : WfCNF (bpsi Omega0 (bOmega Omegaω))
BH-wf-cnf = wf-cnf-bpsi wf-fin (wf-cnf-bomega wf-ω)

----------------------------------------------------------------------
-- A small witness exhibiting the discrimination
----------------------------------------------------------------------

-- `bplus (bOmega Omegaω) bzero` IS WfCNF (right summand is atomic
-- and bzero ≤ᵇ bOmega Omegaω via `<ᵇ-0-Ω`).
--
-- `bplus bzero (bOmega (fin 1))` is NOT WfCNF — the right summand
-- bOmega outsizes the bzero left.  This is exactly the
-- counterexample shape from `buchholz-rank-obstruction.adoc`.

-- Sanity witness for the well-formed direction:
open import Ordinal.Buchholz.Order                using (<ᵇ-0-Ω)

bplus-Ω-bzero-wf-cnf : WfCNF (bplus (bOmega Omegaω) bzero)
bplus-Ω-bzero-wf-cnf =
  wf-cnf-bplus
    (wf-cnf-bomega wf-ω)
    wf-cnf-bzero
    atomic-bzero
    (inj₁ <ᵇ-0-Ω)
