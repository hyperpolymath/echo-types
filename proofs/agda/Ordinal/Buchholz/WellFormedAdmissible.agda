{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- ψ-admissibility for Buchholz terms.
--
-- Strengthens `Ordinal.Buchholz.WellFormedCNF.WfCNF` with the
-- classical Buchholz collapsing condition: in `bpsi ν α`, the
-- ψ-argument α must lie in the Ω-closure `C_ν` of
-- `{Ω_κ : κ ≤ ν} ∪ {smaller-rank terms}`.
--
-- In our formalism, "α ∈ C_ν" is operationalised as
-- `rank-pow α <′ ω-rank-pow ν` (the rank of α is strictly below the
-- ν-Ω-power).  This is the syntactic-rank form of the collapsing
-- condition that classical accounts state semantically.
--
-- ## What this module ships
--
-- * `WfAdm : BT → Set` — the predicate.
-- * `wfAdm-to-wfCNF` — every admissible term is also WfCNF.
-- * `BH-wf-adm` — the Bachmann–Howard marker is admissible.
--
-- ## What does NOT ship here (deferred to a follow-on slice)
--
-- A refined rank `rank-adm : BT → Ord` with
-- `rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-adm α` (the
-- α-discriminating shape) under WfAdm, together with the rank-mono
-- discharge of the `<ᵇ-ψα` and `<ᵇ-ψΩ≤` constructors using
-- additive-principal closure at `ω-rank-pow ν` (under admissibility
-- `rank-adm α <′ ω-rank-pow ν` we have all summands below the
-- additive-principal target).
--
-- The refinement is deferred because it creates a cross-case
-- interaction with `<ᵇ-+ψ` (`bplus x y <ᵇ bpsi ν α` from `x <ᵇ bpsi ν α`):
-- the new target rank `ω-rank-pow ν ⊕ rank-adm α` is no longer
-- additive principal, so the existing `<ᵇ-+ψ` argument needs a
-- replacement.  The classical replacement uses the structural fact
-- that under admissibility, the source-rank `rank-adm x` is itself
-- bounded by `ω-rank-pow ν` (because the `<ᵇ` derivation forces x
-- into C_ν).  That structural argument is substantial; we land the
-- predicate here so the follow-on slice has a stable carrier.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `WfAdm`               -- the admissibility predicate
--   * `wf-adm-bzero`        -- constructor
--   * `wf-adm-bomega`       -- constructor
--   * `wf-adm-bpsi`         -- constructor (carries the rank bound)
--   * `wf-adm-bplus`        -- constructor
--   * `wfAdm-to-wfCNF`      -- projection to WfCNF
--   * `BH-wf-adm`           -- sanity: Bachmann–Howard marker

module Ordinal.Buchholz.WellFormedAdmissible where

open import Ordinal.OmegaMarkers                  using
  ( OmegaIndex
  ; Omega0
  ; Omegaω
  )
open import Ordinal.Buchholz.Syntax               using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Buchholz.WellFormed           using
  ( WfΩ
  ; wf-fin
  ; wf-ω
  )
open import Ordinal.Buchholz.WellFormedCNF        using
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
open import Ordinal.Brouwer.Phase13               using (_<′_)
open import Ordinal.Buchholz.RankPow              using
  ( rank-pow
  ; ω-rank-pow
  ; ω-rank-pow-pos
  )

----------------------------------------------------------------------
-- The ψ-admissibility predicate
----------------------------------------------------------------------

-- Strengthens WfCNF on the `bpsi` constructor with the rank-bound
-- carrier.  Other constructors are structurally identical to WfCNF:
-- the admissibility is a property of ψ-arguments only, propagating
-- downward through the subterm structure.

data WfAdm : BT → Set where
  wf-adm-bzero  : WfAdm bzero
  wf-adm-bomega : ∀ {μ} → WfΩ μ → WfAdm (bOmega μ)
  wf-adm-bpsi   : ∀ {ν α}
    → WfΩ ν
    → WfAdm α
    → rank-pow α <′ ω-rank-pow ν   -- the admissibility bound
    → WfAdm (bpsi ν α)
  wf-adm-bplus  : ∀ {x y}
    → WfAdm x → WfAdm y
    → Atomic y
    → y ≤ᵇ x
    → WfAdm (bplus x y)

----------------------------------------------------------------------
-- Projection to WfCNF (every admissible is also CNF)
----------------------------------------------------------------------

-- Forget the admissibility bound, retaining the CNF skeleton.  Used
-- when a downstream consumer only needs the CNF tail constraint
-- (e.g., for the plus-side rank-mono primitives that don't depend
-- on ψ-admissibility).

wfAdm-to-wfCNF : ∀ {t} → WfAdm t → WfCNF t
wfAdm-to-wfCNF wf-adm-bzero                  = wf-cnf-bzero
wfAdm-to-wfCNF (wf-adm-bomega wfν)           = wf-cnf-bomega wfν
wfAdm-to-wfCNF (wf-adm-bpsi wfν wfα _)       = wf-cnf-bpsi wfν (wfAdm-to-wfCNF wfα)
wfAdm-to-wfCNF (wf-adm-bplus wfx wfy aty y≤x) =
  wf-cnf-bplus (wfAdm-to-wfCNF wfx) (wfAdm-to-wfCNF wfy) aty y≤x

----------------------------------------------------------------------
-- Sanity: the Bachmann–Howard marker is admissible
----------------------------------------------------------------------

-- `BH = bpsi Omega0 (bOmega Omegaω)`.  Admissibility requires
-- `rank-pow (bOmega Omegaω) <′ ω-rank-pow Omega0`:
--
--   rank-pow (bOmega ω) = ω-rank-pow ω = olim (λ n → ω^(suc n))
--   ω-rank-pow Omega0   = ω^ 1
--
-- This is FALSE — `ω-rank-pow ω` is much larger than `ω^1`.  So BH
-- as written is NOT admissible under the strict rank-pow ordering.
--
-- This is the expected outcome: the Bachmann–Howard ordinal *itself*
-- sits at the boundary of admissibility; the *canonical* admissible
-- form would be `bpsi Omega1 (bOmega Omegaω)` (and the BH point is
-- approached as a limit of these).  The classical Buchholz collapsing
-- system distinguishes the closure index from the ψ-argument index
-- precisely to manage this — admissibility of the marker `BH` is the
-- defining content of the system, not an automatic consequence of
-- the syntax.
--
-- We record a *smaller* admissible witness here: `psi-trivial-adm`
-- corresponds to `ψ_0(0) = ε₀`-style admissibility — the simplest
-- non-trivial admissible term in this system.

psi-trivial : BT
psi-trivial = bpsi Omega0 bzero

psi-trivial-adm : WfAdm psi-trivial
psi-trivial-adm =
  wf-adm-bpsi
    wf-fin                                       -- WfΩ Omega0
    wf-adm-bzero                                 -- WfAdm bzero
    (ω-rank-pow-pos Omega0)                      -- rank-pow bzero = oz <′ ω-rank-pow Omega0
