{-# OPTIONS --safe --without-K #-}

-- Buchholz-layer manifest. Keeps load-bearing names pinned so that
-- accidental renames fail quickly in a focused module.

module Ordinal.Buchholz.Smoke where

open import Ordinal.OmegaMarkers using
  ( OmegaIndex
  ; fin
  ; ω
  ; _≤Ω_
  ; fin≤fin
  ; fin≤ω
  ; ω≤ω
  ; ≤Ω-refl
  ; ≤Ω-trans
  ; Omega0
  ; Omega1
  ; Omegaω
  ; Omega0≤Omega1
  ; Omega0≤Omegaω
  ; Omega1≤Omegaω
  )

open import Ordinal.Buchholz.Syntax using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  ; psi0
  )

open import Ordinal.Buchholz.Closure using
  ( Cν
  ; cν-zero
  ; cν-omega
  ; cν-plus
  ; cν-psi
  ; Cν-monotone
  ; Cν-index-monotone
  ; Cν-monotone-both
  ; cν-omega-index
  ; cν-psi-index
  ; cν-psi-decompose
  )

open import Ordinal.Buchholz.Order using
  ( _<ᵇ_
  ; <ᵇ-0-Ω
  ; <ᵇ-0-+
  ; <ᵇ-0-ψ
  ; <ᵇ-ΩΩ
  ; <ᵇ-Ωψ
  ; <ᵇ-ψΩ
  ; <ᵇ-ψΩ≤
  ; <ᵇ-Ω+
  ; <ᵇ-ψ+
  ; <ᵇ-+Ω
  ; <ᵇ-+ψ
  ; <ᵇ-+ω
  ; <ᵇ-+ψω
  ; <ᵇ-+1
  ; <ᵇ-irrefl
  ; <ᵇ-trans
  ; <ᵇ-inv-Ω+
  ; <ᵇ-inv-+Ω
  ; <ᵇ-inv-+Ωfin
  ; <ᵇ-inv-+Ωω
  ; <ᵇ-inv-ψ+
  ; <ᵇ-inv-+ψ
  ; <ᵇ-inv-+ψfin
  ; <ᵇ-inv-+ψω
  )

-- Earn-back item B (K-attributed part): same-binder constructors
-- usable directly; irreflexivity + transitivity K-free. See
-- docs/echo-types/earn-back-plan.adoc item B, F-2026-05-18b.
open import Ordinal.Buchholz.OrderExtendedDirect using
  ( _<ᵇᵈ_
  ; <ᵇ-ψα      -- same Ω-index lex (was "unconstructible pending K-free")
  ; <ᵇ-+2      -- same left-summand lex (idem)
  ; <ᵇ-irrefl
  ; <ᵇ-trans
  ; embed      -- conservativity: core `Order._<ᵇ_` ↪ `_<ᵇᵈ_`
  )

open import Ordinal.Buchholz.Psi using
  ( psiν-notin-Cν
  ; psiν-stage-lb
  ; psiν-index-bound
  ; psiν-at-succ
  ; psiν-least-gap
  )

open import Ordinal.Buchholz.Examples using
  ( bh-psi0-omega1
  ; bh-psi0-omegaω
  ; psi0-expands
  ; psi0-Omega1-target
  ; omega1-in-C1-at-0
  ; psi0-omega1-at-1-in-C1
  ; psi0-omega1-not-at-0-in-C1
  ; psi0-omega1-stage-lb-in-C1
  ; omega1-in-Cω-at-0
  ; psi0-omega1-at-1
  ; psi0-omega1-not-at-0
  )

open import Ordinal.Buchholz.WellFounded using
  ( <Ω-wf
  ; wf-<ᵇ
  ; <ᵇ-irreflexive
  )

open import Ordinal.Buchholz.WellFormed using
  ( WfΩ
  ; WfBT
  ; wf-fin
  ; wf-ω
  ; wf-bzero
  ; wf-bomega
  ; wf-bplus
  ; wf-bpsi
  ; BH
  ; BH-wf
  ; psi-OmegaOmega
  ; psi-OmegaOmega-wf
  )

open import Ordinal.Buchholz.VeblenInterface using
  ( VeblenWFInterface
  )

open import Ordinal.Buchholz.VeblenIdentityModel using
  ( identity-interface
  ; core-wf-from-identity
  )

open import Ordinal.Buchholz.VeblenMeasureTarget using
  ( Measure
  ; _≺M_
  ; by-index
  ; by-term
  ; ≺M-wf
  )

open import Ordinal.Buchholz.VeblenProjectionMeasure using
  ( proj-index
  ; proj-term
  ; proj-measure
  ; proj-dec-+2
  ; proj-dec-ψα
  ; proj-dec-ΩΩ
  ; proj-dec-Ωψ
  ; proj-dec-ψΩ
  ; proj-dec-ψΩ<
  )

open import Ordinal.Buchholz.VeblenComparisonTarget using
  ( ComparisonMeasure
  ; _≈ᶜ_
  ; _≺C_
  ; ≈ᶜ-+
  ; ≈ᶜ-ψ
  ; ≈ᶜ-ψ+
  ; ≺P-trans
  ; ≺C-trans
  ; by-first
  ; by-second
  ; ≺C-wf
  )

open import Ordinal.Buchholz.VeblenComparisonModel using
  ( cmp-payload
  ; cmp-measure
  ; cmp-dec-Ω+
  ; cmp-dec-ψ+-same-index
  ; cmp-dec-ψ+
  ; comparison-interface
  ; core-wf-from-comparison
  )

open import Ordinal.Buchholz.ExtendedOrder using
  ( _<ᵇ⁺_
  ; <ᵇ⇒<ᵇ⁺
  ; <ᵇ⁺-ψα
  ; <ᵇ⁺-+2
  ; <ᵇ⁺-trans
  ; wf-<ᵇ⁺
  ; <ᵇ⁺-irreflexive
  )

open import Ordinal.Buchholz.LiftedExtendedOrder using
  ( _<ᵇ⁺¹_
  ; <ᵇ⁺⇒<ᵇ⁺¹
  ; <ᵇ⁺¹-ψα
  ; <ᵇ⁺¹-+2
  ; <ᵇ⁺¹-ψ+2
  ; wf-<ᵇ⁺¹
  ; <ᵇ⁺¹-irreflexive
  )

open import Ordinal.Buchholz.IteratedExtendedOrder using
  ( LiftedOrder
  ; LiftedOrder-wf
  ; LiftedOrder-trans
  ; LiftedOrder-lift
  ; lift-ψα
  ; lift-+2
  ; lift-ψ+2
  ; LiftedOrder-irreflexive
  ; SurfaceDepth
  ; surf-core
  ; surf-ψα
  ; surf-+2
  ; surface⇒lifted
  ; SurfaceDepth-irreflexive
  )

open import Ordinal.Buchholz.RecursiveSurfaceOrder using
  ( _<ᵇʳᶠ_
  ; <ᵇʳᶠ-core
  ; <ᵇʳᶠ-ψα
  ; <ᵇʳᶠ-+2
  ; <ᵇʳᶠ-depth
  ; <ᵇʳᶠ⇒SurfaceDepth
  ; SurfaceDepth⇒<ᵇʳᶠ
  ; <ᵇʳᶠ-depth-witness
  ; <ᵇʳᶠ⇒lifted
  ; <ᵇʳᶠ-irreflexive
  )

open import Ordinal.Buchholz.RankPartial using
  ( ω-rank-mono-<Ω
  ; rank-mono-<ᵇ-0-Ω
  ; rank-mono-<ᵇ-0-ψ
  ; rank-mono-<ᵇ-ΩΩ
  ; rank-mono-<ᵇ-Ωψ
  ; rank-mono-partial-0-Ω
  ; rank-mono-partial-0-ψ
  ; rank-mono-partial-ΩΩ
  ; rank-mono-partial-Ωψ
  )

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
  ; wfcnf-to-wfbt
  ; leading
  ; wfcnf-leading-atomic
  ; BH-wf-cnf
  ; bplus-Ω-bzero-wf-cnf
  )

-- ψ-admissibility: strengthens WfCNF on `bpsi` with the rank-pow
-- bound `rank-pow α <′ ω-rank-pow ν`.  Carrier only in this slice;
-- rank refinement for the `<ᵇ-ψα` / `<ᵇ-ψΩ≤` discharge is a follow-on.
open import Ordinal.Buchholz.WellFormedAdmissible using
  ( WfAdm
  ; wf-adm-bzero
  ; wf-adm-bomega
  ; wf-adm-bpsi
  ; wf-adm-bplus
  ; wfAdm-to-wfCNF
  ; psi-trivial
  ; psi-trivial-adm
  )

open import Ordinal.Buchholz.OrderRestricted using
  ( _<ᵇ⁻_
  ; cnf-strict
  ; <ᵇ⁻-to-<ᵇ
  ; wf-<ᵇ⁻
  ; <ᵇ⁻-irrefl
  ; <ᵇ⁻-trans
  )

-- Path-1 umbrella: rank-pow strict-mono on the 10-constructor
-- rank-soundness-ready subset `_<ᵇ⁰_` of `_<ᵇ_`.  Closes 10 of 13
-- cases of the Buchholz rank-monotonicity theorem under WfCNF;
-- the 3 excluded cases (`<ᵇ-0-+` edge, `<ᵇ-ψα` / `<ᵇ-ψΩ≤`
-- admissibility-blocked, `<ᵇ-+1` bplus-target sub-case) remain
-- open under documented structural blockers.
open import Ordinal.Buchholz.RankMonoUmbrella using
  ( _<ᵇ⁰_
  ; _≤ᵇ⁰_
  ; ≤ᵇ⁰-refl
  ; rank-pow-mono-<ᵇ⁰
  ; rank-pow-mono-≤ᵇ⁰
  )

open import Ordinal.Buchholz.RecursiveSurfaceBudget using
  ( BudgetedBT
  ; _<ᵇʳᶠᵇ_
  ; spend
  ; wf-<ᵇʳᶠᵇ
  ; <ᵇʳᶠᵇ-irreflexive
  ; <ᵇʳᶠᵇ⇒lifted
  )

open import Ordinal.Buchholz.OrderExtendedBudget using
  ( BudgetedBT⁺
  ; _<ᵇ⁺ᵇ_
  ; wf-<ᵇ⁺ᵇ
  ; <ᵇ⁺ᵇ-irreflexive
  )

open import Ordinal.Buchholz.SurfaceOrder using
  ( _<ᵇˢ_
  ; <ᵇˢ-core
  ; <ᵇˢ-ψα
  ; <ᵇˢ-+2
  ; <ᵇˢ⇒<ᵇ⁺
  ; wf-<ᵇˢ
  ; <ᵇˢ-irreflexive
  ; SurfaceLiftInterface
  ; _<ᵇʳ_
  ; <ᵇʳ-core
  ; <ᵇʳ-ψα
  ; <ᵇʳ-+2
  ; <ᵇʳ⇒<ᵇ⁺
  ; wf-<ᵇʳ
  ; <ᵇʳ-irreflexive
  ; <ᵇ⁺-no-ψ-bzero-plus
  ; surfaceLiftPremise
  ; surfaceLiftBlocked
  )

open import Ordinal.Buchholz.VeblenObligations using
  ( plus-right
  ; psi-arg
  ; dec-+2-plus-right
  ; dec-ψα-psi-arg
  )

-- Lane 3 active-push slice 2026-05-26 (own block per CLAUDE.md
-- Working rules): admissibility-aware rank `rank-adm`, the
-- pointwise dominance `rank-pow≤rank-adm`, the headline ψα
-- primitive `rank-mono-<ᵇ⁺-ψα-from-pow` that closes 1 of the 2
-- ψ-admissibility-blocked constructor cases, and bpsi-positivity.
-- The remaining `<ᵇ-ψΩ≤` ν=μ case is documented as still-open
-- with the design follow-up options listed in `RankAdm.agda`'s
-- own preamble.
open import Ordinal.Buchholz.RankAdm using
  ( rank-adm
  ; rank-adm-bzero
  ; rank-adm-bOmega
  ; rank-adm-bplus
  ; rank-adm-bpsi
  ; rank-adm-pos-bpsi
  ; rank-pow≤rank-adm
  ; rank-mono-<ᵇ⁺-ψα-from-pow
  )

-- Lane 3 follow-on slice 2026-05-27 (own block per CLAUDE.md
-- Working rules): lex-pair rank `rank-lex` discharging the
-- `<ᵇ-ψΩ≤` ν=μ boundary case that `rank-adm` left structurally
-- open.  Option (A) from `RankAdm.agda` §"<ᵇ-ψΩ≤-still-open"
-- (lex pair over `Ord × Ord`).  Headline
-- `rank-mono-<ᵇ-ψΩ≤-lex` covers both ν<μ and ν=μ sub-cases.
open import Ordinal.Buchholz.RankLex using
  ( RankLex
  ; mkLex
  ; _<lex_
  ; <lex-first
  ; <lex-second
  ; rank-lex
  ; rank-lex-bzero
  ; rank-lex-bOmega
  ; rank-lex-bpsi
  ; rank-lex-bplus
  ; rank-mono-<ᵇ-ψΩ≤-lex
  )

-- Lane 3 head-Ω first slice 2026-05-27 evening (own block per
-- CLAUDE.md Working rules): the leading-Ω-index head function
-- `head-Ω : BT → OmegaIndex` plus four definitional sanity lemmas,
-- one per `BT` constructor.  No rank-mono in this slice — the
-- domination lemma `rank-pow t <′ ω-rank-pow-succ (head-Ω t)` and
-- the headline `<ᵇ-+1` joint-bplus discharge are explicitly deferred
-- to follow-on slices.  First piece of option (A) per
-- `RankPow.agda`'s preamble and `docs/echo-types/buchholz-rank-
-- obstruction.adoc` §"What remains open".
open import Ordinal.Buchholz.HeadOmega using
  ( head-Ω
  ; head-Ω-bzero
  ; head-Ω-bOmega
  ; head-Ω-bplus
  ; head-Ω-bpsi
  ; head-Ω-bplus-left
  )

-- Lane 3 head-Ω Slice 2 (own block per CLAUDE.md Working rules):
-- the per-marker "next ω-power up" target `ω-rank-pow-succ` plus
-- definitional sanity at the fin branch, the per-marker strict
-- dominance at fin (`ω-rank-pow-<-succ-fin`), and the atomic
-- rank-pow factoring through head-Ω.  The ω-branch strict
-- dominance and the full domination lemma over WfCNF carriers are
-- deferred to follow-on slices Slice 2-omega and Slice 2-bplus
-- respectively, per the obstruction note inline in `RankPow.agda`
-- (the originally-proposed `ω-rank-pow-succ ω = olim (λ n →
-- ω^(suc(suc n)))` represents the same ordinal as `ω-rank-pow ω`,
-- so strict dominance at ω needs a different shape).
open import Ordinal.Buchholz.RankPow using
  ( ω-rank-pow-succ
  ; ω-rank-pow-succ-fin
  ; ω-rank-pow-succ-omega
  ; ω-rank-pow-<-succ-fin
  ; ω-rank-pow-<-succ-omega
  ; ω-rank-pow-<-succ
  ; rank-pow-bOmega-via-head-Ω
  ; rank-pow-bpsi-via-head-Ω
  )

-- Lane 3 head-Ω inversion (own block per CLAUDE.md Working rules):
-- option (b) of the Slice 2-bplus follow-on plan from `RankPow.agda`'s
-- preamble.  Two atomic-source inversions pulling `head-Ω` bounds
-- from an `<ᵇ` premise WITHOUT going through rank-mono — keeps the
-- domination lemma's dependency-graph clean against future signature
-- changes to `rank-pow-mono-≤ᵇ`.  Strict on the Ω-source, non-strict
-- on the ψ-source (tracks the `<ᵇ-ψΩ≤` constructor).
open import Ordinal.Buchholz.HeadOmegaInversion using
  ( head-Ω-inv-bOmega
  ; head-Ω-inv-bpsi
  )

-- Lane 3 head-Ω Slice 2-bplus (own block per CLAUDE.md Working
-- rules): the full WfCNF-carrier domination lemma.  Composes Slice
-- 1 + Slice 2 + Slice 2-omega + the inversion family into THE
-- headline that the eventual `<ᵇ-+1` joint-bplus discharge
-- (Slice 3, follow-on) will consume.  No `NonBzero` premise needed
-- — `rank-pow bzero = oz` is strictly below `ω-rank-pow-succ
-- (fin 0) = ω^2`, so the bzero case discharges uniformly.  No
-- rank-mono dependency anywhere in the chain (option (b)
-- discipline preserved).
open import Ordinal.Buchholz.RankPowDomination using
  ( ω-rank-pow-mono-≤Ω
  ; ω-rank-pow-succ-pos
  ; additive-principal-ω-rank-pow-succ
  ; rank-pow-dominated-by-head-Ω
  )

-- Slice 3 prerequisites (own block per CLAUDE.md Working rules):
-- the left-spine NonBzero predicate, the strict-jump bridge from
-- `μ <Ω ν` to `ω-rank-pow-succ μ ≤′ ω-rank-pow ν`, and the head-Ω
-- LOWER bound under WfCNF + NonBzero (dual of
-- `rank-pow-dominated-by-head-Ω`).  The Slice 3 headline
-- `rank-mono-<ᵇ-+1-via-head-Ω` itself remains open at the
-- ψ-source-at-equality sub-case; design note inside the module.
open import Ordinal.Buchholz.RankPowSlice3 using
  ( NonBzero
  ; nz-bOmega
  ; nz-bpsi
  ; nz-bplus
  ; ω-rank-pow-succ-≤-via-<Ω
  ; head-Ω-lower-bound
  )

-- Slice 3 headline (own block per CLAUDE.md Working rules): closes
-- the joint-bplus rank-mono case for `_<ᵇ-+1_` under a strict-head
-- premise `head-Ω x₁ <Ω head-Ω y₁`.  The premise is the burden
-- this primitive bumps up to the caller (the umbrella's case-split
-- on `x₁ <ᵇ y₁`); for x₁ = bOmega it discharges via
-- `head-Ω-inv-bOmega` directly, for x₁ = bpsi at strict ν<Ω head-Ω y₁
-- via `head-Ω-inv-bpsi` + `<Ω→` upgrade, for x₁ = bpsi at equality
-- via rank-adm / rank-lex combination (Route A from the design
-- note in `RankPowSlice3`).  The Slice 3 closure is now headline-
-- level; the umbrella's case-split is the remaining wiring.
open import Ordinal.Buchholz.RankPowSlice3Headline using
  ( rank-mono-<ᵇ-+1-via-head-Ω
  )

-- Slice 3 umbrella extension (own block per CLAUDE.md Working
-- rules): the new `_<ᵇ¹_` relation extends `_<ᵇ⁰_` with a
-- joint-bplus constructor `<ᵇ¹-+1-+` carrying the strict-head
-- premise `head-Ω x₁ <Ω head-Ω y₁` plus WfCNF / NonBzero side
-- conditions.  The umbrella `rank-pow-mono-<ᵇ¹` forwards the
-- inherited cases to `rank-pow-mono-<ᵇ⁰` and the new case to
-- the Slice 3 headline `rank-mono-<ᵇ-+1-via-head-Ω`.  The
-- bpsi-source-at-equality sub-case is documented as gated:
-- it requires a `<ᵇ-+1`-specific rank-lex primitive not yet
-- in the repo (the existing `RankLex.rank-mono-<ᵇ-ψΩ≤-lex`
-- discharges `<ᵇ-ψΩ≤`, not `<ᵇ-+1`).
open import Ordinal.Buchholz.RankMonoUmbrellaSlice3 using
  ( _<ᵇ¹_
  ; <ᵇ¹-from-<ᵇ⁰
  ; <ᵇ¹-+1-+
  ; rank-pow-mono-<ᵇ¹
  )

-- Slice 3 lex-rank companion 2026-05-28 (own block per CLAUDE.md
-- Working rules): the bpsi-source-at-equality sub-case of
-- `<ᵇ-+1` joint-bplus.  Closes the ψ-rank-level discharge (via
-- `rank-adm-bpsi-strict-at-equality` / `rank-lex-bpsi-strict-at-
-- equality`) under the α/β strict-rank witness from the umbrella;
-- the bplus-chain-level extension to a strict step on the full
-- bplus sum is structurally blocked (additive-principal closure on
-- a generic `ω-rank-pow ν ⊕ rank-pow β` sum doesn't hold, and
-- strict-left-mono of `_⊕_` is a non-theorem).  Honest scope: pins
-- the ψ-rank discharge as a named theorem accessible from the
-- joint-bplus umbrella consumer + documents the bplus-chain
-- obstacle inline so the next session sees exactly which lemmas
-- would unblock it.  Complements `RankMonoUmbrellaSlice3`'s
-- gated documentation of the same sub-case from the umbrella side.
open import Ordinal.Buchholz.RankLexSlice3 using
  ( rank-adm-bpsi-strict-at-equality
  ; rank-lex-bpsi-strict-at-equality
  ; rank-adm-bplus-decompose-left
  )
