{-# OPTIONS --safe --without-K #-}

-- Headline-theorem manifest. Pins the load-bearing names from each bridge
-- module via `using` clauses so a silent rename or deletion fails CI fast,
-- even if the rest of the suite still typechecks.

module Smoke where

open import Echo using
  ( Echo
  ; echo-intro
  ; map-over
  ; map-over-id
  ; map-over-comp
  ; map-square
  ; Echo-comp-iso-to
  ; Echo-comp-iso-from
  ; Echo-comp-iso-from-to
  ; Echo-comp-iso-to-from
  ; cancel-iso-to
  ; cancel-iso-from
  ; cancel-iso-from-to
  ; cancel-iso-to-from
  ; hom-natural-id
  ; Echo-comp-iso-pent-B
  ; Echo-comp-iso-pent-echo
  ; Echo-comp-pent-Σ-assoc-to
  ; Echo-comp-pent-Σ-assoc-from
  ; Echo-comp-pent-Σ-assoc-from-to
  ; Echo-comp-pent-Σ-assoc-to-from
  ; Echo-comp-iso
  ; cancel-iso
  ; Echo-comp-pent-Σ-assoc
  )
-- Pillar A of docs/echo-types/establishment-plan.adoc: the
-- definitional Echo ≃ fib bridge, pinned so a rename fails CI fast.
open import EchoFiberBridge using (fiber; echo→fib; fib→echo; echo↔fib)

open import EchoCharacteristic using (collapse; echo-true; echo-false; echo-true≢echo-false)
open import EchoResidue using (EchoR; collapse-to-residue; strict-weakening-collapse; no-section-collapse-to-residue)
open import EchoExamples using (square9; visible; quot; collapse-residue-identifies)
open import VecRotation using (rotL-alternating; rotR-alternating; map-alternating)

open import EchoApprox using
  ( Tolerance
  ; PseudoMetric
  ; module Approx
  )

open import EchoIndexed using
  ( Echoᵢ
  ; echoᵢ-intro
  ; forget-role
  ; role-sound
  ; map-role-indexed
  ; map-role-indexed-id
  ; map-role-indexed-comp
  ; forget-role-map-role-indexed
  )

open import EchoDecidable using
  ( EchoDec
  ; echo-dec-intro
  ; echo-dec-pull
  ; echo-dec-respect-≡
  ; echo-dec-fin
  ; echo-dec-compose-iso
  ; echo-dec-compose-fin
  )

open import EchoFiberCount using
  ( FiberSize-fin
  ; FiberSize-fin-no-hit
  ; FiberSize-fin-all-hit
  ; FiberSize-fin-id-zero
  ; FiberSize-fin-const
  ; FiberSize-fin≡0⇒no-echo
  ; no-echo⇒FiberSize-fin≡0
  )

open import EchoThermodynamics using
  ( landauer-bound
  ; fiber-erasure-bound
  ; ⌊log₂1⌋≡0
  ; bennett-reversible
  ; bennett-reversible-id-zero
  ; landauer-collapse
  )

open import EchoChoreo using
  ( Role
  ; Global
  ; obs
  ; RoleEcho
  ; client-non-injective
  ; server-non-injective
  ; client-to-server
  ; client-stability
  ; client-preimage-class
  ; _⊑c_
  ; ⊑c-trans
  ; ⊑c-prop
  ; applyChoreo
  ; applyChoreo-comp
  ; _⊔c_
  ; ⊑c-⊔c-left
  ; ⊑c-⊔c-right
  ; ⊑c-⊔c-univ
  ; applyChoreo-compose
  ; applyChoreo-via-join
  )

open import EchoEpistemic using
  ( Indist
  ; Knows
  ; knowledge-monotone
  ; not-knows-server-true-at-client-true
  ; shared-echo-from-indist
  ; indist-from-two-echoes
  )

open import EchoLinear using
  ( Mode
  ; LEcho
  ; weaken
  ; strict-linear-example
  ; no-section-weaken
  ; _≤m_
  ; ≤m-trans
  ; ≤m-prop
  ; _⊔m_
  ; ≤m-⊔m-left
  ; ≤m-⊔m-right
  ; ≤m-⊔m-univ
  ; degradeMode
  ; degradeMode-comp
  ; degradeMode-compose
  ; degradeMode-via-join
  )

open import EchoGraded using
  ( Grade
  ; degrade
  ; degrade-comp
  ; ⊔g-assoc
  ; ≤g-prop
  ; ≤g-⊔g-left
  ; ≤g-⊔g-right
  ; ≤g-⊔g-univ
  ; degrade-compose
  ; degrade-via-join
  )

-- Pillar B of docs/echo-types/establishment-plan.adoc: echo as a
-- graded comonad of structured loss. Thin slice — counit + the
-- coassociativity verdict (no path algebra beyond ≤g-prop).
open import EchoGradedComonad using
  ( gextract
  ; gduplicate
  ; gcomonad-counit-l
  ; gcomonad-counit-r
  ; gcomonad-coassoc
  )

-- Pillar B (part 1): Echo as the pullback of f along y : ⊤ → B,
-- with the terminal-cone universal property. SliceHom IS a cone.
open import EchoPullback using
  ( EchoCone
  ; echo-cone
  ; cone→slice
  ; slice→cone
  ; cone→slice→cone
  ; slice→cone→slice
  ; IsMediator
  ; echo-pullback-univ
  )

-- Pillar C: separating model — generic Σ-functoriality holds while
-- the characteristic loss-grade composition law fails (carried
-- precisely by propositionality of the loss order).
open import EchoSeparating using
  ( _⊑_
  ; deg
  ; sep-order-not-prop
  ; sep-map-over-id
  ; sep-map-over-comp
  ; SepDegradeCompose
  ; sep-degrade-compose-fails
  )

-- Pillar D: second model + model-independence. The graded-comonad
-- laws proved once for any GradedLossModel; Set and relational
-- instances; they agree under the graph/fibration bridge.
open import EchoRelModel using
  ( GradedLossModel
  ; set-model
  ; rel-model
  ; rel-gcomonad-counit-l
  ; rel-gcomonad-counit-r
  ; rel-gcomonad-coassoc
  ; model-agreement
  ; bridge-natural
  )

open import EchoTropical using
  ( Candidate
  ; score
  ; tropical-non-injective
  ; IsArgmin
  ; TropEcho
  ; distinct-candidates-same-visible-distinct-echo
  )

open import EchoIntegration using
  ( knowledge-preserved-under-choreo
  ; merged-at-residue
  ; no-recovery-after-residue-degrade
  ; knowledge-and-controlled-degradation
  )

open import EchoCNOBridge using
  ( program-to-unit
  ; ProgramEcho
  ; cno-program-echo
  ; empty-cno-echo
  ; halt-cno-echo
  ; absolute-zero-echo
  ; cno-compose-echo
  )

open import EchoOrdinal using
  ( ordinal-collapse
  ; ordinal-left
  ; ordinal-right
  ; ordinal-left≢ordinal-right
  ; ordinal-collapse-non-injective
  ; ordinal-echo-left
  ; ordinal-echo-right
  ; ordinal-echo-left≢ordinal-echo-right
  ; distinct-provenances-same-visible
  ; ordinal-psi-arg-bzero
  ; ordinal-psi-arg-omega1
  ; ordinal-psi-args-distinct
  ; ordinal-psi-arg-collapse-agree
  ; ordinal-echo-psi-bzero
  ; ordinal-echo-psi-omega1
  ; ordinal-echo-psi-distinct
  ; no-section-ordinal-collapse
  ; IsZeroSource
  ; ordinal-collapse-classification
  )

open import Ordinal.Base using
  ( OT
  ; zero
  ; omega
  ; plus
  ; psi
  )

open import Ordinal.Closure using
  ( C
  ; c-zero
  ; c-omega
  ; c-plus
  ; c-psi
  ; C-monotone
  )

open import Ordinal.CNF using
  ( CNF
  ; czero
  ; _∷_
  ; _<ᶜ_
  ; <-zero-cons
  ; <-head
  ; <-tail
  ; <ᶜ-irrefl
  ; <ᶜ-trans
  ; cnf-trichotomy
  )

open import Ordinal.PsiSimple using
  ( psi-notin-C
  ; psi-least
  )

open import Ordinal.Brouwer using
  ( Ord
  ; oz
  ; osuc
  ; olim
  ; _≤_
  ; _<_
  ; ≤-refl
  ; ≤-suc
  ; ≤-lim
  ; ≤-zero
  ; ≤-trans
  ; ≤-osuc
  ; f-in-lim
  ; <-suc-self
  ; <-trans
  ; pred-of-osuc
  ; pred-of-olim
  ; wf-<
  ; <-irrefl
  ; oz<one
  ; one<two
  ; oz<two
  ; one<ω
  )

open import Ordinal.Brouwer.Arithmetic using
  ( _⊕_
  ; nat-to-ord
  ; ω-rank
  ; psi-rank
  ; ⊕-oz-right
  ; ω-rank-fin0
  ; ω-rank-fin1
  )

-- Phase 1.3 (2026-04-28) — recursive `_≤′_` per Echidna SA + swarm
-- recommendation. Bullseye lemma `osuc-mono-≤′ p = p` is identity.
-- Limit case of `≤′-refl` discharged via `≤′-lim` (2026-04-30).
-- WF for the recursive order landed 2026-05-01: `wf-<′` mirrors
-- `wf-<` with predecessor lemmas reducing through computed shapes.
-- Right-monotonicity of `_⊕_` landed (issue #34): `⊕-mono-<-right`
-- and `⊕-mono-≤-right` by induction on γ; helpers `≤′-self-osuc`,
-- `≤′-weaken-osuc`, `⊕-left-≤-sum` also pinned.
open import Ordinal.Brouwer.Phase13 using
  ( _≤′_
  ; _<′_
  ; osuc-mono-≤′
  ; osuc-mono-<′
  ; ≤′-zero
  ; oz<′osuc
  ; ≤′-lim
  ; ≤′-refl
  ; f-in-lim′
  ; ≤′-trans
  ; pred-of-osuc-<′
  ; pred-of-olim-<′
  ; wf-<′
  ; ≤′-self-osuc
  ; ≤′-weaken-osuc
  ; ⊕-left-≤-sum
  ; ⊕-mono-≤-right
  ; ⊕-mono-<-right
  )

-- Recommended rank function for unbudgeted `wf-<ᵇʳᶠ_` per Echidna's
-- design search; transport theorem deferred until Phase 1.3 lemmas land.
open import Ordinal.Buchholz.RankBrouwer using
  ( rank
  )

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
  ; _<Ω_
  ; fin<fin
  ; fin<ω
  ; <Ω-irrefl
  ; <Ω-trans
  ; <Ω→≤Ω
  ; ≤Ω-<Ω-trans
  ; <Ω-≤Ω-trans
  ; ≤Ω-split
  ; Omega0
  ; Omega1
  ; Omegaω
  ; Omega0≤Omega1
  ; Omega0≤Omegaω
  ; Omega1≤Omegaω
  ; Omega0<Omega1
  ; Omega0<Omegaω
  ; Omega1<Omegaω
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

open import Ordinal.Buchholz.OrderExtended using
  ( _<ᵇ⁺_
  ; <ᵇ⁺-base
  ; <ᵇ⁺-ψα
  ; <ᵇ⁺-+2
  ; <ᵇ⁺-irrefl
  ; <ᵇ⁺-trans
  ; <ᵇ⁺-ψα-refl
  ; <ᵇ⁺-+2-refl
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
  ; bzero<Ω0
  ; Ω0<Ω1
  ; Ω1<Ωω
  ; Ω0<ψ1-zero
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

open import Ordinal.Buchholz.Smoke using ()

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

