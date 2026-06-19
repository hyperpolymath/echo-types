{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

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

-- Displayed-type / fibration packaging of the categorical base
-- (EchoDisplayed.agda) — faithful Agda mirror of typed-wasm's Idris
-- Displayed / DispHom / idDispHom / fromHomOver. Pins the packaging
-- (Displayed, DispHom, idDispHom, EchoOf, fromHomOver) and the four
-- laws (identity displayed morphism acts as identity; fromHomOver
-- well-defined = map-over by construction; fromHomOver compatible with
-- map-over-id and map-over-comp). PURELY the fibration packaging — no
-- variance / graded-comonad / universal-property claim (R-2026-05-18).
open import EchoDisplayed using
  ( Displayed
  ; DispHom
  ; dispMap
  ; idDispHom
  ; EchoOf
  ; fromHomOver
  ; idDispHom-acts-id
  ; fromHomOver-action
  ; fromHomOver-id
  ; fromHomOver-comp
  )

-- AntiEcho thin slice (theory/antiecho — Σ-dual of Echo). Lands the
-- carrier, per-element disjointness, introduction, source-side
-- map-over, and per-element partition with decidability of `f x ≡ y`
-- (obligation 5). Distinct from `EchoFiberTriangulation.CoEcho`
-- (which is the trivial opposite-orientation fibre `∃ x . y ≡ f x`);
-- see `coecho.md` §6 for the naming rationale. Tropical decomposition
-- lives in `AntiEchoTropical.agda`; the generic-codomain lift of it
-- remains deferred.
open import AntiEcho using
  ( AntiEcho
  ; antiecho-intro
  ; antiecho-disjoint
  ; antiecho-map-over
  ; antiecho-partition-dec
  ; antiecho-partition-codomain-dec
  )

-- Pillar A of docs/echo-types/establishment-plan.adoc: the
-- definitional Echo ≃ fib bridge, pinned so a rename fails CI fast.
open import EchoFiberBridge using (fiber; echo→fib; fib→echo; echo↔fib)

-- EchoTotalCompletion — the slogan-unlock theorem: A ≃ Σ B (Echo f).
-- "Irreversible computation + echo = reversible representation."
-- Encode/decode + round-trips + factorisation triangle (definitional).
-- Load-bearing lemma for EchoOrthogonalFactorizationSystem and for
-- the optic-complement / image-factorisation framings.
open import EchoTotalCompletion using
  ( encode
  ; decode
  ; decode-encode
  ; encode-decode
  ; A↔ΣEcho
  ; f-factors-via-projection
  ; encode-is-section-of-proj₁
  )

-- EchoNoSectionGeneric — raises the example-level
-- `no-section-collapse-to-residue` to a uniform structural theorem.
-- Generic headline `no-section-of-collapsing-map`: any collapsing
-- map with two distinct elements landing on the same image admits
-- no section. Existing instance recovered as
-- `no-section-collapse-to-residue′`; Echo-specific corollary
-- `no-section-when-non-injective-at-y` is the form the abstraction-
-- barrier / non-injectivity narrative wants.
open import EchoNoSectionGeneric using
  ( no-section-of-collapsing-map
  ; no-section-collapse-to-residue′
  ; trivial-weaken
  ; trivial-weaken-collapses
  ; no-section-when-non-injective-at-y
  )

-- EchoAggregation — the GENERAL aggregation form (issue #175):
-- aggregation-as-fold over a `Monoid`, with a `GroupAggregator` and
-- the monoid-homomorphism law `aggregation-as-fold` (aggregating a
-- concatenation = combining the aggregates). Four concrete instances
-- (`sumMonoid`/`countMonoid`/`maxMonoid`/`minMonoid`), a worked
-- `countAggregator`, and generic non-disaggregability
-- `no-canonical-disaggregation-of` (any collision ⇒ no section, via
-- `no-section-of-collapsing-map`; also covers #174). The MACRO
-- economics reading (micro→macro ledger, SMD critique) is the oikos
-- alib bridge's interpretation of the `Example-PairSum` instance:
-- `pairSum` IS the `sumMonoid` fold (`pairSum-is-fold`), is
-- many-to-one (`pairSum-non-injective`), and has no canonical
-- disaggregation (`no-canonical-disaggregation`).
open import EchoAggregation using
  ( Monoid
  ; GroupAggregator
  ; ⊕-fold
  ; ⊕-fold-++
  ; aggregate-values
  ; aggregation-as-fold
  ; sumMonoid
  ; countMonoid
  ; maxMonoid
  ; minMonoid
  ; countAggregator
  ; no-canonical-disaggregation-of
  )
open EchoAggregation.Example-PairSum using
  ( pairSum
  ; pairSum-is-fold
  ; pairSum-non-injective
  ; no-canonical-disaggregation
  )

-- EchoImageFactorization — image-factorisation triangle in Echo
-- language. `Image f := Σ B (Echo f)` IS the total Echo space.
-- Three classifications (Surjective / Injective / projection-
-- uniqueness under injectivity) pin the function-level
-- characterisations needed for `EchoLossTaxonomy`. Companion to
-- `EchoOrthogonalFactorizationSystem` at the (surj, inj) collapse
-- boundary; the (epi, mono) truncation form remains the next
-- earn-back gate.
open import EchoImageFactorization using
  ( Image
  ; image-factor-left
  ; image-factor-right
  ; image-factor-commutes
  ; Surjective
  ; surjective-iff-every-fibre-inhabited
  ; Injective
  ; injective-fibres-proj-unique
  ; image-membership-is-echo
  )

-- EchoImageFactorizationProp — (epi, mono) image factorisation
-- module-parameterised in a propositional-truncation interface
-- (`TruncInterface`).  Closes the (epi, mono) earn-back gate the
-- base module flagged: takes ∥_∥ as an explicit module parameter
-- (mirroring the funext-as-module-parameter discipline of
-- `EchoOFSUnivF5`), then ships the (-1)-truncated image + its
-- monic right leg + its mere-surjective left leg.  Zero postulates
-- in THIS module; the truncation interface is supplied by the
-- consumer.
open import EchoImageFactorizationProp using
  ( TruncInterface
  ; module ImageProp
  )

-- EchoLossTaxonomy — function-side classification of `f : A → B`
-- by echo shape. Four cases: EQUIV (centre + projection unique),
-- INJ (projection unique, re-export), SURJ (every fibre inhabited,
-- re-export), CONST (fibre at y₀ ↔ A). The EQUIV/CONST cases ship
-- new content (`HasInverse` record, `const-fibre-↔-domain` packaged
-- as `↔`); INJ/SURJ are taxonomy-side renames of the
-- `EchoImageFactorization` headlines. Honest scope: the full
-- "contractible fibre" and "propositional fibre" upgrades need UIP /
-- truncation and are documented as the next earn-back. Companion to
-- `EchoResidueTaxonomy` (next module).
open import EchoLossTaxonomy using
  ( HasInverse
  ; equiv-fibre-center
  ; equiv-implies-injective
  ; equiv-fibre-proj-unique
  ; inj-fibre-proj-unique
  ; surj-fibre-inhabited
  ; const-fun
  ; const-fibre-inhabits-domain
  ; const-fibre-section
  ; const-fibre-projection
  ; const-fibre-section-projects-to-id
  )

-- EchoResidueTaxonomy — residue-side companion to EchoLossTaxonomy.
-- `record ResidueForm f R` packages the minimum unified residue
-- shape (per-output carrier + lowering). Four instances: trivial
-- (⊤), identity (Echo f itself), generic Σ-cert (`echoR-residue`),
-- and the worked `linear-affine-residue` on `collapse : Bool → ⊤`.
-- Other six decoration modules (Graded / Choreo / Access / Cost /
-- Search / Indexed / Epistemic) documented as structurally
-- compatible in the companion-remark; decoration RECIPE
-- (order / order-prop / join / degrade-compose / degrade-via-join)
-- lands in `EchoDecorationStructure` (next module).
open import EchoResidueTaxonomy using
  ( ResidueForm
  ; trivial-residue
  ; identity-residue
  ; echoR-residue
  ; linear-affine-residue
  ; indexed-residue
  ; module CostInstance
  ; search-residue
  ; epistemic-residue
  )

-- EchoDecorationStructure — observation-side companion to
-- EchoResidueTaxonomy. `record DecorationStructure G` packages the
-- seven-field decoration recipe (order, refl, trans, prop, join,
-- join-left, join-right, join-univ) shared across the eight
-- decoration modules. Three instance witnesses (Graded, Linear,
-- Access) pinned; remaining five (Choreo / Cost / Search / Indexed
-- / Epistemic) documented as structurally compatible. Naming:
-- abstract join is `join` (not `_⊔_`) to avoid Level._⊔_ collision
-- at the projection level.
open import EchoDecorationStructure using
  ( DecorationStructure
  ; graded-decoration-structure
  ; linear-decoration-structure
  ; access-decoration-structure
  ; choreo-decoration-structure
  ; module DegradeAbstract
  )

-- EchoObservationalEquivalence — mode-indexed equality on LEcho,
-- closing the Tier-2 spine. `_≡m_` is `_≡_` at linear (witness-
-- aware) and `⊤` at affine (witness-blind). The headline
-- `mode-equality-strictly-finer-at-linear` exhibits a
-- linear-distinct / affine-equal pair, pinning the strictly-finer
-- direction as a checked theorem.
open import EchoObservationalEquivalence using
  ( _≡m_
  ; ≡m-refl
  ; ≡m-sym
  ; linear-distinguishes-true-false
  ; affine-collapses
  ; weaken-preserves-≡m
  ; mode-equality-strictly-finer-at-linear
  )

-- EchoOrthogonalFactorizationSystem — the architectural keystone.
-- Every f : A → B factors canonically as A ≃ Σ B (Echo f) → B with
-- the left leg an equivalence (totality completion) and the right
-- leg a projection whose fibre at y is exactly Echo f y. Honest
-- scope: factorisation existence + fibre identification land here
-- under --safe --without-K; the full OFS lifting/uniqueness clause
-- requires funext and is documented as the next earn-back gate (in
-- the EchoPullbackUnivF4 / Pillar F4 style).
open import EchoOrthogonalFactorizationSystem using
  ( echo-factorisation
  ; left-leg-equivalence
  ; fibre-of-proj₁-to
  ; fibre-of-proj₁-from
  ; fibre-of-proj₁-to-from
  ; fibre-of-proj₁-from-to
  ; fibre-of-proj₁-iso
  ; projection-fibre-iso
  ; ofs-witness
  )

-- Foundation P1 (docs/foundation.adoc): external-fibre
-- triangulation against the standard library's OWN notions —
-- removes the same-module self-reference R-2026-05-18 flagged.
-- `echo↔coecho` is the genuine (non-refl, sym-carrying) coherence;
-- the T1/T3 pins are calibration coincidences with stdlib, owned as
-- such. Pinned so a rename or a slide to an unanchored claim trips CI.
open import EchoFiberTriangulation using
  ( echo-is-stdlib-witness                      -- T1 calibration
  ; all-echo→stdlib-strictly-surjective
  ; stdlib-strictly-surjective→all-echo
  ; echo↔coecho                                 -- T2 genuine content
  ; all-echo→stdlib-surjection                  -- T3 surjection tie
  )

open import EchoCharacteristic using (collapse; echo-true; echo-false; echo-true≢echo-false)
open import EchoResidue using (EchoR; collapse-to-residue; strict-weakening-collapse; no-section-collapse-to-residue)
open import EchoExamples using (square9; visible; quot; collapse-residue-identifies)

-- Example 9 (docs/echo-types/examples.md §9): parser residue —
-- balanced parentheses. The Boolean shadow `parses : List Token →
-- Bool` is non-injective on distinct presentations (`(())` vs `()()`),
-- and the Echo retains the token stream. Pinned headlines: the
-- non-injectivity Σ-witness, the three concrete `Echo parses true`
-- carriers (empty / pair / nested), and the residue Σ-pair.
open import EchoExampleParser using
  ( Token
  ; LP
  ; RP
  ; parses
  ; echo-parse-empty
  ; echo-parse-pair
  ; echo-parse-nested
  ; echo-parse-nested≢echo-parse-pair
  ; parses-non-injective
  ; parser-residue
  ; BalancedClosed
  ; empty-balanced
  ; paren-empty-balanced
  ; paren-nested-balanced
  ; paren-pair-balanced
  )

-- Example 10 from `docs/echo-types/examples.md` (abstract
-- interpretation via Sign lattice). Headlines pinned so a rename
-- or a slide back to an unanchored claim fails CI fast. See
-- PR #76 (presentation-dependence cluster).
open import EchoExampleAbsInt using
  ( Sign
  ; Carrier
  ; α
  ; concretization-collapses
  ; α-non-injective-on-pos
  ; echo-pos-p1
  ; echo-pos-p2
  ; echo-zero-witness
  ; distinct-echoes-same-sign
  ; absint-classification
  )

-- Example 5 (docs/echo-types/examples.md §5): database provenance via
-- K-provenance semiring. Distinct Bool-provenance rows project to the
-- same payload, witnessing the non-injectivity of `project` and
-- producing distinct echoes at the same projected value.
open import EchoExampleProvenance using
  ( Row
  ; project
  ; provenance-collapses
  ; echo-prov-true
  ; echo-prov-false
  ; echoes-distinguish-provenance
  ; echo-prov-true≢echo-prov-false
  ; collapse-via-residue
  )
open import VecRotation using (rotL-alternating; rotR-alternating; map-alternating)

open import EchoApprox using
  ( Tolerance
  ; PseudoMetric
  ; BalancedTolerance
  ; module Approx
  )

-- Per-lemma pins for the parameterised EchoApprox via EchoApproxInstance
-- (hygiene; closes the CLAUDE.md "Working rules" invariant gap for
-- parameterised modules — see follow-up to PR #70).
open import EchoApproxInstance using
  ( trivialTolerance
  ; trivialPseudoMetric
  ; trivialBalancedTolerance
  ; approx-EchoR
  ; approx-intro
  ; approx-strict→approx
  ; approx-relax
  ; approx-NonExpansive
  ; approx-compose
  ; approx-comp-sound
  ; approx-comp-retract-to
  ; approx-comp-retract-A
  ; approx-comp-retract-B
  ; approx-comp-retract-budget
  ; approx-comp-retract-from-to
  ; approx-subst-A-invariant
  ; approx-Separated
  ; approx-zero-collapses-strict
  ; approx-shadow-A
  ; approx-shadow-iso-to
  ; approx-shadow-iso-from
  ; approx-strict→approx-shadow-A
  ; approx-strict→approx-collapse-shadow-A
  )

-- Axis 8 third quantitative artifact (taxonomy.md §8, refinement 1):
-- cost-indexed echo over an abstract `CostAlgebra` (ordered commutative
-- monoid with `0`, `+`, `≤`, left-identity, transitivity, monotone-`+`).
-- Sits orthogonal to `EchoDecidable` (refinement 3, qualitative
-- decidability) and `EchoFiberCount` (quantitative fibre-count for
-- finite domains): names the resource-budget dimension of Axis 8.
-- Carrier + headlines pinned via `EchoCostInstance` (trivial-on-⊤
-- instance) — same hygiene pattern as `EchoApproxInstance`.
open import EchoCost using
  ( CostAlgebra
  ; module Cost
  )

open import EchoCostInstance using
  ( trivialCostAlgebra
  ; cost-EchoC
  ; cost-intro
  ; cost-intro-≤
  ; cost-relax
  ; cost-relax-zero
  ; cost-forget
  ; cost-compose
  ; cost-compose-mono
  ; cost-forget-compose-mono-A
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

-- Axis 8(4) thin slice (taxonomy.md §"Witness-search abstract
-- machine"): the enumerator-bounded refinement of `Echo`. Lands the
-- search strategy + bound-indexed carrier, introduction, bound
-- monotonicity, forgetful projection to plain `Echo`, empty-budget
-- vacuity, and the honest post-composition rule. Sequential /
-- product-strategy composition needs a `ℕ × ℕ ↔ ℕ` pairing
-- bijection and lands in a separate slice; see the module preamble
-- "where next" section.
open import EchoSearch using
  ( SearchStrategy
  ; EchoS
  ; echo-search-intro
  ; echo-search-relax
  ; echo-search-forget
  ; echo-search-bound-zero
  ; echo-search-postcompose
  )

-- Per-lemma pins for the parameterised EchoSearch via
-- EchoSearchInstance — same hygiene pattern as EchoApproxInstance.
open import EchoSearchInstance using
  ( trivialEnum
  ; trivialF
  ; search-intro-⊤
  ; search-relax-⊤
  ; search-forget-⊤
  ; search-bound-zero-⊤
  ; search-postcompose-⊤
  )

-- Axis 8 second formal artifact (taxonomy.md §8): graded access
-- modality. Order layer (enum, Hasse-enumerated order, transitivity,
-- propositionality) + Σ-shape carrier + `_≤a_`-indexed degrade
-- primitive landed in the thin slice; the per-decoration composition
-- trio (`degrade-access-comp` / `compose` / `via-join`) and the
-- categorical join structure (`_⊔a_` + `≤a-⊔a-{left,right,univ}`)
-- land in this PR, completing the same recipe as `EchoGraded` and
-- `EchoLinear`. Honest carriers for `enum` / `feasible` / `infeasible`
-- remain deferred (a real design choice — see the module preamble).
open import EchoAccess using
  ( Access
  ; free
  ; decidable
  ; enum
  ; feasible
  ; infeasible
  ; _≤a_
  ; ≤a-trans
  ; ≤a-prop
  ; CEcho
  ; EchoAccess
  ; access-of
  ; degrade-access
  ; _⊔a_
  ; ≤a-⊔a-left
  ; ≤a-⊔a-right
  ; ≤a-⊔a-univ
  ; degrade-access-comp
  ; degrade-access-compose
  ; degrade-access-via-join
  )

open import EchoFiberCount using
  ( FiberSize-fin
  ; FiberSize-fin-no-hit
  ; FiberSize-fin-all-hit
  ; FiberSize-fin-id-zero
  ; FiberSize-fin-injective
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
  ; bennett-reversible-injective
  ; landauer-collapse
  )

-- EchoEntropy — discrete Shannon-entropy non-distinguishing theorem.
-- Companion to EchoAbstractionBarrier: the entropic shadow (fibre
-- count = 2 bit on collapse@tt) agrees on echo-true vs echo-false,
-- so any consumer factoring through it cannot distinguish them.
-- Matched-negative via `sigma-distinguishes` (witness side does).
-- Closes the "Shannon-entropy formalisations not yet present" item
-- flagged in EchoThermodynamics + EchoStabilityTests.
open import EchoEntropy using
  ( collapse-as-fin
  ; collapse-fibre-count
  ; entropy-shadow
  ; shannon-shadow
  ; entropy-shadow-equal
  ; shannon-shadow-equal
  ; entropy-shadow-blind
  ; shannon-shadow-blind
  ; witness-distinguishes-where-entropy-cannot
  )

open import EchoThermodynamicsFinite using
  ( FiniteDomain
  ; fiber-erasure-bound-fin
  ; bennett-reversible-finite
  ; landauer-collapse-finite
  )

open import EchoThermodynamicsArbitrary using
  ( FiberSubsingleton
  ; injective⇒fiber-subsingleton
  ; reversible-erasure-cost
  ; bennett-reversible-arbitrary
  ; occupancy≡FiberSize-fin
  ; bennett-arbitrary-refines-finite
  ; bennett-reversible-cno-identity
  )

open import EchoThermoCollapseImpossible using
  ( nat-into-collapse-fiber
  ; nat-into-collapse-fiber-injective
  ; collapse-cost-impossible
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

-- EchoAbstractionBarrier — Track B of the Echo-vs-Σ identity claim.
-- Consumer-side free theorem at the affine instance + raw-Σ
-- counter-program. See `roadmap.adoc` §Lane 2 and
-- `core/skepticisms/is-this-just-sigma-types.md` §4.
open import EchoAbstractionBarrier using
  ( affine-consumer-cannot-distinguish
  ; sigma-distinguishes
  )

-- EchoLLEncoding — linear-logic shallow-encoding gap. Companion to
-- EchoAbstractionBarrier: no standard LL `!A`-style shadow encoding
-- preserves Echo's `no-section-weaken` property, because the
-- distinguishing data lives in the witness LL discards. The trivial
-- ⊤-shadow is the canonical LL `!A := 1` model and admits a section
-- of the encoded weakening; the source side does not. Closes the
-- LL-encoding-gap follow-up to the abstraction-barrier audit.
open import EchoLLEncoding using
  ( LLShallowEncoding
  ; trivial-encoding
  ; trivial-encoding-has-section
  ; ll-encoding-gap
  ; source-no-section
  ; gap-paired
  )

-- examples.EchoVsSigma — Track C of the Echo-vs-Σ identity claim.
-- Per-example raw-Σ counter-programs paired with each headline
-- example (parser, provenance, absint) — the matched-negative
-- companions for Gate 3. See `roadmap.adoc` §Lane 2 close-out
-- item 2.
open import examples.EchoVsSigma using
  ( parser-sigma-distinguishes
  ; provenance-sigma-distinguishes
  ; absint-sigma-distinguishes
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

-- Pillar B of docs/echo-types/establishment-plan.adoc: echo's
-- loss-graded *reindexing modality* (NOT a graded comonad — no
-- nested D_r D_s; gextract is the identity coercion, gduplicate the
-- join-left single-grade reindex). The coherence equations collapse
-- to ≤g-prop because the grade order is thin, not because a comonad
-- coherence was discharged. See docs/retractions.adoc R-2026-05-18.
open import EchoGradedComonad using
  ( gextract
  ; gduplicate
  ; gcomonad-counit-l
  ; gcomonad-counit-r
  ; gcomonad-coassoc
  )

-- Pillar B (part 1): Echo as the pullback of f along y : ⊤ → B,
-- with a funext-relative *pointwise* mediator property (NOT a
-- terminal-cone universal property: m' ≡ m is unstatable here
-- without funext). SliceHom IS a cone. See R-2026-05-18.
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
-- the characteristic loss-grade composition law fails. This
-- *quantifies* the modality's content over generic Σ: it is exactly
-- thinness of the loss order (≤g-prop), and no more.
open import EchoSeparating using
  ( _⊑_
  ; deg
  ; sep-order-not-prop
  ; sep-map-over-id
  ; sep-map-over-comp
  ; SepDegradeCompose
  ; sep-degrade-compose-fails
  )

-- Pillar D: carrier-parametricity (NOT model-independence). The
-- coherence equations proved once for any GradedLossModel, but the
-- interface's ⊑-prop field bakes in the only load-bearing
-- hypothesis and both instances fix the same grade poset; rel-model
-- is set-model × ⊤, agreeing by refl. See R-2026-05-18.
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

-- Pillar F, Gate F4 (docs/echo-types/earn-back-plan.adoc; retraction
-- follow-up F-2026-05-18a). The terminal-cone universal property,
-- earned back as TRUE CONDITIONAL ON an explicit `funext` parameter
-- (never a postulate). The unconditional pointwise mediator property
-- is kept as the funext-free corollary. Names pinned so a rename or
-- a slide back to an *unconditional* claim fails CI fast.
open import EchoPullbackUnivF4 using
  ( FunExt₀
  ; echo-pullback-univ-strict     -- m' ≡ m, GIVEN funext (no postulate)
  ; echo-pullback-univ-pointwise  -- ∀ v → m' v ≡ m v, funext-free
  )

-- Pillar F, Gate F5 first slice (docs/echo-types/earn-back-plan.adoc).
-- Same shape as F4: the function-level factorisation triangle
-- `f ≡ proj₁ ∘ encode f` is TRUE CONDITIONAL ON an explicit `funext`
-- parameter; the unconditional pointwise corollary (the existing
-- `echo-factorisation`) is kept as the funext-free form. Slice F5-1
-- only; F5-2 (diagonal lifting) and F5-3 (factorisation uniqueness up
-- to iso) remain open per the ledger. F5-1 partial-pass status.
open import EchoOFSUnivF5 using
  ( echo-factorisation-strict     -- f ≡ proj₁ ∘ encode f, GIVEN funext
  ; echo-factorisation-pointwise  -- ∀ x → f x ≡ proj₁ (encode f x)
  )

-- Pillar F, Gate F5 second slice. Same template: pointwise (K-free)
-- diagonal lift + funext-strict diagonal lift. Construction:
-- `lift x = h (e⁻¹ x)` where `e⁻¹` is the inverse from `HasInverse e`.
-- Both triangles (lift ∘ e ≡ h, proj₁ ∘ lift ≡ k) commute pointwise
-- K-free; strict forms lifted via funext. Uniqueness K-free pointwise;
-- strict via funext. F5-2 partial-pass; F5-3 (factorisation uniqueness
-- up to iso) remains the final open slice for full F5 pass.
open import EchoOFSUnivF5Diag using
  ( module Pointwise
  ; module Strict
  )

-- Pillar F, Gate F5 third slice — F5 FULL PASS.
-- Factorisation uniqueness up to iso. Given any second (eq, proj)
-- factorisation `f = p ∘ g` with `g : A → X` an equivalence (via
-- `HasInverse`), construct the canonical iso `φ : X ↔ Σ B (Echo f)`
-- with `φ.to ∘ g ≡ encode f` and `proj₁ ∘ φ.to ≡ p` (both strict
-- given funext). Design: composition `φ.to = encode f ∘ g⁻¹`
-- routes path-algebra through existing K-free `encode-decode` /
-- `decode-encode` round-trips, avoiding the triangle-identity
-- obligation the direct formulation would need. F5 fully passes
-- with all three slices: F5-1 + F5-2 + F5-3, all funext-qualified,
-- zero postulates. Module names disambiguate the F5-2 / F5-3
-- `module Pointwise` / `module Strict` via qualified open.
open import EchoOFSUnivF5Iso as F5Iso using ()
open F5Iso.Pointwise using
  ( φ-to
  ; φ-from
  ; φ-from-to
  ; φ-to-from
  ; φ-iso
  ; φ-respects-g
  ; φ-projects-to-p
  )

-- EchoProvenance — audience-facing abstract provenance theorem
-- (Tier 3 first audience move, per GPT-recommended order).
-- Generalises EchoExampleProvenance from Bool-over-ℕ to any
-- `Provenance` setup (payload + tag + distinguishability witness).
-- Four headline theorems parametric in `P : Provenance`:
-- non-injectivity at every payload, concrete Echo carriers per
-- tag, carriers distinguish tags, residue collapses tags. The
-- `bool-over-nat-provenance` instance witnesses inhabitability.
open import EchoProvenance using
  ( Provenance
  ; module ProvenanceTheorems
  ; bool-over-nat-provenance
  )

-- EchoSecurity — second audience move per GPT order. Abstract
-- `Security` record (resource + receipt + region indexing + exit
-- + distinguishability + collapse witness); two parametric
-- headline theorems via `module SecurityTheorems (S : Security)`:
-- per-region collapse, per-region audit-no-recovery (factored
-- through `EchoNoSectionGeneric.no-section-of-collapsing-map`).
-- Worked `region-exit-audit-instance` reproduces the existing
-- RegionExitAudit walkthrough's structure. Honest-bound matched
-- negatives at the bottom of the file (bytes-zeroed,
-- side-channel-safe, tamper-evident, oracle-recovery).
open import EchoSecurity using
  ( Security
  ; module SecurityTheorems
  ; TwoRegion
  ; region-exit-audit-instance
  )

-- EchoProbabilisticSupport — third audience move per GPT order.
-- Abstract `Sampling` record (outcome + index + distinguishability
-- witness) with four parametric headline theorems via `module
-- SamplingTheorems (S : Sampling)`: marginal non-injectivity,
-- concrete Echo carriers per index, carriers distinguish indices,
-- residue loses index. Worked `bool-indexed-nat-sampling` instance.
-- Honest-bound matched-negatives: not measure-preserving, not a
-- probability monad, no Kantorovich / coupling / randomness
-- extraction.
open import EchoProbabilisticSupport using
  ( Sampling
  ; module SamplingTheorems
  ; bool-indexed-nat-sampling
  )

-- EchoDifferential — fourth audience move per GPT order. Abstract
-- `Sensitivity` record (value + perturbation + distinguishability
-- witness) with four parametric headline theorems via `module
-- SensitivityTheorems (S : Sensitivity)`: blur non-injectivity,
-- concrete Echo carriers per perturbation, carriers distinguish
-- perturbations, residue loses perturbation. Worked
-- `bool-perturbed-nat-sensitivity` instance. Honest-bound
-- matched-negatives: not ε-DP, no Lipschitz bound, no noise
-- calibration, no adversary model.
open import EchoDifferential using
  ( Sensitivity
  ; module SensitivityTheorems
  ; bool-perturbed-nat-sensitivity
  )

-- EchoDeniability — residue deniability as a first-class echo property
-- (2026-06-13). Two production functions at opposite ends of the
-- deniability spectrum: produce-perfect (constant → fully deniable,
-- no section) and produce-partial (injective → not deniable for
-- arbitrary openers, has section). IsConstantOpener is the exact
-- cut-point at which deniability is restored for the partial case;
-- it is the type-level analogue of the `affine` mode in
-- EchoObservationalEquivalence. no-section-produce-perfect / partial-
-- has-section make the duality a checked theorem pair.
open import EchoDeniability using
  ( History
  ; Residue
  ; Trace
  ; Erased
  ; produce-perfect
  ; produce-partial
  ; IsDeniable
  ; IsConstantOpener
  ; perfect-deniable
  ; partial-witness
  ; partial-distinguishable
  ; partial-not-deniable
  ; partial-deniable-restricted
  ; no-section-produce-perfect
  ; partial-has-section
  ; echo-intact-perfect
  ; echo-lost-perfect
  ; echo-intact-lost-distinct
  ; NotProved-side-channel-safe
  ; NotProved-cryptographic-deniability
  ; NotProved-adaptive-adversary
  )

-- EchoCanonicalIdentitySuite — the curated entry point for "why
-- Echo deserves a name". Re-exports the load-bearing headlines
-- from every Tier-1 / Tier-2 / Tier-3 module in a single readable
-- file. Demonstrating the suite typechecks under --safe --without-K
-- is the load-bearing CI check; a rename in any source module
-- that breaks the suite's re-export trips CI fast.
open import EchoCanonicalIdentitySuite using ()

-- Pillar F, Gate F2 (same plan / follow-up). A genuine second model
-- of the *bare* Echo functor on the non-deterministic, non-graph
-- relation `StepND`: same interface as the deterministic model,
-- functor laws hold, agreement has content (constructor case
-- analysis, not refl / not Σ-η on × ⊤), and `nd-not-graph` is the
-- checked proof it is NOT a disguised graph. Scope: the Echo
-- functor, NOT the graded comonad / model-independence (still
-- retracted, R-2026-05-18).
open import EchoStepNDModelF2 using
  ( EchoFunctorModel
  ; det-model
  ; nd-model
  ; nd-not-graph                  -- StepND is no function's graph
  ; det→nd                        -- content-bearing witness preservation
  ; nd-sum-fromto                 -- nd fibre = sum of det branches
  ; nd-fibre-not-prop             -- the fibre is not a proposition
  )

-- Pillar F, Gate F1 — the MAKE-OR-BREAK gate (docs/echo-types/
-- earn-back-plan.adoc §F1). A genuine graded comonad on the
-- iterated-residue carrier `D r A = r nested R-layers`, with grade
-- monoid (ℕ, +, 0), Echo as the grade-unit object (D 0 (Echo f y) is
-- the bare echo), NESTED comultiplication δ : D (m+n) ⇒ D m ∘ D n,
-- all three graded-comonad laws proved, and a separating witness
-- showing D 2 is not collapsing to ⊤. --safe --without-K, zero
-- postulates, no funext. Scope: this earns back the graded-comonad
-- claim FOR THIS WITNESS ONLY; `EchoGraded` itself remains a
-- thin-poset reindexing modality per R-2026-05-18.
open import EchoGradedComonadF1 using
  ( D                              -- the graded functor
  ; mapD ; mapD-id ; mapD-∘        -- functor laws
  ; ε                              -- counit at the unit grade
  ; δ                              -- NESTED comultiplication
  ; D2-nontrivial                  -- D 2 is not ⊤ / a prop
  ; gc-counit-r                    -- counit-right law (definitional)
  ; gc-counit-l                    -- counit-left law
  ; gc-coassoc                     -- coassociativity law (the F1 keystone)
  )

-- Pillar F, Gate F3 — PASSED (docs/echo-types/earn-back-plan.adoc §F3).
-- The abstract `GradedComonadStructure` record (grade monoid + graded
-- functor + counit + nested comultiplication + monoid laws + functor
-- laws + comonad laws, with NO ⊑-prop-equivalent field) plus TWO
-- non-isomorphic-grade-monoid instances:
--   * `nat-instance`  at the COMMUTATIVE  monoid (ℕ, +, 0)
--   * `list-instance` at the NON-COMMUTATIVE monoid (List Tag, ++, [])
-- The non-isomorphism is witnessed by `tag-list-non-commutative`
-- (one direction: only a non-commutative monoid satisfies it).
open import EchoGradedComonadInterface using
  ( GradedComonadStructure          -- the abstract record
  )
open import EchoGradedComonadInstance1 using
  ( nat-instance                    -- F1 packaged as record-inhabitant at (ℕ, +, 0)
  )
open import EchoGradedComonadInstance2 using
  ( Tag                             -- two-element grade index
  ; tag-list-non-commutative        -- monoid non-isomorphism witness
  ; D-nontrivial                    -- D (smol ∷ big ∷ []) is non-trivial
  ; list-instance                   -- the second graded-comonad instance
  )

-- Variance verdict (docs/echo-types/variance-resolution.adoc): the
-- monad / comonad / adjunction status of loss accumulation, resolved in
-- --safe Agda rather than asserted. Accumulation is the graded-MONAD
-- multiplication (total + canonical); recoverability is exact on the
-- grade-0 fibre (the section/retraction adjunction); the graded-COMONAD
-- direction fails for genuine loss (no bare-residue recovery); the
-- "graded comonad" reading (F1) is the LOSSLESS complement-storing writer
-- (δ invertible). Pinned so a slide back to an unqualified "graded
-- comonad of loss" claim fails CI fast.
open import EchoVariance using
  ( accumulate                       -- μ : D_r (D_s A) → D_{r+s} A — accumulation is monadic
  ; split-with-factoring             -- δ given the factoring (its inverse)
  ; accumulate-split-id              -- exact on the fibre (round-trip refl)
  ; split-accumulate-id              -- exact on the fibre (round-trip refl)
  ; recoverable-fibre                -- A ↔ Σ B (Echo f): the grade-0 section/retraction adjunction
  ; no-bare-recovery                 -- the comonad obstruction: collapse has no section
  ; fibre-retains-lost-bit           -- the lost bit lives on the fibre, not as a complement
  ; μ-writer                         -- F1 writer's accumulation (inverse of δ)
  ; writer-μ-section                 -- writer δ is invertible ⇒ LOSSLESS (complement-storing)
  ; writer-δ-section                 -- … both round-trips
  )

open import EchoTropical using
  ( Candidate
  ; score
  ; tropical-non-injective
  ; IsArgmin
  ; TropEcho
  ; distinct-candidates-same-visible-distinct-echo
  )

-- AntiEcho × EchoTropical (theory/antiecho-tropical-decompose):
-- the headline "Echo × Π-bound" decomposition of TropEcho /
-- IsArgmin from `coecho.md` §3 / §5 obligation 6. Both
-- round-trips are `refl` once IsArgmin's Σ-shape is unfolded;
-- the AntiEcho-flavoured corollary expresses the Π-bound as
-- Π of negative data over the candidate set (Π-form AntiEcho,
-- `coecho.md` §1(c)). Pinned so a rename or a slide back to
-- ad-hoc tropical decoration fails CI fast.
open import AntiEchoTropical using
  ( antiecho-tropical-decompose-to
  ; antiecho-tropical-decompose-from
  ; antiecho-tropical-decompose-to-from
  ; antiecho-tropical-decompose-from-to
  ; antiecho-tropical-decompose
  ; isargmin-decompose-to
  ; isargmin-decompose-from
  ; isargmin-decompose
  ; ≤⇒¬<
  ; ¬<⇒≤
  ; optimality-as-antiecho-flavour-to
  ; optimality-as-antiecho-flavour-from
  ; tropdecomp-antiecho-to
  ; tropdecomp-antiecho-from
  )

-- Generic-codomain lift of the tropical decomposition. Same headline
-- theorems as `AntiEchoTropical` above, but parameterised by an
-- abstract `OrderedCodomain` interface (carrier B, ≤/<, ≤⇒¬<, ¬<⇒≤)
-- rather than fixed to ℕ. Sanity instance `ℕ-ordered-codomain`
-- pinned so the interface is demonstrably inhabitable.
open import AntiEchoTropicalGeneric using
  ( OrderedCodomain
  ; ℕ-ordered-codomain
  ; module Generic
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

-- Lane 3 (2026-05-20): structural mirror of januskey's canonical
-- Idris2 OpKind ABI (hyperpolymath/januskey:src/abi/Types.idr).
-- Eight-variant OpKind + IsFileOp / IsKeyOp partition predicates,
-- one *-echo per constructor. Theorems remain trivial (each is
-- `λ e → e`); no content-bridge claim, pending
-- januskey/PROOF-NEEDS.md.
open import EchoJanusBridge using
  ( OpKind
  ; IsFileOp
  ; IsKeyOp
  ; copy-echo
  ; move-echo
  ; delete-echo
  ; modify-echo
  ; obliterate-echo
  ; keygen-echo
  ; keyrotate-echo
  ; keyrevoke-echo
  )

-- Cross-repo bridges (NARROW): ephapax `formal/Echo.v` is a Coq port
-- of `EchoLinear.agda` + `EchoResidue.agda` under a K-free / zero-axiom
-- discipline.  `ephapax-L3-weaken` and `ephapax-L3-no-section-collapse`
-- are definitional `refl`-renames of the load-bearing Agda symbols,
-- pinned so a silent upstream rename trips CI fast.  See
-- `EchoEphapaxBridge.agda` preamble.
open import EchoEphapaxBridge using
  ( ephapax-L3-weaken
  ; ephapax-L3-no-section-collapse
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
  ; ⊕-mono-≤-left
  ; ⊕-assoc-≤
  ; ⊕-assoc-≥
  )

-- ω-power infrastructure for path-1 of the Buchholz rank-monotonicity
-- unblock (docs/echo-types/buchholz-rank-obstruction.adoc).  Limit-
-- shaped replacement for `nat-to-ord (suc n)` successor stacks.
open import Ordinal.Brouwer.OmegaPow using
  ( _·ℕ_
  ; ω^_
  ; ω^0≡one
  ; ·ℕ-zero
  ; ·ℕ-suc
  ; one·ℕ≡nat-to-ord
  ; ω^_-pos
  ; X≤′oz⊕X
  ; ω^-strict-mono-suc
  ; ω^-step
  ; ·ℕ-mono-≤-left
  ; ω^-from-zero
  ; ω^-mono-≤-suc-suc
  ; ω^-mono-≤
  ; ω^-strict-mono
  ; ·ℕ-add-≤
  ; additive-principal
  )

-- Ordinal exponentiation + ε₀ (2026-06-15, own block per CLAUDE.md
-- Working rules): rung 1 of the target-side Brouwer climb toward
-- ψ₀(Ω_ω) (BH order-type fidelity, D-2026-06-14).  `ω^^_` is ω to an
-- ORDINAL power (generalising OmegaPow.ω^_ : ℕ → Ord); `ε₀` is the
-- first ε-number.  Honest scope: ε₀ ≪ ψ₀(Ω_ω) — this lands the
-- exponentiation primitive every higher rung needs and pins ε₀ as the
-- first checkable milestone value.
open import Ordinal.Brouwer.OrdinalExp using
  ( ω^^_
  ; ω^^-zero
  ; ω^^-pos
  ; ε-tower
  ; ε-tower-suc
  ; ε₀
  ; ε₀-pos
  ; ε-tower-below-ε₀
  ; ω^^-ε₀-≤
  ; ε₀-≤-ω^^-ε₀
  ; ε₀-ε-number
  ; ω^^-infl
  )

-- Veblen φ-hierarchy slice 2 (2026-06-18, own block per CLAUDE.md
-- Working rules): φ₁, the enumeration of ε-numbers (fixed points of
-- ω^^), built on the rung-3.1 inflationary law.  `next-ε β` = least
-- ε-number above β; `φ₁` enumerates them (0↦ε₀, suc↦next-ε, limit↦sup);
-- `φ₁-ε-number` proves every value is an ε-number (bi-≤′).  Rung 3 of the
-- climb toward Γ₀ / ψ₀(Ω_ω) (order-type fidelity OPEN, D-2026-06-14).
open import Ordinal.Brouwer.VeblenPhi using
  ( tower-from
  ; next-ε
  ; ω^^-next-ε-≤
  ; next-ε-≤-ω^^
  ; β<next-ε
  ; φ₁
  ; φ₁-ε-number
  )

-- Recommended rank function for unbudgeted `wf-<ᵇʳᶠ_` per Echidna's
-- design search; transport theorem deferred until Phase 1.3 lemmas land.
open import Ordinal.Buchholz.RankBrouwer using
  ( rank
  )

-- Brouwer-arithmetic CHECKED REFUTATIONS (2026-05-28).  Promote
-- the two prose obstacles from `RankLexSlice3`'s design note and
-- `Phase13`'s `⊕-mono-≤-left` block comment into named theorems:
--
-- (b) strict-left-mono of `_⊕_` is NOT a theorem
--     (`strict-left-mono-refuted`).  Counterexample at α = oz,
--     β = osuc oz, γ = ω: both sides equal ω, so the strict step
--     fails.  Refutation derives ⊥ from the hypothesis + `<′-irrefl`
--     (also exposed here for downstream use).
--
-- (a) "additive-principal closure on generic sums" is NOT a theorem
--     (`additive-principal-generic-sum-refuted`).  Counterexample
--     at X = Y = α = β = ω: `ω ⊕ ω <′ ω ⊕ ω` would follow,
--     refuted by `<′-irrefl`.
--
-- These pin the two routes documented as "structurally blocked"
-- in `Ordinal.Buchholz.RankLexSlice3` as CHECKED dead-ends
-- rather than prose claims.
open import Ordinal.Brouwer.StrictLeftMonoRefuted using
  ( StrictLeftMonoSum
  ; <′-irrefl
  ; osuc-oz-⊕-ω≤oz-⊕-ω
  ; strict-left-mono-refuted
  )

open import Ordinal.Brouwer.AdditivePrincipalGenericRefuted using
  ( AdditivePrincipalGenericSum
  ; ω<′ω⊕ω
  ; additive-principal-generic-sum-refuted
  )

-- ω-power rank for Ω-markers and Buchholz terms.  Limit-shaped
-- replacement for `nat-to-ord (suc n)` successor stacks.  Compositional
-- rank-mono primitives (right-mono on `bplus`) reusable across both
-- `_<ᵇ⁻_` (this track) and `_<ᵇʳᶠ_` (parallel session).
open import Ordinal.Buchholz.RankPow using
  ( ω-rank-pow
  ; ω-rank-pow-fin
  ; ω-rank-pow-pos
  ; ω-rank-pow-mono
  ; rank-pow
  ; rank-pow-bplus
  ; rank-pow-bOmega
  ; rank-pow-bplus-right-mono
  ; rank-pow-bplus-left-≤
  ; rank-pow-via-left
  ; additive-principal-ω-rank-pow
  ; rank-pow-bplus-into-ω-rank-pow
  ; rank-mono-<ᵇ-0-Ω
  ; rank-mono-<ᵇ-0-ψ
  ; rank-mono-<ᵇ-ΩΩ
  ; rank-mono-<ᵇ-Ωψ
  ; rank-mono-<ᵇ-ψΩ
  ; rank-mono-<ᵇ-Ω+
  ; rank-mono-<ᵇ-ψ+
  ; rank-mono-<ᵇ-+Ω
  ; rank-mono-<ᵇ-+ψ
  ; rank-mono-<ᵇ-+1-via-target
  ; rank-mono-<ᵇ-+1-Ω-target
  ; rank-mono-<ᵇ-+1-ψ-target
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

-- Foundation contract surface (FOUNDATION_CONTRACT.md). The curated,
-- stable `Echo.*` public interface: echo index (thin poset), the Echo
-- modality core (measure-independent), the anti-collapse separation
-- (Echo IS-NOT a resource instance), and the residue-measure seam.
-- Pinned so a silent rename of any contract name fails CI fast.

open import Echo.Index.ThinPoset using
  ( ThinPoset
  ; grade-thinPoset
  ; ≤g-refl
  )

open import Echo.Modality.Interface using
  ( EchoModality
  )

open import Echo.Modality.Core using
  ( Echo
  ; GEcho
  ; degrade
  ; degrade-id
  ; degrade-compose
  ; no-section-of-collapsing-map
  ; grade-echoModality
  )

open import Echo.Separation.NotResourceInstance using
  ( echo-degrade-not-generic-sigma
  ; residue-measure
  ; measure-agrees
  ; echo-distinguishes
  ; equal-measure-does-not-imply-equal-echo
  ; measure-not-injective
  ; visible-measure
  ; visible-measure-informative
  ; equal-informative-measure-does-not-imply-equal-echo
  )

open import Echo.Measure.Interface using
  ( OrderedCarrier
  ; ResidueMeasure
  )

open import Echo.Measure.Examples using
  ( cost-measure
  ; tropical-cost-measure
  ; confidence-measure
  )

