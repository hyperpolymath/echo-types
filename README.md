# echo-types

Constructive Agda development for echo types as a first-class notion of structured loss:

loss that is not total erasure.

## Core Idea

Most formalisms foreground two clean cases:

- reversible / injective / linear-ish: no important loss
- ordinary irreversible: loss occurs and is usually forgotten

Echo types target a third case:

- irreversible, but with a retained proof-relevant constraint on what was lost

This repository treats that third case as the primary object of study.

## Definition (Foundation)

Given `f : A → B`, define the fiber/echo at `y : B`:

`Echo f y := Σ (x : A) , (f x ≡ y)`

Current formal foundation is in:

- `proofs/agda/Echo.agda`
- `proofs/agda/EchoCharacteristic.agda`
- `proofs/agda/EchoResidue.agda`
- `proofs/agda/EchoExamples.agda`
- `proofs/agda/EchoChoreo.agda`
- `proofs/agda/EchoEpistemic.agda`
- `proofs/agda/EchoLinear.agda`
- `proofs/agda/EchoGraded.agda`
- `proofs/agda/EchoTropical.agda`
- `proofs/agda/EchoIntegration.agda`

with constructive proofs (`--safe --without-K`, no postulates in `proofs/agda`):

- `echo-intro` (introduction into own fiber)
- `map-over` (action on fibers for morphisms over fixed base)
- `map-over-id` (identity law)
- `map-over-comp` (composition law)
- `map-square` (action along commuting squares)

Characteristic M2 results include:

- explicit non-injectivity witnesses for collapse maps
- impossibility of full reconstruction from plain visible output (`no-section-*` family)
- distinct echoes over the same visible value (`echo-true≢echo-false`, `stateA≢stateB`)
- retained-constraint theorem for projection-style structured loss (`visible-constraint`)

Scope-broadening stages now include:

- choreographic bridge (`RoleEcho` over role projections, commuting-square transport)
- epistemic bridge (indistinguishability and echo-indexed knowledge)
- affine/linear bridge (strict weakening from full echoes to residues)
- graded bridge (grade order and compositional degradation law)
- tropical bridge (argmin-style witness residues under tropical collapse)
- integration bridge (knowledge preservation under choreography plus controlled graded degradation)
- indexed/relational/categorical packaging (`EchoIndexed`, `EchoRelational`, `EchoCategorical`, `EchoScope`)
- cross-ecosystem bridges (`EchoCNOBridge`, `EchoJanusBridge`, `DyadicEchoBridge`, `EchoOrdinal`)

## Current Status Snapshot (2026-04-23)

On `main`, the following are true:

- full suite compiles: `agda -i proofs/agda proofs/agda/All.agda`
- core echo/fiber laws are smoke-pinned (`echo-intro`, `map-over`, `map-over-id`, `map-over-comp`, `map-square`)
- non-injectivity/no-section family is present (`collapse-non-injective`, `no-section-collapse`, `no-section-visible`, `no-section-collapse-to-residue`, `no-section-weaken`)
- distinct-witness and retained-constraint exemplars are present (`echo-true≢echo-false`, `stateA≢stateB`, `visible-constraint`)

Ordinal/Buchholz track status:

- `Ordinal.Buchholz.WellFounded` provides `wf-<ᵇ : WellFounded _<ᵇ_` for the currently admitted constructor core
- top-marker `bplus` bridges are admitted and inverted: `<ᵇ-+ω`, `<ᵇ-+ψω`, `<ᵇ-inv-+Ωω`, `<ᵇ-inv-+ψω`
- left-summand bridges into additive terms are admitted and inverted: `<ᵇ-Ω+`, `<ᵇ-ψ+`, `<ᵇ-inv-Ω+`, `<ᵇ-inv-ψ+`
- general additive-target bridges are admitted and inverted: `<ᵇ-+Ω`, `<ᵇ-+ψ`, `<ᵇ-inv-+Ω`, `<ᵇ-inv-+ψ`
- `Ordinal.Buchholz.VeblenInterface` pins the measure-based WF interface with explicit constructor obligations; the historical same-binder fields (`dec-ψα`, `dec-+2`) remain part of the generic interface, but the closed comparison route now discharges them internally
- `Ordinal.Buchholz.VeblenMeasureTarget` fixes a first concrete target carrier: a lexicographic order on `OmegaIndex × BT`
- `Ordinal.Buchholz.VeblenProjectionMeasure` is retained as an explanatory scaffold: it makes the projection-style measure into that target explicit and discharges the shared-binder obligations there as target lemmas
- `Ordinal.Buchholz.VeblenComparisonTarget` adds a second concrete target: a lexicographic order on `BT × Payload` with recursive `ψ`-compatibility on the first coordinate and tagged payload descent for the same-binder follow-up cases
- `Ordinal.Buchholz.VeblenComparisonModel` is now the primary closed Veblen route: it instantiates the Veblen interface without deferred assumptions and exposes `core-wf-from-comparison : WellFounded _<ᵇ_`
- `Ordinal.Buchholz.ExtendedOrder` now packages a closed comparison-induced extension `_ <ᵇ⁺ _` of `BT`: it contains the current core, exposes the historical same-binder principles as lemmas, and is transitive and well-founded
- `Ordinal.Buchholz.SurfaceOrder` now adds a direct inductive surface `_ <ᵇˢ _` for the two historical same-binder shapes, with an embedding into `_ <ᵇ⁺ _` and inherited well-foundedness
- the Veblen comparison route is now closed for the current admitted constructor core
- the new `_ <ᵇ⁺ _` wrapper advances the full-order line by giving a mediated closed relation on all terms
- the new `_ <ᵇˢ _` surface is the first direct bridge candidate between the current core presentation and that mediated wrapper
- this does not yet internalize the historically blocked shared-binder shapes as actual constructors of `_ <ᵇ _`; the full intended Buchholz order remains open at that step
- remaining live mathematical work is therefore not the current-core WF route, but the mediated internalization of the shared-binder cases back into the real order package

## External Bridge Targets (local workspace)

Current bridge targets in this workspace are:

- `absolute-zero`: `/var/mnt/eclipse/repos/verification-ecosystem/maa-framework/absolute-zero`
- `januskey`: `/var/mnt/eclipse/repos/developer-ecosystem/januskey`
- `tropical-resource-typing` (potential target, not recently audited): `/var/mnt/eclipse/repos/verification-ecosystem/tropical-resource-typing` (upstream: `https://github.com/hyperpolymath/tropical-resource-typing`)

Note: `januskey` is not currently nested under `maa-framework` in this workspace layout.

Cross-repo status:

- bridge formalisms live in this repo (`EchoCNOBridge`, `EchoJanusBridge`, tropical-collapse witness work in `EchoTropical`)
- Agda-side adapter slot now exists in `maa-framework/absolute-zero` at `absolute-zero/proofs/agda/EchoBridgeScaffold.agda`
- end-to-end conformance against upstream codebases is a separate track and is not yet fully machine-checked here
- current bridge ledger: `docs/echo-types/cross-repo-bridge-status.md`
- see `docs/echo-types/roadmap.md` for staged cross-repo verification gates

## What Echo Types Are For

Echo types are useful when outputs are:

- insufficient to reconstruct their source exactly
- still sufficient to constrain the source non-trivially

Intended proof-use cases include:

- non-injective computation
- provenance
- structured irreversibility
- partial recoverability
- classification up to equivalence
- forensic inference from residues
- refined taxonomies of information loss

## Identity Claim and Falsifiability

This repo is trying to establish echo types as a concept with its own identity.
Since `Echo` is built from sigma/fiber machinery, identity will not come from syntax.
It must come from role and theorems.

We treat the claim as established only if all three are met:

1. Distinct phenomenon: structured loss under non-injective computation.
2. Characteristic theorem family: results that are naturally echo-shaped, not just generic sigma lemmas.
3. Canonical examples: cases where echo type is the right explanatory unit.

If these fail, we record that result and stop the identity claim.

## Build

```bash
cd /var/mnt/eclipse/repos/echo-types
agda -i proofs/agda proofs/agda/Echo.agda
```

Full suite:

```bash
cd /var/mnt/eclipse/repos/echo-types
agda -i proofs/agda proofs/agda/All.agda
```

## Tooling Stance

- default development stays plain Agda with the standard library
- optional exploratory work may use Agda's built-in `--cubical` mode plus the separate Cubical Agda library
- adjacent cubical systems such as `RedPRL`, `redtt`, and `cooltt` are tracked as references, not as active proof infrastructure for this repo
- see `roadmap.adoc` (`R2`) and `docs/adjacency/cubical-systems.adoc`

## Roadmap

Proof milestones and decision gates are in:

- `roadmap.adoc`
- `docs/buchholz-plan.adoc`

Open/gated work and cross-repo follow-ups are tracked in:

- `docs/echo-types/roadmap.md`
- `docs/echo-types/taxonomy.md`
- `docs/echo-types/composition.md`

## Licensing

- code, proofs, and tooling in this repository are intended to be licensed under `MPL-2.0`; see [LICENSE](LICENSE)
- prose documentation in `docs/`, `README.md`, `readme.adoc`, and roadmap files is intended to be licensed under `CC-BY-4.0`; see [LICENSE-docs](LICENSE-docs)
- current practical follow-up: normalize per-file SPDX headers across source files so file-level notices match the top-level licensing intent
