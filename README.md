<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# echo-types

[![OpenSSF Best Practices](https://img.shields.io/badge/OpenSSF-Best_Practices-green?logo=opensourcesecurity)](https://www.bestpractices.dev/en/projects/new?repo_url=https://github.com/hyperpolymath/echo-types)
[![License: PMPL-1.0](https://img.shields.io/badge/License-PMPL--1.0-blue.svg)](https://github.com/hyperpolymath/palimpsest-license)
[![Green Web](https://api.thegreenwebfoundation.org/greencheckimage/github.com)](https://www.thegreenwebfoundation.org/green-web-check/?url=github.com)

Constructive Agda development for echo types as a first-class notion of structured loss:

loss that is not total erasure.

## 🗺️ Where things are

**New here, or can't find something? Start with the
[Master Map](docs/echo-types/MAP.adoc).** It is the single source of
truth for every direction (Thermodynamic, Buchholz/Veblen ordinals,
Characteristic/EI, CNO/absolute-zero, JanusKey, Tropical/Dyadic, MAA,
Shannon — and ArghDA tooling), each status-tagged and back-linked to
its proofs and docs, with the retraction/proof-debt governance called
out. The scattered overview/roadmap docs are detail under it.

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
- integration bridge (cross-decoration commutation via the recipe; the recipe is useful as organising vocabulary but does not carry substantive simultaneous integration content — see `docs/EI2_REPORT.adoc`. Distinctness rests on truncation and 2-cell arguments)
- indexed/relational/categorical packaging (`EchoIndexed`, `EchoRelational`, `EchoCategorical`, `EchoScope`)
- cross-ecosystem bridges (`EchoCNOBridge`, `EchoJanusBridge`, `DyadicEchoBridge`, `EchoOrdinal`)

## Current Status Snapshot

The repository runs **two parallel, independent tracks**. *Echo Core does
NOT depend on the Ordinal / Buchholz track.* A reader interested only
in echo types as a type-theoretic concept can ignore the Ordinal track
entirely; it lives in `proofs/agda/Ordinal/` and is documented under
`roadmap.adoc` §Lane 3.

### Echo Core (load-bearing for the identity claim)

On `main`, the following are true:

- full suite compiles: `agda -i proofs/agda proofs/agda/All.agda`
- core echo/fiber laws are smoke-pinned (`echo-intro`, `map-over`, `map-over-id`, `map-over-comp`, `map-square`)
- non-injectivity/no-section family is present (`collapse-non-injective`, `no-section-collapse`, `no-section-visible`, `no-section-collapse-to-residue`, `no-section-weaken`)
- distinct-witness and retained-constraint exemplars are present (`echo-true≢echo-false`, `stateA≢stateB`, `visible-constraint`)
- degrade-law family lands across decoration layers (graded, linear/affine, choreographic, access, cost, search); see `docs/theorem-index.md` for the aggregate
- Pillars A–D of the establishment plan are LANDED (with R-2026-05-18 narrowings; see `docs/retractions.adoc`); Pillar E (paper) is in progress
- Lane 5 tutorial triplet LANDED 2026-05-27 under `tutorial/`: region-exit audit, epistemic erasure, and provenance / debugging — each with honest-bound + matched-negative disclosure discipline; build via `agda --library-file=/tmp/agda-libs -i . -i proofs/agda tutorial/All.agda`

Per-lane status, close-out criteria, and the identity-claim verdict
per tag are in `roadmap.adoc`.

### Ordinal / Buchholz (parallel-independent, experimental)

> **Banner.** This track is a separate proof-theoretic research project
> living in the same repository. Echo Core does not depend on it.
> Modules under `proofs/agda/Ordinal/` are treated as **experimental**
> until the unbudgeted `wf-<ᵇʳᶠ_` closure lands. See `roadmap.adoc`
> §Lane 3 for status and close-out criterion; `docs/buchholz-plan.adoc`
> for the full plan.

Current state (one-line summary; the full per-rung ledger lives in
CLAUDE.md):

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
- `Ordinal.Buchholz.LiftedExtendedOrder` now adds the next honest wrapper `_ <ᵇ⁺¹ _`: the blocked self-lift of `_ <ᵇ⁺ _` fails, but same-binder moves from `_ <ᵇ⁺ _` into `_ <ᵇ⁺¹ _` are derivable and `_ <ᵇ⁺¹ _` is well-founded
- `Ordinal.Buchholz.IteratedExtendedOrder` now packages that repair as a finite iteration scheme: `LiftedOrder n` gives the `n`th wrapper layer, same-binder moves lift one level at a time, and exact finite same-binder depth is tracked by `SurfaceDepth n` with an embedding into `LiftedOrder (suc n)`
- `Ordinal.Buchholz.SurfaceOrder` now adds a direct inductive surface `_ <ᵇˢ _` for the two historical same-binder shapes, with an embedding into `_ <ᵇ⁺ _` and inherited well-foundedness
- `Ordinal.Buchholz.RecursiveSurfaceOrder` now adds a genuinely recursive finite-closure candidate `_ <ᵇʳᶠ _`: every derivation extracts an exact finite depth and embeds into `LiftedOrder (suc n)`, so irreflexivity follows without requiring a single self-stable wrapper
- `Ordinal.Buchholz.RecursiveSurfaceBudget` now packages the next accepted recursion vehicle: a budgeted relation on `ℕ × BT` whose first coordinate strictly decreases and which still carries the lifted witness into the iterated wrapper tower
- the exact remaining recursive frontier is now explicit in code as a blocked self-lift: `SurfaceLiftInterface` is refuted by a concrete same-left `bplus` counterexample, and the surviving route is finite wrapper iteration rather than self-stability
- the Veblen comparison route is now closed for the current admitted constructor core
- the new `_ <ᵇ⁺ _` wrapper advances the full-order line by giving a mediated closed relation on all terms
- the new `_ <ᵇˢ _` surface is the first direct bridge candidate between the current core presentation and that mediated wrapper
- the new `LiftedOrder n` / `SurfaceDepth n` family shows that arbitrary finite same-binder depth can already be handled by iterated mediated wrappers
- the new `_ <ᵇʳᶠ _` candidate shows that direct recursive derivations also reduce to those finite-depth fragments; what is still open is a single global mediated well-foundedness theorem for that union
- the new budgeted layer on `ℕ × BT` isolates the missing global step: the recursive surface route is now well-founded once explicit budget is carried, and the remaining task is to discharge or eliminate that budget in the unbudgeted theorem
- this still does not internalize the historically blocked shared-binder shapes as actual constructors of `_ <ᵇ _`; the full intended Buchholz order remains open at that step
- remaining live mathematical work is therefore not the current-core WF route, but the mediated internalization of the shared-binder cases back into the real order package
- as of 2026-05-27: the Buchholz rank-monotonicity matrix closes 11/13 constructor cases via the WfCNF-restricted `_<ᵇ⁻_` umbrella (9 via `RankPow` + `<ᵇ⁺-ψα` via `RankAdm` 2026-05-26 + `<ᵇ-ψΩ≤` via `RankLex` 2026-05-27); the last open case is `<ᵇ-+1` joint-bplus, with the `Ordinal.Buchholz.HeadOmega` first slice (leading-Ω-index head function + 4 definitional sanity lemmas) landed 2026-05-27 as the structural opening of option (A) per the obstruction doc

## External Bridge Targets (local workspace)

Current bridge targets in this workspace are:

- `absolute-zero`: `/var/mnt/eclipse/repos/verification-ecosystem/maa-framework/absolute-zero`
- `januskey`: `/var/mnt/eclipse/repos/developer-ecosystem/januskey`
- `tropical-resource-typing` (potential target, not recently audited): `/var/mnt/eclipse/repos/verification-ecosystem/tropical-resource-typing` (upstream: `https://github.com/hyperpolymath/tropical-resource-typing`)

Note: `januskey` is not currently nested under `maa-framework` in this workspace layout.

Cross-repo status:

- bridge formalisms live in this repo (`EchoCNOBridge`, `EchoJanusBridge`, tropical-collapse witness work in `EchoTropical`)
- Agda-side content-bridge `proofs/agda/EchoCNOBridge.agda` imports `IsCNO` directly from `absolute-zero/proofs/agda/CNO.agda` (the earlier scaffolded-adapter plan `EchoBridgeScaffold.agda` was superseded)
- end-to-end conformance against upstream codebases is a separate track and is not yet fully machine-checked here
- current bridge ledger: `docs/echo-types/cross-repo-bridge-status.md`
- see `roadmap.adoc` (Lane 4) for staged cross-repo verification gates

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

### Installing as a library

The repo is structured as an Agda library via `echo-types.agda-lib`
at the repo root. To use `echo-types` from another Agda project,
register the library file once:

```bash
git clone https://github.com/hyperpolymath/echo-types.git
echo "$(pwd)/echo-types/echo-types.agda-lib" >> ~/.agda/libraries
```

Then in any other project, depend on `echo-types` in that
project's own `.agda-lib`:

```text
name: my-project
depend: standard-library echo-types
include: src
```

Consumers can then `open import Echo`, `open import EchoLinear`,
or `open import tutorial.region_exit_audit.RegionExitAudit` — the
library's `include:` line covers both `proofs/agda` and the repo
root (for the Lane 5 tutorial track).

Requires `standard-library` v2.3 or later registered alongside.

## Citation

If you cite this repository in academic work, please cite via the
Zenodo DOI listed in [CITATION.cff](CITATION.cff). The Zenodo
record is the canonical citation target; GitHub's "Cite this
repository" widget resolves directly to it.

GitHub→Zenodo integration is a one-time author setup; until that
is wired the `CITATION.cff` `doi:` field carries a placeholder
(`10.5281/zenodo.0000000`). See
[docs/echo-types/pillar-e-offline.adoc](docs/echo-types/pillar-e-offline.adoc)
§"Zenodo DOI mint" for the activation sequence.

## Tooling Stance

- default development stays plain Agda with the standard library
- optional exploratory work may use Agda's built-in `--cubical` mode plus the separate Cubical Agda library
- adjacent cubical systems such as `RedPRL`, `redtt`, and `cooltt` are tracked as references, not as active proof infrastructure for this repo
- see `roadmap.adoc` (`R2`) and `docs/adjacency/cubical-systems.adoc`

## Roadmap

Single canonical roadmap with lane tracker, gates summary, pillar
status, deferred-research track, and operating rules:

- `roadmap.adoc`

Companions (different kinds of doc, not roadmaps):

- `roadmap-gates.adoc` — identity-claim falsifier gates (Gate 1/2/3)
- `docs/echo-types/establishment-plan.adoc` — five-pillar plan to
  recognised type-theoretic standing
- `docs/buchholz-plan.adoc` — Ordinal track plan (parallel-independent
  lane; see roadmap.adoc §Lane 3)
- `docs/echo-types/taxonomy.md`, `docs/echo-types/composition.md` —
  topical reference

As of 2026-05-26 the four previously overlapping roadmap docs
(`docs/echo-types/roadmap.md`, `docs/PRIORITIZED_PROOF_ROADMAP.md`,
`docs/ProofRoadmap.md`, `docs/WORK_PLAN.md`) have been consolidated
into `roadmap.adoc` and removed.

## Licensing

- code, proofs, and tooling in this repository are intended to be licensed under `MPL-2.0`; see [LICENSE](LICENSE)
- prose documentation in `docs/`, `README.md`, `readme.adoc`, and roadmap files is intended to be licensed under `CC-BY-4.0`; see [LICENSE-docs](LICENSE-docs)
- current practical follow-up: normalize per-file SPDX headers across source files so file-level notices match the top-level licensing intent
