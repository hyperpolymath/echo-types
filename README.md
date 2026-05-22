<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# echo-types

[![OpenSSF Best Practices](https://img.shields.io/badge/OpenSSF-Best_Practices-green?logo=opensourcesecurity)](https://www.bestpractices.dev/en/projects/new?repo_url=https://github.com/hyperpolymath/echo-types)
[![License: MPL-2.0](https://img.shields.io/badge/License-MPL--2.0-blue.svg)](https://www.mozilla.org/en-US/MPL/2.0/)
[![Green Web](https://api.thegreenwebfoundation.org/greencheckimage/github.com)](https://www.thegreenwebfoundation.org/green-web-check/?url=github.com)

Constructive Agda development isolating a minimal, mechanically defensible core for "echo types": a first-class notion of structured loss where irreversible operations retain a proof-relevant constraint on what was lost.

## ⚠️ Repository Stance

This repository has been strictly refactored to separate **mechanically verified core theory** from **speculative bridge material and retracted claims**. 

We prioritise correctness over ambition. For a strict ledger of what is proven, what is partial, and what is retracted, see the [Proof Obligation Ledger](docs/proof-obligations.md). 

For technical defenses against triviality, see our [Skepticism Documents](core/skepticisms/) (e.g., *Is this just Fibers?*).

For the narrative structure of the core argument, see the [Paper Spine](docs/paper-spine.md).

## The Minimal Core

Most formalisms foreground two clean cases:
1. Reversible / injective: no important loss.
2. Ordinary irreversible: loss occurs and is forgotten.

Echo types target a third case:
3. Irreversible, but with a retained proof-relevant constraint on what was lost.

Given `f : A → B`, the "echo" at `y : B` is defined purely structurally as the fiber:

`Echo f y := Σ (x : A) , (f x ≡ y)`

The core claim is *not* that this syntax is new (it is a standard homotopy fiber), but that treating this specific structure as a computational artifact of irreversible processes exposes a class of practically useful "residue" theorems.

The foundational, mechanically verified core is isolated in:
- `proofs/agda/Echo/Core.agda`
- `proofs/agda/Echo/Characteristic.agda`
- `proofs/agda/Echo/Residue.agda`

Characteristic results (PROVED) include:
- Explicit non-injectivity witnesses for collapse maps (`collapse-non-injective`).
- Impossibility of full reconstruction from visible output (`no-section-*` family).
- Retained-constraint theorem for projection-style structured loss (`visible-constraint`).

Canonical examples are in `proofs/agda/Echo/Examples/`:
- Lossy boolean classification (`EchoExampleAbsInt.agda`).
- Provenance and redaction (`EchoExampleProvenance.agda`).

## Bridge Material [EXPERIMENTAL / SPECULATIVE]

Extensive exploratory work connecting Echo Types to other domains has been isolated into `proofs/agda/Echo/Bridges/` and `docs/bridges/`. **These are strictly labeled as partial or speculative.**

- **CNO Bridge (Absolute Zero):** [PARTIAL] Integrating with semantic collapse models.
- **Thermodynamics:** [EXPLORATORY] Mapping information loss to thermodynamic cost.
- **Tropical Semantics:** [PARTIAL] Argmin-style witness residues.
- **Buchholz / Veblen Ordinals:** [BLOCKED] Ordinal representation tracks are blocked on the well-foundedness of shared-binder cases (self-lift fails).
- **JanusKey / Categorical:** [EXPLORATORY]

## Retracted Claims [RETRACTED]

The following framings were previously explored but have been strictly **retracted** due to fundamental type-theoretic or mathematical obstacles. They must not be revived without explicit new mechanical proof. See `docs/retracted/` for historical context.

- **Graded Comonad Framing:** The structure is a thin-poset action, not a true graded comonad.
- **Universal Property / Terminal Cone:** Blocked by the lack of native function extensionality.
- **Conservativity / Two-Models Framing.**

## Build

To build the strictly verified core and all experimental bridges:

```bash
just build-all
```

To run the test suite:

```bash
just test-all
```

## Tooling Stance

- Default development stays plain Agda with the standard library (`--safe --without-K`).
- We do not use unsafe postulates, `TERMINATING` pragmas, or hidden assumptions to bypass checking. If a proof cannot be completed, it is left as a typed hole and marked `BLOCKED`.

## Licensing

- Code and proofs: `MPL-2.0`; see [LICENSE](LICENSE).
- Prose documentation: `CC-BY-4.0`; see [LICENSE-docs](LICENSE-docs).
