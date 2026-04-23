# Cross-Repo Bridge Status

Last updated: 2026-04-23

This file is the single status ledger for echo-type bridge work that touches
other repositories.

## Tracks

| Track | echo-types side | Adjacent side | Current status | Main blocker |
|---|---|---|---|---|
| CNO bridge (Agda) | `proofs/agda/EchoCNOBridge.agda` | `maa-framework/absolute-zero/proofs/agda/EchoBridgeScaffold.agda` | Adapter slot landed on both sides | `absolute-zero/proofs/agda/CNO.agda` still has unfinished holes, so direct import-level instantiation is deferred |
| CNO core theorem alignment | `EchoCNOBridge` theorem family | `absolute-zero/proofs/coq/common/CNO.v`, `absolute-zero/proofs/lean4/CNO.lean` | Paths identified; theorem-by-theorem alignment not yet done | Cross-prover statement normalization not written |
| JanusKey bridge (reversibility/category/thermo context) | `proofs/agda/EchoJanusBridge.agda`, `EchoThermodynamics.agda` | `januskey/src/abi/*.idr`, `januskey/docs/wiki/theory/*.adoc` | Conceptual relation present; no formal checker bridge yet | JanusKey formal artifacts are mostly Idris + docs, not a synchronized Coq/Lean theorem surface |
| Tropical alignment | `proofs/agda/EchoTropical.agda` | `tropical-resource-typing/*.thy`, `TropicalSessionTypes.lean` | Repo inventory complete; no theorem alignment yet | Adjacent repo not recently audited for this integration path |

## Immediate next actions

1. Close holes in `absolute-zero/proofs/agda/CNO.agda`.
2. Add `EchoCNOBridgeConcrete.agda` in `absolute-zero/proofs/agda/` that instantiates `EchoBridgeScaffold.CNOModel` from concrete CNO semantics.
3. Write a theorem correspondence table (name-by-name) for `EchoCNOBridge` vs Coq/Lean CNO statements.
4. Decide JanusKey formal target layer (Idris ABI vs another prover) before writing an automated bridge.
