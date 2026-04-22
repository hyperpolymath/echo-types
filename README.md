# echo-types

Constructive Agda formalization of echo types / fibers:

`Echo f y := Σ (x : A) , (f x ≡ y)`

This repository provides a minimal, explicit development in ordinary intensional dependent type theory (`--safe --without-K`) with:

- fiber introduction (`echo-intro`)
- action on fibers over a fixed base (`map-over`)
- identity law (`map-over-id`)
- composition law (`map-over-comp`)
- action along commuting squares (`map-square`)

## Controlled Scope Broadening

The formal scope is extended in controlled phases:

- Phase A (`proofs/agda/EchoIndexed.agda`): role-indexed echoes `Echoᵢ` with trace-level witness separation.
- Phase B (`proofs/agda/EchoEpistemicResidue.agda`): residue-based epistemic echoes `EchoR` with strict weakening/no-section results.
- Phase C (`proofs/agda/EchoRelational.agda`): relational semantics `Step : S → O → Set` and output fibers `Σ s , Step s o`.
- Phase D (`proofs/agda/EchoCategorical.agda`): slice/fibration packaging over the compiled deterministic and relational layers.

## Build

```bash
cd /var/mnt/eclipse/repos/echo-types
agda -i proofs/agda proofs/agda/Echo.agda
agda -i proofs/agda proofs/agda/All.agda
for f in proofs/agda/*.agda; do agda -i proofs/agda "$f"; done
```

## Bridge to Certified Null Operations (CNOs)

This repository now includes a theoretical bridge to **Certified Null Operations (CNOs)** from the [Absolute Zero](https://gitlab.com/maa-framework/6-the-foundation/absolute-zero) project.

**Key Insight**: CNOs are singleton echo types over identity functions.

**Bridge Modules**:
- `proofs/agda/EchoCNO.agda` - Basic bridge with core theorems
- `proofs/agda/EchoCNOBridge.agda` - Comprehensive bridge with full mapping

**Documentation**: See `docs/ECHO-CNO-BRIDGE.adoc` for detailed explanation.

**Main Theorems**:
- `cno-echo-equivalence`: CNOs ≃ singleton echoes over identity
- `all-cnos-are-echos`: All state-preserving programs are echoes over identity
- `cno-composition-echo`: CNO composition preserves echo structure

This bridge enables:
- Using echo type theory for CNO verification
- Cross-repository theorem sharing
- Unified foundation for structured loss and null operations
