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
