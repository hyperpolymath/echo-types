<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Governance & Research Discipline

This repository operates under strict stabilisation and proof-preservation rules. It is treated as a sensitive proof artifact.

## Core vs. Bridge
- **Core:** The minimal, mechanically verified theory of echo types (`proofs/agda/Echo/Core.agda`, `Characteristic.agda`, `Residue.agda`). This is the unshakeable foundation.
- **Bridge:** Speculative extensions, cross-domain mappings, and integrations. Bridge materials are strictly labeled (e.g., PARTIAL, EXPLORATORY, BLOCKED) and reside in `proofs/agda/Echo/Bridges/` and `docs/bridges/`. They do *not* affect the core identity.

## Retractions
- A claim is **RETRACTED** when fundamental type-theoretic or mathematical obstacles are encountered (e.g., Graded Comonad framing, Universal Property without funext).
- Retracted claims are moved to `docs/retracted/`. They must not be revived without explicit new, mechanically verified proofs that overcome the documented blockers.

## Burden of Proof and Hidden Assumptions
- Every substantive theorem must be mechanically checked in Agda.
- **Prohibited:** Unsafe postulates, `TERMINATING` pragmas, `NON_TERMINATING` pragmas, `--allow-unsolved-metas`, and hidden assumptions.
- If a proof cannot be completed, it must be left as a typed hole, annotated as a `TODO`, and explicitly labeled as `BLOCKED`.
- Conjectures must be explicitly labeled as `CONJECTURE`.

## Modifications
- Do not perform global namespace rewrites or aggressive file moves.
- Favor small, proof-preserving commits.
- Documentation must prioritize precision, restraint, and falsifiability over hype.
