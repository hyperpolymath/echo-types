<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Failure Conditions

## The Skeptical Position
Any formalism can be made to work on trivial examples. The true test of a theory is its boundary conditions and where it breaks down.

## Explicit Failure Modes

1. **Abstraction Leaks:** If users must constantly unwrap the `Echo` to perform standard proofs, the abstraction has failed.
2. **Combinatorial Explosion:** If composing two lossy operations `f` and `g` results in an unmanageably complex nested `Echo`, the theory is not compositionally viable.
3. **Triviality:** If the only provable theorems are isomorphic to `f x ≡ f x`, the theory lacks predictive power.
4. **Lack of Separation:** If the "residue" cannot be meaningfully separated from the full "echo" in a proof-relevant way (e.g., if extracting the constraint requires keeping the entire original witness), then the claim of "partial recovery" is false.

## The Burden of Proof
The repository must provide mechanically checked counter-examples to these failure modes, specifically demonstrating non-trivial composition, manageable complexity, and strict separation of residues.
