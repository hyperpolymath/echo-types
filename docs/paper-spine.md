<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Paper Spine

## 1. Problem
Standard formalisms prioritize reversible or perfectly linear systems where no information is lost, or simply discard lost information entirely in irreversible systems. There is no first-class treatment for *structured* loss where the fact of the loss and a constraint on what was lost are retained.

## 2. Observation
When a non-injective function collapses distinct inputs to the same output, the fiber over that output contains the exact witness of the collapse. Treating this fiber not as a topological artifact but as a computational "echo" provides a formal vocabulary for partial recovery.

## 3. Definition
Given `f : A → B`, the echo at `y : B` is defined as:
`Echo f y := Σ (x : A) , (f x ≡ y)`

## 4. Why ordinary fibers are insufficient
While structurally identical to homotopy fibers, ordinary fibers are rarely studied as carriers of programmatic provenance or computational residue. The "Echo" vocabulary shifts the focus from equivalence proofs to epistemic constraints and non-injective bounds.

## 5. Characteristic theorem candidates
- `collapse-non-injective`: Explicit witnesses of irreversible collapse.
- `no-section-visible`: It is impossible to fully reconstruct the input from the output alone.
- `visible-constraint`: Projection-style structured loss retains a provable constraint on the original state.

## 6. Canonical example
Lossy boolean classification (`true` and `false` collapsing to `unit`), demonstrating distinct echoes over the same visible value.

## 7. Failure conditions
If the echo type requires constant manual unwrapping to the underlying sigma type, or if compositional complexity explodes, the abstraction fails.

## 8. Bridge roadmap
Future exploratory work includes bridging this minimal core to thermodynamic costs, tropical semantics, and choreographic state tracking.
