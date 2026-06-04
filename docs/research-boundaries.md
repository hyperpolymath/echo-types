<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Research Boundaries

The goal of this project is to maintain a minimal, defensible core for Echo Types.

## What is In-Scope
- **Proof-preserving cleanup:** Refactoring that maintains exact semantics and improves readability.
- **Documentation precision:** Clarifying exact proof obligations, adding theorem indexes, and noting limitations.
- **Compatibility hardening:** Using wrappers to ensure stable imports for dependent projects.
- **Auditing:** Verification scripts that reject unsafe assumptions or pragmas.
- **Minimal Canonical Examples:** Small, self-contained illustrations of structured loss (e.g., lossy boolean classification, provenance).

## What is Strictly Out-of-Scope
- **Abstraction expansion:** Inventing new mathematical terminology or introducing large categorical frameworks unless strictly required by a specific, mechanically verified theorem.
- **Theory growth:** Attempting to "complete" the theory beyond the established minimal core.
- **Revisiting Retractions:** Revisiting graded-comonad framing, universal property framing, or thermodynamics without substantial new mechanical breakthroughs.
- **Unsafe assumptions:** Introducing `postulate`, `TERMINATING`, or `--allow-unsolved-metas` to force a proof to pass.
- **Overclaiming:** Using hype-driven terminology like "revolutionary" or "universal" in place of "mechanically checked" or "candidate."
