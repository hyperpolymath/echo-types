<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Bridge Status

This document strictly tracks the status of experimental extensions and bridges between the minimal core of Echo Types and other domains.

**Note:** Bridge materials are speculative and exploratory. They do *not* affect the core identity or foundational theorems of the repository.

## 1. CNO Bridge (Absolute Zero)
- **Status:** PARTIAL
- **Dependencies:** Absolute Zero Framework
- **Blockers:** End-to-end integration across repositories is not yet mechanically verified here.
- **Core Affect:** NO

## 2. Thermodynamics
- **Status:** EXPLORATORY
- **Dependencies:** None
- **Blockers:** The quantitative collapse functional on infinite carriers is negatively closed (`collapse-cost-impossible`).
- **Core Affect:** NO

## 3. Tropical Semantics
- **Status:** PARTIAL
- **Dependencies:** None
- **Blockers:** Witness residues under tropical collapse are established, but broader ecosystem mapping remains incomplete.
- **Core Affect:** NO

## 4. Buchholz / Veblen Ordinals
- **Status:** PARTIAL (11/13 constructors closed under WfCNF; 1 in flight)
- **Dependencies:** Standard Agda
- **Blockers:** `<ᵇ-+1` joint-bplus is the single remaining open constructor. The head-Ω domination route (option A) has its abstraction + per-marker dominances at both branches + the option-(b) head-Ω inversion lemmas all landed across 2026-05-27 (PRs #124 / #130 / #131); only the WfCNF-carrier structural recursion (Slice 2-bplus) remains. The earlier shared-binder-self-lift blocker is resolved (`RankAdm` + `RankLex` slices, 2026-05-26/27). Live tracker: `docs/echo-types/buchholz-rank-obstruction.adoc`.
- **Core Affect:** NO

## 5. JanusKey / Categorical
- **Status:** EXPLORATORY
- **Dependencies:** Categorical foundations
- **Blockers:** Higher-level abstractions (monads, adjunctions) are still evolving; core functors are stable.
- **Core Affect:** NO

## 6. Decoration bridge (conceptual, not cross-repo)
- **Status:** EXPLORATORY (R5 deferred-research; cleanly abandonable)
- **Dependencies:** `EchoIntegration`, `EchoChoreo`, `EchoGraded` (import only)
- **Blockers:** Bridge is bounded by construction. Closes under any of the documented termination criteria: Track A/B/C failure, all candidate analogies retired, redundancy with retracted-prose graded-comonad framing, forbidden-rebrandings register addition, retraction-watch trip. Companion: `docs/echo-types/explorations/decoration-bridge/README.adoc`; module: `proofs/agda/EchoDecorationBridge.agda` (deliberately not in `All.agda`).
- **Core Affect:** NO

## 7. Valence Shell / Ochránce accountable-shell bridge (candidate downstream consumer)
- **Status:** EXPLORATORY (candidate downstream consumer; no Agda artefact, no cross-repo theorem)
- **Dependencies:** None in this repo. Adjacent (downstream) only: Valence Shell (`hyperpolymath/valence-shell` — shell state transitions, undo/redo, checkpoints, diff/replay); Ochránce (`hyperpolymath/ochrance` — A2ML manifests, Merkle state commitments, repair/attestation surfaces).
- **Blockers:** No shared schema and no mechanised cross-repo theorem exist. The relationship is citation-level only: Echo Types' structured-loss vocabulary (recoverable / constrained / residue-bearing / observationally equivalent / genuinely lost) is a *candidate* classifier for shell state transitions, and Ochránce may supply concrete receipt evidence. This is downstream application evidence, not a new foundation. Echo Types makes **no** claim about Valence Shell or Ochránce implementation correctness, and **no** claim about POSIX, Rust, the Lean→Rust correspondence, secure deletion, GDPR, cryptographic integrity, or attestation. Companion note: `docs/echo-types/explorations/accountable-shell/README.adoc`. Nothing for this bridge is imported into `proofs/agda/All.agda`, `proofs/agda/Smoke.agda`, or `proofs/agda/EchoCanonicalIdentitySuite.agda`.
- **Core Affect:** NO
