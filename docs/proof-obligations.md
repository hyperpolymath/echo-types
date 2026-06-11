<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Proof Obligation Ledger

## Foundational Core
- **Echo Introduction:** PROVED (`echo-intro`)
- **Map Over:** PROVED (`map-over`)
- **Composition Law:** PROVED (`map-over-comp`)
- **Identity Law:** PROVED (`map-over-id`)

## Characteristic Theorems
- **Non-injectivity of collapse:** PROVED (`collapse-non-injective`)
- **No-section for visible output:** PROVED (`no-section-visible`)
- **No-section for weakened residue:** PROVED (`no-section-weaken`)
- **Distinct echoes over same base:** PROVED (`echo-true≢echo-false`)
- **Retained constraint for projection:** PROVED (`visible-constraint`)

## Bridges & Extensions (Speculative / Exploratory)
- **Graded Comonad Framing:** RETRACTED (This is a thin-poset action, not a comonad. See `docs/retracted/retractions.adoc`)
- **Universal Property / Terminal Cone:** RETRACTED (Requires funext, not natively constructible. See `docs/retracted/retractions.adoc`)
- **Conservativity Claims:** RETRACTED
- **Two-Models Framing:** RETRACTED
- **CNO Bridge (Absolute Zero):** PARTIAL
- **JanusKey Integration:** PARTIAL
- **Tropical Semantics (Argmin residues):** PARTIAL
- **Buchholz/Veblen Ordinal Representation:** BLOCKED (Well-foundedness of shared-binder cases blocked on self-lift)
