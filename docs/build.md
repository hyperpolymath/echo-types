<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Build Instructions

This repository contains mechanically verified proofs written in Agda.

## Prerequisites
- Agda (with the standard library)
- `just` (command runner)

## Verifying the Proofs

To run the complete verification suite, including safety checks and build steps:

```bash
sh scripts/verify.sh
```

To build the Agda proofs via `just`:

```bash
just build-all
```

To run the full suite via `just`:

```bash
just test-all
```
