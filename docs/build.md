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
