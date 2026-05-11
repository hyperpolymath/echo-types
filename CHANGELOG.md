# Changelog

All notable changes to echo-types will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added

- Initial RSR template floor (CHANGELOG/SECURITY/CONTRIBUTING/QUICKSTART set + contractiles + 4 mandatory workflows + dotfiles + 0-AI-MANIFEST). Scaffolded 2026-04-30.

### Changed

- 6a2 metadata files migrated from `*.scm` at repo root to `.machine_readable/6a2/*.a2ml` per the canonical hyperpolymath rule (`.a2ml` is the canonical extension; `.scm` is reserved for Guix). 2026-04-30.

## [0.1.0+integration-pending]

### Added

- Core echo / fiber theorems (`echo-intro`, `map-over`, `map-over-id`, `map-over-comp`, `map-square`).
- Characteristic non-injectivity / no-section family.
- Bridges: `EchoLinear`, `EchoGraded`, `EchoTropical`, `EchoChoreo`, `EchoEpistemic`, `EchoCNOBridge`, `EchoJanusBridge`, `DyadicEchoBridge`, `EchoOrdinal`, `EchoIndexed`, `EchoRelational`, `EchoCategorical`, `EchoScope`.
- Ordinal / Buchholz track artefacts (`Ordinal.Buchholz.*`).
