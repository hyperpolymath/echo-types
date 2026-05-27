# Changelog

All notable changes to echo-types will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added (2026-05-27)

- *Lane 3 ordinal track — 11/13 Buchholz constructors closed under
  WfCNF restriction.* Three slices land on top of the existing
  `RankPow` 9-constructor umbrella:
  - `Ordinal.Buchholz.RankAdm` (admissibility-aware rank
    `rank-adm (bpsi ν α) = ω-rank-pow ν ⊕ rank-pow α`) closing
    `<ᵇ⁺-ψα` via `rank-mono-<ᵇ⁺-ψα-from-pow`.
  - `Ordinal.Buchholz.RankLex` (lex-pair rank `RankLex` over
    `Ord × Ord` with shared-implicit second-strict constructor)
    closing `<ᵇ-ψΩ≤` at both `ν<μ` (first-strict) and the
    `ν=μ` boundary (second-strict via the admissibility bound).
  - `Ordinal.Buchholz.HeadOmega` (leading-Ω-index head function
    `head-Ω : BT → OmegaIndex` plus definitional sanity lemmas and
    a two-level compositional convenience) — first slice of option
    (A) for the remaining `<ᵇ-+1` joint-bplus discharge; no
    rank-mono yet.
- *Lane 3 head-Ω route — Slice 2 + Slice 2-omega + inversion (option (b))
  landed.* Follow-on to the Slice 1 head-Ω landing above (session night,
  PRs #130 + #131):
  - `Ordinal.Buchholz.RankPow` gains `ω-rank-pow-succ : OmegaIndex →
    Ord` with per-marker strict dominance at *both* branches
    (`ω-rank-pow-<-succ-fin` via `ω^-strict-mono-suc`;
    `ω-rank-pow-<-succ-omega` via the `Brouwer/OmegaPow.ω^-strict-mono-suc`
    template mirrored at `ω-rank-pow ω`) plus the unified
    `ω-rank-pow-<-succ : ∀ μ → ω-rank-pow μ <′ ω-rank-pow-succ μ`,
    plus atomic-rank factoring through `head-Ω`
    (`rank-pow-bOmega-via-head-Ω`, `rank-pow-bpsi-via-head-Ω`).
  - Slice 2-omega closes a Brouwer-encoding hazard the original
    CLAUDE.md proposal would have tripped: the proposed
    `ω-rank-pow-succ ω = olim (λ n → ω^(suc(suc n)))` is
    equi-ordinal with `ω-rank-pow ω = olim (λ n → ω^(suc n))`
    (both denote `ω^ω`), so cannot strictly dominate.  The
    revised shape `olim (λ n → ω-rank-pow ω ·ℕ n)` denotes
    `ω^(ω+1)` and goes strictly higher via `X≤′oz⊕X` +
    `⊕-mono-<-right (ω-rank-pow-pos ω)`.  Full record in
    `Ordinal.Buchholz.RankPow`'s "History note" block.
  - New module `Ordinal.Buchholz.HeadOmegaInversion` lands the
    option-(b) inversion lemmas `head-Ω-inv-bOmega :
    bOmega ν <ᵇ y → ν <Ω head-Ω y` (strict — three constructors
    with `bOmega ν` LHS all carry strict `<Ω` witnesses) and
    `head-Ω-inv-bpsi : bpsi ν α <ᵇ y → ν ≤Ω head-Ω y` (non-strict —
    the `<ᵇ-ψΩ≤` constructor tops out at `≤Ω`).  Both proved by
    structural recursion on the `<ᵇ` derivation; no rank-mono
    dependency.  Picking option (b) over option (a) keeps the
    eventual `rank-pow-dominated-by-head-Ω` (Slice 2-bplus,
    remaining open) independent of the still-open `rank-pow-mono-≤ᵇ`
    on the original `_<ᵇ_`.
- *Decoration bridge — R5 exploratory entry scaffolded (PR #129).*
  `docs/echo-types/explorations/decoration-bridge/` lands a bounded
  exploration of whether the Choreo × Graded integration shape
  resembles adjacent-domain decoration constructions (CRDTs, gossip,
  local-first causal histories).  Scope strictly the one axis pair
  `EchoIntegration.agda` already integrates; external candidates
  framed as analogies-with-falsifiers, never as evidence of recipe
  generalisation.  Sits as `roadmap.adoc` § R5 (deferred research)
  with explicit termination criteria (Track A/B/C failure, all
  candidates retired, redundancy with retracted framing,
  forbidden-rebrandings register addition, retraction-watch trip).
  Companion Agda module `proofs/agda/EchoDecorationBridge.agda` —
  deliberately not in `All.agda`, classified as "Exploratory (not in
  All.agda)" in `docs/echo-types/echo-kernel-note.adoc` so CI's
  classification-drift lint stays green.
- *Lane 5 tutorial track — the originally-scaffolded triplet is
  complete.* `tutorial/` ships three worked walkthroughs with
  honest-bound disclosure at top + matched-negative `NotProved-*`
  `⊤`-aliases at bottom:
  - `tutorial/region_exit_audit/` (Walkthrough 1, killer-app
    candidate per `roadmap.adoc` §Lane 5) — ephapax-L3-style
    region exit modelled type-level via
    `EchoLinear.no-section-weaken`.
  - `tutorial/epistemic_erasure/` (Walkthrough 2) — 4-seed →
    2-key KDF with no-section-via-residue lifted from
    `EchoResidue.no-section-collapse-to-residue`.
  - `tutorial/provenance_debugging/` (Walkthrough 3) — 4-element
    `State` with two orthogonal sign bits walked through 3 residue
    layers; new pedagogical shape ships *both* a section (Layer 1
    `recover-section-at-layer-1`) and its absence (Layer 2
    `no-recovery-from-trivial`), exhibiting the boundary at which
    the type-level recovery property flips.
- *Establishment-track Pillar E — packaging pre-staged.*
  `CITATION.cff` and `.zenodo.json` at the repo root (placeholder
  DOI + ORCID-commented until author setup), `echo-types.agda-lib`
  with dual `include: proofs/agda .` covering the tutorial track,
  and README §Citation + §"Installing as a library" sections. CI
  install-self + GitHub→Zenodo workflows intentionally deferred
  until the author authorises the Zenodo integration (avoids
  transient CI red).
- *Establishment-track Pillar E — venue + outreach.*
  `docs/echo-types/pillar-e-offline.adoc` lands the venue matrix
  (TYPES → CPP → ITP → MSCS), Zenodo DOI mint plan, library
  packaging plan, and three pre-written outreach cover letters
  (Granule/QTT, choreographic types, Linear Haskell). Author-driven
  for submission, sending, and Zenodo flip.
- *Gate 2 audit — Revision 5 + 5b.* `docs/characteristic.adoc`
  carries the close-out re-audit (4/4 surviving theorems, N5
  resolved within Rev 5 follow-up).
- Initial RSR template floor (CHANGELOG/SECURITY/CONTRIBUTING/QUICKSTART set + contractiles + 4 mandatory workflows + dotfiles + 0-AI-MANIFEST). Scaffolded 2026-04-30.

### Changed (2026-05-27)

- *Roadmap consolidation.* Five overlapping roadmap docs
  (`docs/echo-types/roadmap.md`, `docs/PRIORITIZED_PROOF_ROADMAP.md`,
  `docs/ProofRoadmap.md`, `docs/WORK_PLAN.md`, plus stragglers)
  consolidated into the single canonical `roadmap.adoc` at repo
  root.
- *Per-constructor verdict on `_<ᵇ_`.*
  `docs/echo-types/buchholz-rank-obstruction.adoc` score bumped
  10/13 → 11/13; `<ᵇ-ψΩ≤` flipped from "encoding mismatch" to
  "closed (Lane 3 follow-on, lex pair)". Only `<ᵇ-+1` joint-bplus
  remains in the per-constructor matrix.
- *N5Falsifier promoted into characteristic CI green closure.*
  `proofs/agda/characteristic/N5Falsifier.agda` no longer carries
  the "broken" banner; the unsolved metas were diagnosed as an
  inference blocker (Agda cannot recover the role from
  `RoleGEcho r keep = Echo (obs r) true` because `obs` is not
  injective), resolved by making the `applyRole` / `applyGrade`
  Role + Grade parameters explicit at the four call sites.
- 6a2 metadata files migrated from `*.scm` at repo root to `.machine_readable/6a2/*.a2ml` per the canonical hyperpolymath rule (`.a2ml` is the canonical extension; `.scm` is reserved for Guix). 2026-04-30.

## [0.1.0+integration-pending]

### Added

- Core echo / fiber theorems (`echo-intro`, `map-over`, `map-over-id`, `map-over-comp`, `map-square`).
- Characteristic non-injectivity / no-section family.
- Bridges: `EchoLinear`, `EchoGraded`, `EchoTropical`, `EchoChoreo`, `EchoEpistemic`, `EchoCNOBridge`, `EchoJanusBridge`, `DyadicEchoBridge`, `EchoOrdinal`, `EchoIndexed`, `EchoRelational`, `EchoCategorical`, `EchoScope`.
- Ordinal / Buchholz track artefacts (`Ordinal.Buchholz.*`).
