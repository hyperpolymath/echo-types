# Changelog

All notable changes to echo-types will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added (2026-05-28)

- *Lane 3 ordinal track — Slice 3 prerequisites.* PR #137 added
  `proofs/agda/Ordinal/Buchholz/RankPowSlice3.agda` (220 lines) —
  three primitives toward the Slice 3 headline:
  - `NonBzero` — left-spine non-bzero predicate excluding the
    degenerate `bplus bzero bzero` chains that WfCNF technically
    allows but CNF normalisation excludes.
  - `ω-rank-pow-succ-≤-via-<Ω` — strict-jump bridge from `μ <Ω ν`
    to `ω-rank-pow-succ μ ≤′ ω-rank-pow ν`. Closes the gap between
    Slice 2-bplus's upper bound on the source's rank and the lower
    bound on the target's rank.
  - `head-Ω-lower-bound` — head-Ω LOWER bound under WfCNF +
    NonBzero. Dual of `rank-pow-dominated-by-head-Ω`.

- *Lane 3 ordinal track — Slice 3 headline closed under a strict-head
  premise.* PR #141 added
  `proofs/agda/Ordinal/Buchholz/RankPowSlice3Headline.agda` (155
  lines). The headline `rank-mono-<ᵇ-+1-via-head-Ω` closes the
  joint-bplus rank-mono case for `_<ᵇ-+1_` via Route A from the
  Slice 3 design note. The proof composes the four Slice 3
  prerequisites in a clean chain (no structural recursion):
  Slice 2-bplus + head-Ω-bplus → strict-jump bridge → head-Ω lower
  bound → `⊕-left-≤-sum`, all via `≤′-trans`. The headline takes
  the strict-head premise `head-Ω x₁ <Ω head-Ω y₁` as an EXTERNAL
  HYPOTHESIS; the umbrella's case-split is the remaining wiring
  (the `bpsi=bpsi` at equal markers sub-case still needs `α`'s
  rank via rank-adm or rank-lex). Compiles standalone under
  `--safe --without-K`, zero postulates. Smoke green.

- *Canonical identity layer — (epi, mono) earn-back form.* PR #138:
  `proofs/agda/EchoImageFactorizationProp.agda` lands the
  (epi, mono) factorisation module-parameterised in a truncation
  interface — the long-pending earn-back gate previously referenced
  as "next" in `docs/echo-types/MAP.adoc`. Companion to
  `EchoImageFactorization`. Classification: Tier 2 in
  `docs/echo-types/echo-kernel-note.adoc`.

- *Classification grid — Search + Epistemic ResidueForm instances.*
  PR #139: `EchoResidueTaxonomy.agda` gains two further `ResidueForm
  f R` instances (`Search` and `Epistemic`) alongside the existing
  four (trivial, identity, generic Σ-cert, linear-affine). Brings
  the total to six instances, with the other four decoration
  modules documented as structurally compatible.

- *Visual identity — banner kit ("Diagrammatic Hush").* PR #140:
  `docs/assets/banner.{png,svg}`, `docs/assets/banner-philosophy.md`,
  `tools/banner/build-banner.mjs`. The `README.md` and `readme.adoc`
  both gained the banner image at the top. No content impact; purely
  visual identity for the project's public surface.

### Fixed (2026-05-28)

- *CI hygiene: kernel-guard classification-drift unblocked.* PR #136:
  18 previously-unclassified `Echo*.agda` modules (the canonical-
  identity / OFS cohort plus the application/extension modules:
  `EchoTotalCompletion`, `EchoOrthogonalFactorizationSystem`,
  `EchoImageFactorization`, `EchoNoSectionGeneric`,
  `EchoLossTaxonomy`, `EchoResidueTaxonomy`,
  `EchoDecorationStructure`, `EchoObservationalEquivalence`,
  `EchoOFSUnivF5`/`Diag`/`Iso`, `EchoCanonicalIdentitySuite`,
  `EchoEntropy`, `EchoLLEncoding`, `EchoProvenance`, `EchoSecurity`,
  `EchoProbabilisticSupport`, `EchoDifferential`) are now classified
  in `docs/echo-types/echo-kernel-note.adoc`, unblocking
  `scripts/kernel-guard.sh` Check B (classification-drift lint).

- *CI hygiene: N5Falsifier xfail gate removed.* PR #136 also dropped
  the `Expected-failure gate (N5Falsifier is known-broken)` step
  from `.github/workflows/agda.yml`. `proofs/agda/characteristic/
  N5Falsifier.agda` was resolved on 2026-05-27 by pinning the
  implicit `r` / `grade` at four `applyRole` / `applyGrade` call
  sites — the unsolved-metas were an inference blocker, not a
  content blocker. The module is now imported by
  `proofs/agda/characteristic/All.agda` (line 33). The xfail gate's
  own self-disclosed instructions (`"register it in
  characteristic/All.agda and remove this xfail gate"`) fired on
  the previous CI run; this PR completed those instructions.

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
- *Lane 3 head-Ω route — Slice 2 + Slice 2-omega + inversion + Slice 2-bplus
  ALL LANDED 2026-05-27.* Follow-on to the Slice 1 head-Ω landing above
  (PRs #130 + #131 + #133 + #134):
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
    option-(b) inversion lemmas `head-Ω-inv-bOmega` (strict) and
    `head-Ω-inv-bpsi` (non-strict). Both proved by structural
    recursion on the `<ᵇ` derivation; no rank-mono dependency.
  - New module `Ordinal.Buchholz.RankPowDomination` lands the
    Slice 2-bplus headline `rank-pow-dominated-by-head-Ω` by
    structural recursion on WfCNF, plus the supporting lemmas
    (`<′→≤′`, `≤′-<′-trans`, `<′-trans`, `ω-rank-pow-mono-≤Ω`,
    `ω-rank-pow-succ-pos`, `additive-principal-ω-rank-pow-succ`,
    `rank-y-bound`). PR #134 was the one-line explicit-implicit
    fix for the initial `ω≤ω` case of `ω-rank-pow-mono-≤Ω`.
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
- *Tier-1+2+3 spine + audience moves + suite + F5 FULL PASS
  LANDED 2026-05-27.* My session's contribution sitting on top of
  the parallel-session ordinal work above. See CLAUDE.md's
  "Slice-2 upstream adoption" + "broad-cleanup close" session arcs
  for the deliverable list; key headlines: `EchoTotalCompletion.A↔ΣEcho`,
  `EchoOrthogonalFactorizationSystem.ofs-witness`,
  `EchoNoSectionGeneric.no-section-of-collapsing-map`, the four
  Tier-2 classification-grid records (`ResidueForm` /
  `DecorationStructure` / function-side / observational), the
  Pillar F Gate F5 FULL PASS triple (F5-1 / F5-2 / F5-3) earning
  back the qualified OFS, four audience-facing modules
  (`EchoProvenance` / `EchoSecurity` / `EchoProbabilisticSupport`
  / `EchoDifferential`), and the curated single-file entry
  `EchoCanonicalIdentitySuite`. Two consolidation narratives
  `docs/echo-types/{universal-property,fibration-package}.adoc`.
  Retraction follow-up F-2026-05-27a logged in `docs/retractions.adoc`.
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
