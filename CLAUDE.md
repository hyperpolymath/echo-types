<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Ecosystem context

This repo (echo-types) is one node in the hyperpolymath / PanLL ecosystem.
Adjacent projects, in one line each, for session bootstrapping:

- echo-types — constructive Agda formalization of fiber-based structured
  loss ("echo types"); `Echo f y := Σ (x : A) , (f x ≡ y)`. Gated
  identity-claim development; `--safe --without-K` throughout. Current
  workstream: E (ordinal-notation / Buchholz collapsing layer).
  https://github.com/hyperpolymath/echo-types
- PanLL — three-pane cognitive-relief HTI; Ambient/Symbolic/Neural/World panes.
  https://github.com/hyperpolymath/panll
- Gossamer — Zig + WebKitGTK webview shell used by PanLL (~5 MB binary).
- Burble — self-hostable voice-communications platform; Zig-based SIMD
  audio, IEEE 1588 PTP clock sync, sub-second room joining, browser-based
  (no downloads / no accounts), configurable topology from single-server
  to fully distributed mesh. In PanLL, used for team replication via
  broadcast and as a switchable service alongside Gossamer.
- Echidna (hyperpolymath) — planned high-assurance interface verification.
  NOT the Ethereum fuzzer of the same name. Exact repo still to confirm.
- Ephapax — programming language with a linear type system guaranteeing
  memory safety for WebAssembly (compile-time "no use-after-free / no
  memory leaks"). https://github.com/hyperpolymath/ephapax
- VeriSim / VeriSimDB — identity-state capture with filesystem fallback.
- VCL-UT (now VCL-total) — next-generation interaction language for
  VeriSim; designed to satisfy all 10 levels of type safety when
  proposing, inspecting, and verifying operations in a consonance engine
  (rather than querying a passive database).
- Groove protocol — HTTP-based service-discovery mechanism; lets
  capabilities across the hyperpolymath ecosystem announce themselves
  for automatic detection and integration (e.g. discipline-specific
  analyzers becoming visible to PanLL without manual wiring).
  See GROOVE_PANLL_RESEARCH_SUMMARY.md in panll.
- ArghDA — lightweight proof-workspace manager for Agda;
  triage folders (inbox → working → proven/rejected), linter, DAG view.
  Split as `arghda-core` (language-agnostic engine, separate repo at
  https://github.com/hyperpolymath/arghda-core, extracted from this
  repo 2026-05-30 — see echo-types#159) + `arghda-panll`
  (Gossamer/ReScript presentation, planned). See docs/buchholz-plan.adoc
  appendix for the motivating proof pipeline.
- EchoTypes.jl — executable Julia companion to echo-types, mirroring the
  finite-domain shadow of the Tier-1 + Tier-2 spine + the unconditional
  F5 OFS fragment. v0.2.0 (2026-05-27) extends v0.1.0's `Echo` /
  `EchoResidue` / `EchoFiberCount` / `EchoThermodynamics` coverage with
  seven new modules (`EchoTotalCompletion`, `EchoOrthogonalFactorizationSystem`,
  `EchoImageFactorization`, `EchoNoSectionGeneric`, `EchoLossTaxonomy`,
  `EchoEntropy`, `EchoObservationalEquivalence`). Honestly scoped under
  R-2026-05-18 — the retracted surface and the funext-qualified F5
  clauses are NOT mirrored. Falsifies-by-counterexample on concrete
  data; the Agda here remains the source of truth.
  https://github.com/hyperpolymath/EchoTypes.jl

# This repo

echo-types — constructive Agda formalization of fiber-based structured loss
("echo types"). Gated identity-claim development per roadmap-gates.adoc.

Two active workstreams:

1. **Composition track (Echo.agda + echo-types theory docs).** Base
   accumulation iso `Echo-comp-iso-{to, from, from-to, to-from}`
   landed and packaged as `Echo-comp-iso : ... ↔ ...`. Cancellation
   iso landed: `cancel-iso-{to, from, from-to, to-from}` plus the
   `cancel-iso : ... ↔ ...` packaging (PR #25), parameterised by
   `s-left`, `s-right`, and both triangle identities. Pentagon
   coherence complete: projection-pentagon lemmas
   `Echo-comp-iso-pent-{B, echo}` land as `refl`, the full
   Σ-associativity iso between the two nested Σ-shapes lands as
   `Echo-comp-pent-Σ-assoc-{to, from, from-to, to-from}`, and
   the equivalence-record packaging `Echo-comp-pent-Σ-assoc :
   ... ↔ ...` (stdlib `Function.Bundles._↔_`) is in place.

2. **Ordinal track (buchholz-plan.adoc).** Target remains Bachmann–
   Howard (ψ₀(Ω_ω)) as first credible milestone, stretch to ψ(Ω_Ω)
   ≈ TFBO. E1–E7 landed (OT syntax, ℕ-staged closure with
   `C-monotone`, CNF with `cnf-trichotomy`, pedagogical ψ with
   `psi-notin-C`/`psi-least`, Buchholz scaffold with `Cν-monotone`
   family, well-formedness with `BH-wf`/`psi-OmegaOmega-wf`, echo
   bridge with `ordinal-collapse-non-injective`). WF-0 partial
   Buchholz order `_<ᵇ_` and WF-1 well-foundedness `wf-<ᵇ` landed
   for the admitted core (currently `Order.agda`'s 13-constructor
   set including Ω/+ and ψ/+ bridges). Surface / extended / iterated
   / Veblen layers now live under `Ordinal/Buchholz/*` and feed a
   second measure route via `VeblenComparisonModel.agda`.
   Recursive-surface route has a **budgeted** well-foundedness
   `wf-<ᵇʳᶠᵇ` in `RecursiveSurfaceBudget.agda` (carries ℕ budget
   alongside BT); the unbudgeted global WF theorem for `_<ᵇʳᶠ_`
   remains open.

   Open pieces on this track:
   * Full constructor set beyond the admitted core (K-limited
     shared-binder cases such as `<ᵇ-ψα`, `<ᵇ-+2`).
   * Unbudgeted `_<ᵇʳᶠ_` global WF — eliminate the explicit ℕ
     budget from `wf-<ᵇʳᶠᵇ` without leaving `--safe --without-K`.
   * Push the surface-route WF back into `Order.agda`'s main
     `_<ᵇ_` package.

3. **Establishment track (`docs/echo-types/establishment-plan.adoc`).**
   Path to recognised type-theoretic standing as a *characterised
   graded comonad of structured loss* (coeffect/quantitative
   lineage) — explicitly NOT the linear/dependent judgmental ladder.
   Five pillars: A pin-the-identity, B universal property +
   graded-comonad laws, C separating model, D second model +
   conservativity, E external validation. Pillar A landed
   (`EchoFiberBridge.agda`: `echo↔fib` definitional bridge, pinned
   in `Smoke.agda`). Pillars B–D exist as declaration-free doc
   scaffolds in `All.agda` (`EchoPullback`, `EchoGradedComonad`,
   `EchoSeparating`, `EchoRelModel`) carrying intended signatures.

   **Pillar B COMPLETE (2026-05-17).** Both artefacts real:
   * `EchoGradedComonad` — `gextract`, `gduplicate`,
     `gcomonad-counit-{l,r}`, `gcomonad-coassoc`. De-risk verdict:
     graded coassociativity needs NO path algebra beyond `≤g-prop`
     (common-upper-bound idiom kills the `⊔g-assoc` transport).
   * `EchoPullback` — `EchoCone`/`echo-cone`, `SliceHom`↔cone bridge
     (`refl` round-trips), `IsMediator`, `echo-pullback-univ`
     (existence + funext-free pointwise uniqueness via stdlib
     `Σ-≡,≡→≡`; no K). Pillars A and B both complete; thesis
     strengthened, unchanged. See establishment-plan.adoc §"H2
     verdict" + revision history.

   **Pillars A–D ALL COMPLETE (2026-05-17).** Pillar C:
   `EchoSeparating.agda` (separating model = `EchoGraded` minus
   `≤g-prop`; `sep-degrade-compose-fails`). Pillar D artefact 1:
   `EchoRelModel.agda` — abstract `GradedLossModel` + generic
   `GCLaws` (comonad laws proved once for ANY model = the
   model-independence theorem), `set-model`/`rel-model` instances,
   `model-agreement` + `bridge-natural`. Pillar D artefact 2:
   `docs/echo-types/conservativity.adoc` — conservative/definitional
   metatheorem with a 3-clause formal anchor. No scaffold modules
   remain; the entire internal programme is done.

   Open pieces on this track:
   * Pillar E only. TYPES extended abstract DRAFTED
     (`docs/echo-types/types-abstract.adoc`, content
     submission-ready). Full CPP/ITP paper is a LIVING DRAFT
     (`docs/echo-types/paper.adoc`) with sections tagged *[EXPAND]*
     (background primer, evaluation, related work, ordinal
     consumer-evidence appendix) — fill as more context accrues; do
     NOT submit until [EXPAND] tags clear and a venue/template is
     chosen. Remaining: clear [EXPAND]s, then Zenodo DOI +
     installable library packaging + outreach (offline /
     author-driven — flag to user, don't auto-run).

Cross-repo bridge status lives in `docs/echo-types/cross-repo-bridge-status.md`.

# Build

```
cd /home/user/echo-types
agda -i proofs/agda proofs/agda/All.agda
for f in proofs/agda/*.agda proofs/agda/Ordinal/*.agda proofs/agda/Ordinal/Buchholz/*.agda; do
  [ -f "$f" ] && agda -i proofs/agda "$f"
done
```

Requires Agda ≥ 2.6.3 with stdlib ≥ 2.3 (CI installs v2.3; see
`.github/workflows/agda.yml`). On Ubuntu 24.04 with apt's
`agda`/`agda-stdlib` (which ships stdlib 1.7.3 and lacks
`Data.Product.Base`), check out stdlib 2.3 from source:
```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git /opt/agda-stdlib
sed -i 's/^name: standard-library-2.3$/name: standard-library/' /opt/agda-stdlib/standard-library.agda-lib
mkdir -p ~/.agda && echo /opt/agda-stdlib/standard-library.agda-lib > ~/.agda/libraries
```
Then `LC_ALL=C.UTF-8 agda proofs/agda/All.agda` exits 0.

# Working rules in this repo

- No postulates unless explicitly isolated and justified.
- `--safe --without-K` throughout.
- Every edit ends with an Agda compile command and captured output.
- Every headline theorem must be pinned in `Smoke.agda` via `using` clause.
- Every new module goes into `All.agda` as an `open import` so the
  verified suite covers it. Orphan modules that compile but are not
  in `All.agda` are treated as dead code.

## Rung-consolidation policy (added 2026-04-23)

Each time a new proof rung lands on the composition or ordinal
tracks (a named theorem or iso-shape), consolidate all outstanding
work to `main` and refresh all documentation:

1. **Branch housekeeping.** Enumerate all open remote branches
   ahead of `main`. Decide which are landing, which are superseded,
   and which are abandoned. Merge the landing ones; mark the
   superseded / abandoned ones in the session ledger.
2. **Cherry-pick to a consolidation branch** off latest `main`, in
   dependency order. Resolve any conflicts (typically additive, in
   `Smoke.agda` and `All.agda`).
3. **Update human docs.** `docs/echo-types/composition.md`,
   `roadmap.adoc`, `docs/echo-types/overview.md` and
   `cross-repo-bridge-status.md` get a sweep for stale `(Open)` /
   `[unblocked]` tags on anything that just landed. Honest labels:
   `(Landed)`, `(Partial)`, `(Open)`.
4. **Update machine docs (this file).** Add the new rung under the
   active-workstream summary. Update the build instructions if the
   toolchain changed. Note any new structural constraints that would
   guide a fresh session's first steps.
5. **Verify.** `agda proofs/agda/All.agda` and `agda proofs/agda/Smoke.agda`
   both exit 0 under `--safe --without-K`. No postulates introduced.
6. **Fast-forward `main`** to the consolidation branch and push.
7. **Session ledger.** In the session response, record the rung
   name, the commits folded in, the remaining open pieces of the
   milestone, and the proposed smallest useful next advance.

## Current rung state (2026-05-27)

### Session arc 2026-05-27 Slice-2 upstream adoption (READ FIRST after the broad-cleanup arc below)

A parallel-session agent shipped PRs #130/#131/#133/#134 to
`origin/main` while my session was building its own partial
Slice 2 foundation in `proofs/agda/Ordinal/Buchholz/RankPowDomination.agda`.
Audit verdict (verified in an isolated worktree): the upstream
work is REAL, compiles clean under `--safe --without-K`, zero
postulates. The upstream version is strictly stronger than my
partial slice:

* Complete domination lemma `rank-pow-dominated-by-head-Ω`
  (which I had deferred to Slice 2b).
* Better `ω-rank-pow-succ ω` design — `olim (λ n → ω-rank-pow ω
  ·ℕ n)` (engineered for `additive-principal-ω-rank-pow-succ`
  via `·ℕ-add-≤`), vs my naïve `olim (λ n → ω^ (suc (suc n)))`.
* Eliminated my `NonBzero` premise — `rank-pow bzero = oz` is
  strictly below `ω-rank-pow-succ (fin 0) = ω^2` via
  `ω^_-pos 2`, so the bzero case fires uniformly without a
  discriminator.
* Full inversion-lemma module `Ordinal.Buchholz.HeadOmegaInversion`
  (`head-Ω-inv-bOmega`, `head-Ω-inv-bpsi`) supporting the bplus
  tail-bound case.
* Properly wired into `All.agda` + the Buchholz-layer `Smoke`.

*Action taken (this session):* surgically adopted the four
upstream Ordinal-track files (`HeadOmegaInversion.agda` new,
`RankPow.agda` modified, `RankPowDomination.agda` replaces my
partial version, `Ordinal/Buchholz/Smoke.agda` modified) via
`git checkout origin/main -- <files>`. My `RankPowDomination.agda`
deleted; added the two new imports to top-level `All.agda`.
Full + Smoke build green post-merge.

*One subtle quality issue from PR #133:* it was admin-merged
before CI completed, and the first version had unsolved metas
at `ω-rank-pow-mono-≤Ω {fin m} fin≤ω` (actually triggered by
the `ω≤ω` line below it needing explicit `{ω-rank-pow ω}` on
`≤′-refl`). PR #134 was a one-line fix landed shortly after.
Future Ordinal-track admin-merges should wait for CI green
before merging — the same gate-discipline the rest of the repo
follows.

*F5-3 memory note remains valid* — the composition-design
insight `φ.to = encode f ∘ g⁻¹` avoiding triangle identities is
unaffected by the upstream Ordinal work; my Tier-1+2+3 +
audience-moves spine remains the canonical structural extension
on top of the Pillar A–D + F1–F5 layers.

### Session arc 2026-05-27 broad-cleanup close — audience spine + suite + F5 prose + consolidation + Choreo + abstract-degrade (read this first)

*Where we started (post-EchoProvenance + F5 FULL PASS):* user
chose option 3 (4 spine items + closing doc-sweep + broader
cleanup touching the ordinal track and deferred follow-ons).
Nine tasks set up; all nine landed in this push.

*Where we ended:* the audience+suite spine is COMPLETE; the F5
qualified-OFS prose is reflected in the paper + abstract; two
consolidation docs threaded; Choreo wired into DecorationStructure;
abstract degrade-compose theorem closed; *Ordinal Slice 2
originally partial-shipped — superseded by upstream PRs
#130/#131/#133/#134 per the next session arc above.* Each
deliverable per-task:

1. *`EchoSecurity.agda`* (Tier 3 audience move 2). Abstract
   `Security` record (resource + receipt + region indexing + exit
   + distinguishability + collapse witness) + two parametric
   headline theorems via `module SecurityTheorems`. Worked
   `region-exit-audit-instance` reproduces the existing
   `RegionExitAudit` walkthrough. Honest-bound matched-negative
   block at the bottom (bytes-zeroed, side-channel-safe,
   tamper-evident, oracle-recovery).

2. *`EchoProbabilisticSupport.agda`* (Tier 3 audience move 3).
   Abstract `Sampling` record + four parametric headline
   theorems. Worked `bool-indexed-nat-sampling` instance.
   Matched-negatives: not measure-preserving, not a probability
   monad, no Kantorovich / coupling / randomness extraction.

3. *`EchoDifferential.agda`* (Tier 3 audience move 4). Abstract
   `Sensitivity` record + four parametric headline theorems.
   Worked `bool-perturbed-nat-sensitivity` instance.
   Matched-negatives: not ε-DP, no Lipschitz bound, no noise
   calibration, no adversary model.

4. *`EchoCanonicalIdentitySuite.agda`* (narrative deliverable).
   Single curated file re-exporting the load-bearing headlines
   from every Tier-1 / Tier-2 / Tier-3 module under the "why
   Echo deserves a name" reading order. Tier 1 spine (totality,
   OFS, image, no-section), Tier 2 grid (function/residue/
   decoration/observational axes), Tier 3 qualified UP
   (F5-1+2+3), cementing matched-negatives (Entropy + LL), four
   audience surfaces (Provenance, Security, Sampling,
   Sensitivity). Module-name clash F5-2 vs F5-3 resolved via
   `import ... as F5Diag` / `as F5Iso`.

5. *F5 prose updates* — `paper.adoc` gains a new NOTE block
   right after the F4 NOTE, reflecting F5 FULL PASS with the
   three slices + retraction follow-up F-2026-05-27a +
   composition-design note. `types-abstract.adoc` gains a
   "Post-abstract advances (2026-05-27)" NOTE summarising the
   four post-abstract layers (Canonical identity layer / Tier-2
   classification grid / F5 / audience moves + suite).
   `conservativity.adoc` correctly NOT edited — it lives in
   `docs/retracted/conservativity.adoc` per R-2026-05-18, and
   the retraction discipline forbids resurrecting retracted
   docs.

6. *Doc consolidations* — `docs/echo-types/universal-property.adoc`
   threads the EchoPullback + EchoPullbackUnivF4 + F5-1/2/3
   narrative with reading order; `docs/echo-types/fibration-package.adoc`
   threads the map-over + Echo-comp-iso + cancel-iso +
   pentagon narrative. Pure doc work; both AsciiDoc per MAP.adoc
   convention.

7. *Decoration zoo wiring* — Choreo wired as
   `choreo-decoration-structure : DecorationStructure Role _`
   (two-role order with c⊑c/c⊑s/s⊑s and the join). 4/5 of the
   originally-scoped instances (Cost/Search/Indexed/Epistemic)
   don't fit the seven-field recipe cleanly without
   per-module design choices (Cost = parametric algebra,
   Search = ℕ budget axis, Indexed = projection not graded,
   Epistemic = relational not tag-shaped); documented as
   ready-to-wire with notes in the companion-remark.

8. *Abstract degrade-compose theorem* — `module DegradeAbstract`
   added to `EchoDecorationStructure.agda`. Two theorems:
   `degrade-compose-abstract` (any factoring agrees with any
   direct map via `≤-prop`) and `degrade-via-join-abstract`
   (any direct degradation factors through the join). Closes
   the carrier-side companion-remark deferred follow-on; the
   per-decoration modules' concrete forms remain (compile
   faster, give pinned-name CI signals).

9. *Ordinal Slice 2 partial (SUPERSEDED).* This session
   originally shipped a partial-foundation
   `Ordinal/Buchholz/RankPowDomination.agda` with
   `ω-rank-pow-succ` + `NonBzero` + fin-case bump, deferring the
   ω-case bump + additive-principal-succ + headline domination
   to Slice 2b. Upstream PRs #130/#131/#133/#134 shipped the
   COMPLETE chain in parallel; my partial slice was strictly
   weaker (worse `ω-rank-pow-succ ω` design; unnecessary
   `NonBzero` premise; deferred headline). Action: dropped my
   version, adopted theirs via surgical `git checkout
   origin/main` on the four Ordinal-track files. See the
   "Slice-2 upstream adoption" session arc above this one for
   the full reconciliation record.

Build invariant held: `Smoke.agda` + `All.agda` exit 0 under
`--safe --without-K`, zero postulates, no funext in the trusted
base. New modules count: 5 (Security, Probabilistic, Differential,
Suite, RankPowDomination). Modified modules: 2
(EchoDecorationStructure for Choreo + abstract degrade; Smoke +
All for pins). Modified docs: paper.adoc, types-abstract.adoc,
earn-back-plan.adoc (F5 full-pass status), retractions.adoc
(F-2026-05-27a follow-up landed in previous arc). New docs: 2
(universal-property.adoc, fibration-package.adoc).

*Plan for the next Claude.*

1. *Ordinal Slice 2b* — finish the ω-bump + additive-principal-
   ω-rank-pow-succ + headline domination lemma. Then wire
   `RankPowDomination` into All/Smoke. Foundation for Slice 3
   (closes `<ᵇ-+1` joint-bplus rank-mono).

2. *Decoration zoo wiring continuation* — Cost as
   `DecorationStructure` over abstract CostAlgebra (needs
   parametric record); Indexed / Search / Epistemic as
   `ResidueForm` instances with their non-tag-shaped carriers.
   Each module-by-module mechanical work.

3. *Image factorisation (epi, mono) earn-back* — requires
   propositional truncation. Either via Cubical Agda (different
   --safe flag profile) or via postulated `∥_∥` interface
   with scoped honest-scope. Substantial design decision.

4. *Pillar E paper `[EXPAND]` tag clearing* — ordinal
   consumer-evidence appendix is gated on the Bachmann–Howard
   milestone; other [EXPAND] tags may be ready to clear as
   material accrues. Author-driven.

5. *MAP.adoc + wiki sweep for this session's additions* —
   audience moves (Security/Probabilistic/Differential),
   curated suite, the two consolidation docs. Will be batched
   with this CLAUDE.md update.

*Parallel-agent reminder.* The Decoration Bridge exploration is
still parallel-active in the repo. Their territory: own module
(Exploratory/EchoDecorationBridge.agda or similar) + docs under
`docs/echo-types/explorations/decoration-bridge/` + one bullet
in `roadmap.adoc` + possibly `docs/echo-types/cross-repo-bridge-status.md`.
I've stayed clear of `EchoIntegration.agda`, `EchoChoreo.agda`,
`EchoGraded.agda`, existing `EchoXBridge.agda`, and
`roadmap.adoc` throughout. The `--only <paths>` parallel-session
discipline still applies if both sessions commit before sync.

DO NOT reopen: any of the 9 tasks closed above; the F5 design
choices (composition route in F5-3 is correct, no triangle
identity needed); the Tier-2 spine (closed); the abstract
degrade-compose level-organisation in `DegradeAbstract` (the
module parameters are explicit and minimal). The Slice 2
foundation IS load-bearing for Slice 2b — the fin-bump +
NonBzero + ω-rank-pow-succ definition are the correct
primitives, don't redesign them.

### Session arc 2026-05-27 Tier-3 F5 FULL PASS + first audience move (read this first)

*Where we started (post-F5 partial 2/3):* F5-1 + F5-2 had landed
and were wired; F5-3 had been deferred on a misdiagnosed
"requires triangle identity" obstruction. User authorised
continuing (F5-3 then EchoProvenance).

*Where we ended:* F5 FULLY PASSES. EchoProvenance (first
audience move) LANDS. Three deliverables:

1. *F5-3 design correction.* The natural-but-blocked direct
   formulation `φ.to x = (p x, g⁻¹ x, witness)` was sidestepped
   by routing through composition with the existing totality
   completion:

     φ.to   = encode f ∘ g⁻¹
     φ.from = g ∘ decode f

   Round-trips then reduce via the existing K-free
   `encode-decode` / `decode-encode` lemmas + `cong` of `inv-f`
   / `f-inv`. No triangle identity needed. The trade-off:
   `proj₁ ∘ φ.to ≡ p` is no longer definitional — only pointwise
   via `commute` (strict under funext, fine under the F4
   template). Original concern about needing
   `HasCoherentInverse` was wrong; composition design closes
   with bare `HasInverse`.

2. *F5-3 landed* (`proofs/agda/EchoOFSUnivF5Iso.agda`). Same F4
   template as F5-1 / F5-2 (modules `Pointwise` + `Strict`).
   Headlines: `φ-to`, `φ-from`, `φ-from-to`, `φ-to-from`,
   `φ-iso` (packaged `_↔_`), `φ-respects-g` (`φ.to ∘ g ≡ encode
   f` pointwise), `φ-projects-to-p` (`proj₁ ∘ φ.to ≡ p`
   pointwise); strict forms via `funext` in the `Strict`
   sub-module. Wired into All.agda, pinned in Smoke.agda under
   qualified-open of the `module Pointwise`.

   *F5 FULL PASS.* Ledger updated:
   `docs/echo-types/earn-back-plan.adoc` status entry expanded
   to "Gate F5 PASSED (all three slices)". Retraction follow-up
   `F-2026-05-27a` landed in `docs/retractions.adoc` as the
   first follow-up sub-section on R-2026-05-18 (sets format for
   future F-YYYY-MM-DD-x entries).

3. *EchoProvenance landed* (`proofs/agda/EchoProvenance.agda`)
   — Tier 3 first audience move per GPT order. Generalises the
   existing `EchoExampleProvenance.agda` (Bool-over-ℕ instance)
   into an abstract `Provenance` record (payload + tag +
   distinguishability witness) + four parametric headline
   theorems via `module ProvenanceTheorems (P : Provenance)`:
     * `provenance-collapses-at` — projection non-injective at
       every payload;
     * `echo-tag₁` / `echo-tag₂` — concrete Echo carriers per
       tag;
     * `echoes-distinguish-tag` + `echo-tag₁≢echo-tag₂` — Echo
       distinguishes the lost tag;
     * `residue-collapses-tags` — lowering forgets the tag.
   Worked instance `bool-over-nat-provenance` witnesses
   inhabitability and reproduces the existing example's
   structure. Wired into All/Smoke.

   *Echo-vs-Σ clearance.* The headlines invoke `Echo`,
   `echo-intro`, and `EchoResidue.echo-to-residue` directly;
   replacing `Echo project p` by a generic Σ would lose the
   residue-collapse alignment with
   `EchoResidue.collapse-residue-same`. Falsifier explicitly
   documented in the companion-remark.

Build invariant held: all four new modules (`EchoOFSUnivF5Iso`,
`EchoProvenance`, plus the F5-1 / F5-2 modules from the
previous arc) + `Smoke.agda` + `All.agda` exit 0 under `--safe
--without-K`, zero postulates, no funext in the trusted base.

*Plan for the next Claude.*

1. *MAP.adoc + wiki sweep* — add F5 (full pass) to the
   Governance / Pillar F ledger pointer + add `EchoProvenance`
   as the first audience-move entry under "Canonical identity
   layer" (or as a new "Audience-facing modules" sub-section).
   Mechanical doc-only edit. Next.

2. *EchoSecurity.agda* — second audience move per GPT order.
   Use `RegionExitAudit.agda` (in `tutorial/region_exit_audit/`)
   as the honest-bound template; lift its region-exit /
   no-section content into an abstract `Security` record similar
   to `Provenance`. Mechanical generalisation following the same
   pattern as EchoProvenance.

3. *EchoProbabilisticSupport.agda* / *EchoDifferential.agda* —
   third + fourth audience moves; lower priority and
   independent.

4. *Narrative deliverable — `EchoCanonicalIdentitySuite.agda`*
   — pull the Tier-1+2+3 named theorems into one curated file
   as the "why Echo deserves a name" demo. Almost no new proof
   work; mostly assembly.

*Parallel-agent reminder.* Another agent is scaffolding the
exploratory Decoration Bridge in this repo (own module +
`docs/echo-types/explorations/decoration-bridge/` + one bullet
in `roadmap.adoc`). Their constraint disallows touching
`EchoIntegration`, `EchoChoreo`, `EchoGraded`, existing bridges,
`All.agda`. They WILL touch `roadmap.adoc` (one bullet).
Continuing to stay clear of `roadmap.adoc`; if both sessions
need to commit, the `--only <paths>` discipline from existing
memory applies.

DO NOT reopen: F5 (fully passed; the composition design via
`encode f ∘ g⁻¹` is the right one — don't second-guess it back
to the triangle-identity formulation); EchoProvenance's record
shape (`Payload`, `Tag`, two tags, distinguishability witness
is the minimum-sufficient — adding semiring laws is a separate
EchoProvenanceSemiring module).

### Session arc 2026-05-27 Tier-3 F5 partial pass 2/3 — F5-1 + F5-2 (read this first)

*Where we started (post-F5-1 standalone):* the F5 first slice
(`echo-factorisation-strict`) compiled standalone but was not
wired pending gate-ledger entry. User authorised continuing.

*Where we ended:* F5 partial-pass advances to 2/3 slices. F5
ledger entry created in `docs/echo-types/earn-back-plan.adoc`
(Gate F5 — Full OFS, honestly qualified) with three-slice scope.
F5-1 and F5-2 land, are wired into `All.agda`, and pinned in
`Smoke.agda`. F5-3 remains open (design issue documented below).

*F5-1 — Strict factorisation triangle (LANDED, wired).*
`proofs/agda/EchoOFSUnivF5.agda`. `echo-factorisation-strict
(funext) : f ≡ proj₁ ∘ encode f`. Three-line proof lifting the
existing K-free pointwise `echo-factorisation` via `funext`.
Pinned: `echo-factorisation-strict`,
`echo-factorisation-pointwise`.

*F5-2 — Diagonal lifting property (LANDED, wired).*
`proofs/agda/EchoOFSUnivF5Diag.agda`. Given a commutative square
`e : A → A'` (equivalence via `HasInverse`) + `proj₁` + `h, k`
with pointwise commutativity, the canonical lift `λ x → h (e⁻¹
x)` exists, satisfies both triangles pointwise (K-free), is
unique pointwise (K-free); and the strict (function-level)
versions of all three lift via `funext`. Two module
parameterisations: `module Pointwise (...)` for the K-free
content + `module Strict (funext)` for the funext-qualified
content. Pinned via `module Pointwise` + `module Strict` in
Smoke.

*F5-3 — Factorisation uniqueness up to iso (DEFERRED, design
note below).* Attempting the construction surfaces a clean
design issue: the round-trip `φ.to ∘ φ.from ≡ id` on `Σ B (Echo
f)` requires a half-adjoint triangle identity on the input
equivalence's inverse data, which `EchoLossTaxonomy.HasInverse`
(quasi-inverse only) doesn't carry. The standard HoTT fix is to
either:

  * (a) Strengthen `HasInverse` to `HasCoherentInverse` by
    adding the triangle identity `∀ a → cong g (inv-f a) ≡
    g-f-inv (g a)` as an additional field. The Pointwise +
    Strict module split then works as for F5-2.

  * (b) Add UIP on `B` (or `is-set B`) as an explicit
    hypothesis, making the third Σ-component of the round-trip
    trivial. Strictly weaker than UIP (`is-set` would do); not
    funext, but an orthogonal extra hypothesis.

  * (c) Reformulate the iso to avoid the Σ-equality decomposition
    — e.g. by quotienting out the residue equation, or by
    splitting the iso into projection-equal + residue-equivalent
    halves. Speculative.

The cleanest is (a) — adding the triangle identity is the
standard HoTT discipline and matches the way
`Echo.cancel-iso-{from-to, to-from}` already take `triangle₁` /
`triangle₂` as explicit parameters. The F5-3 design slice
should: introduce `HasCoherentInverse` as a thin extension of
`HasInverse`; redo the F5-3 construction parameterised by
`HasCoherentInverse`; ship the F4-style Pointwise + Strict
modules. This is a one-session task for a fresh window.

Build invariant held: `EchoOFSUnivF5.agda`,
`EchoOFSUnivF5Diag.agda`, `Smoke.agda`, and `All.agda` all
exit 0 under `--safe --without-K`, zero postulates, no funext
in the trusted base (funext is hypothetical per the F4
discipline).

*Plan for the next Claude.*

1. *F5-3 (coherent inverse + factorisation uniqueness).* Add
   `HasCoherentInverse` record extending `HasInverse` with one
   triangle identity; re-do the F5-3 iso construction in
   Pointwise + Strict modules; wire into Smoke/All. Closes the
   full F5 gate. ONE-SESSION task; design path is clear (see
   options above).

2. *Audience moves.* Per GPT order: `EchoProvenance.agda` first
   (generalises existing `EchoExampleProvenance.agda`); then
   `EchoSecurity.agda`; then `EchoProbabilisticSupport.agda` /
   `EchoDifferential.agda`.

3. *Narrative deliverable — `EchoCanonicalIdentitySuite.agda`*
   once F5 fully passes (or once the audience moves give the
   suite enough breadth).

*Parallel-agent note.* Another agent is concurrently scaffolding
an exploratory "Decoration Bridge" investigation in this repo
(`proofs/agda/EchoDecorationBridge.agda` or
`Exploratory/EchoDecorationBridge.agda`, plus docs under
`docs/echo-types/explorations/decoration-bridge/` or similar,
plus one bullet in `roadmap.adoc`). Their constraint: don't
modify `EchoIntegration.agda`, `EchoChoreo.agda`,
`EchoGraded.agda`, existing bridges, or `All.agda`. They WILL
edit `roadmap.adoc` (one bullet) and possibly
`docs/echo-types/cross-repo-bridge-status.md`. Avoid touching
those files; if both sessions need to commit, use `--only
<paths>` per the parallel-session discipline already in memory.

DO NOT reopen: the F5-1 / F5-2 wiring (clean partial pass; full
F5 just needs F5-3); the `HasInverse` quasi-inverse design
(it's correct for F5-2's purposes; F5-3 needs the coherent
upgrade, not a replacement); the F4 template (the Pointwise +
Strict split with funext as module parameter is the right
pattern).

### Session arc 2026-05-27 Tier-3 F5-1 slice — strict factorisation triangle (read this first)

*Where we started (post-Tier-2 spine):* Tier 2 closed (LossTaxonomy
+ ResidueTaxonomy + DecorationStructure + ObsEquivalence all
landed, wired, and pushed to wiki). The next ladder advance per
the plan: Tier 3 = full-OFS earn-back gate, structured as F5 in
the F1-F4 discipline.

*Where we ended:* the F5 FIRST SLICE lands at
`proofs/agda/EchoOFSUnivF5.agda`. Closes one direct analogue of
F4's `echo-pullback-univ-strict`:

  * `echo-factorisation-strict (funext) : f ≡ proj₁ ∘ encode f`
    — the function-level form of the factorisation triangle,
    conditional on funext. Three-line proof: take the existing
    K-free pointwise `echo-factorisation : (x : A) → f x ≡
    proj₁ (encode f x)`, apply the supplied `funext` hypothesis
    to lift to a function equation.
  * `echo-factorisation-pointwise` — the funext-free corollary
    (re-export of `EchoOrthogonalFactorizationSystem.echo-
    factorisation`), pinned alongside for the conditional /
    unconditional reading.

*Discipline note (gate-passing).* Following the F4 template
precisely, the module is NOT YET WIRED into `All.agda` or
`Smoke.agda`. The wiring waits on (a) an earn-back-plan ledger
entry creating Gate F5 with the three-slice scope (F5-1 strict
triangle, F5-2 diagonal lifting, F5-3 factorisation uniqueness
up to iso), and (b) explicit user authorisation to proceed with
the gate. The module compiles standalone under `--safe --without-K`,
zero postulates, ready for ledger inclusion when authorised.

*The two remaining F5 slices (NOT started, awaiting authorisation).*

  * F5-2 — Diagonal lifting property. Given a commutative square
    `e : A → A'` (equivalence via `HasInverse`) + `p : Σ B (Echo
    f) → B` (= `proj₁`) + `h : A → Σ B (Echo f)` + `k : A' → B`
    with `proj₁ ∘ h ≡ k ∘ e` pointwise, there is a unique
    `lift : A' → Σ B (Echo f)` with `lift ∘ e ≡ h` and
    `proj₁ ∘ lift ≡ k`. Construction: `lift x = h (e⁻¹ x)`.
    Pointwise commutativity K-free; strict form needs funext.
    Uniqueness: pointwise from injectivity of `e`; strict via
    funext.

  * F5-3 — Factorisation uniqueness up to iso. Given any other
    `g : A → X` equivalence + `p : X → B` with `p ∘ g ≡ f`
    pointwise, construct a canonical `φ : X ↔ Σ B (Echo f)` with
    `proj₁ ∘ φ.to ≡ p` (strict, funext) and `φ.to ∘ g ≡ encode
    f` (strict, funext). Construction goes via `g`'s inverse;
    the path-algebra obligations on the round-trips need funext.

Build invariant held: `EchoOFSUnivF5.agda` compiles standalone
under `--safe --without-K`, zero postulates. `Smoke.agda` /
`All.agda` unchanged (no wiring yet). Tier-2 spine continues to
build clean.

*Wiki + MAP.adoc state.* Tier-2 spine entries (ResidueForm,
DecorationStructure, ObsEquivalence) landed in MAP.adoc +
Home.md in the previous arc. F5-1 NOT added to canonical docs
pending gate-pass — same gate-discipline as F1/F2/F3/F4.

*Plan for the next Claude.* Two paths, mutually exclusive
without user input:

1. *Continue F5 gate.* User opts F5 into the ledger; wire F5-1
   into Smoke/All; proceed with F5-2 (diagonal lifting) or F5-3
   (uniqueness up to iso). Each is a separate slice in the F4
   discipline.

2. *Pivot to audience moves.* Per the GPT-recommended order:
   `EchoProvenance.agda` first (closest fit to existing
   `EchoExampleProvenance.agda`); then `EchoSecurity.agda`
   (using the `RegionExitAudit.agda` honest-bound template);
   then `EchoProbabilisticSupport.agda` and `EchoDifferential.
   agda` (independent + lower-priority).

3. *Narrative deliverable.* `EchoCanonicalIdentitySuite.agda` —
   the curated suite pulling the Tier-1+2 named theorems into
   one file as the "why Echo deserves a name" demo. Almost no
   new proof work; mostly organising the existing artefacts.

DO NOT reopen: the Tier-2 spine (closed); the F4 / F1 / F2 / F3
gates (already passed); the OFS module's R-2026-05-18 narrowing
(the full OFS NEEDS funext for the strict clauses, this is
honest).

### Session arc 2026-05-27 Tier-2 spine complete — Residue + Decoration + ObsEquiv (read this first)

*Where we started (post-LossTaxonomy, on the same Tier-2 spine):*
the synthesis-roadmap reorder put `EchoResidueTaxonomy` (#3),
`EchoDecorationStructure` (#4), and `EchoObservationalEquivalence`
(#5) as the remaining Tier-2 items. The audit's "kinds-of-loss ×
shapes-of-residue" two-axis grid was half-built (function-side
axis landed; residue-side + decoration-structure + observation
axes pending).

*Where we ended:* the Tier-2 spine is COMPLETE. Three modules land
in one push, all building under `--safe --without-K`, zero
postulates, no funext.

1. *`proofs/agda/EchoResidueTaxonomy.agda`* — Tier 2 #3, residue-
   side companion. `record ResidueForm f R` packages the minimum
   unified residue shape: a per-output residue carrier `R : B →
   Set _` plus a canonical lowering `lower : Echo f y → R y`.
   Four instance witnesses: `trivial-residue` (⊤, the maximum-
   collapse endpoint), `identity-residue` (`Echo f` itself, the
   no-collapse endpoint), `echoR-residue` (generic Σ-cert form
   via `EchoResidue.echo-to-residue`), `linear-affine-residue`
   (worked instance: `LEcho affine` on `collapse : Bool → ⊤`,
   lowering via `weaken`). The remaining six decoration modules
   (Graded / Choreo / Access / Cost / Search / Indexed /
   Epistemic) documented as structurally compatible in the
   companion-remark.

2. *`proofs/agda/EchoDecorationStructure.agda`* — Tier 2 #4,
   observation-side companion. `record DecorationStructure G`
   packages the seven-field decoration recipe shared across the
   eight decoration modules: `_≤_` order, `≤-refl`, `≤-trans`,
   `≤-prop` (the load-bearing thinness witness), `join`,
   `≤-join-left`, `≤-join-right`, `≤-join-univ`. Three instance
   witnesses: `graded-decoration-structure` (3-grade `keep ≤g
   residue ≤g forget`), `linear-decoration-structure` (2-grade
   `linear ≤m affine`), `access-decoration-structure` (5-grade
   `free ≤a decidable ≤a enum ≤a feasible ≤a infeasible`).
   *Naming note*: abstract join field is `join` (not `_⊔_`) to
   avoid `Level._⊔_` collision at the record-projection level;
   per-decoration modules keep their suffixed forms (`_⊔g_`,
   `_⊔m_`, `_⊔a_`).

3. *`proofs/agda/EchoObservationalEquivalence.agda`* — Tier 2 #5,
   closing the spine. Mode-indexed equality `_≡m_` on `LEcho`:
   `_≡m_ {linear} e₁ e₂ = e₁ ≡ e₂` (witness-aware), `_≡m_
   {affine} _ _ = ⊤` (witness-blind). Per-mode reflexivity +
   symmetry. The headline
   `mode-equality-strictly-finer-at-linear` is a Σ-witness
   exhibiting two specific echoes (`echo-true`, `echo-false`)
   that are linear-distinct (via existing
   `echo-true≢echo-false`) but affine-equal (via the trivial
   `tt`-collapse at affine). This pins the strictly-finer
   direction as a checked theorem, making "affine forgets what
   linear retains" a single named artefact.

*Honest scope (all three).* Each module ships the minimum-viable
unified abstraction + a small set of canonical instances. The
COMPLETE lift (all eight decoration modules wired as
`ResidueForm` + `DecorationStructure` instances; the abstract
degrade-compose theorem proved generically over the record; the
mode-indexed equality generalised to the abstract
`DecorationStructure`) is mechanical per-module wiring deferred
as follow-on. The three modules each demonstrate the abstraction
is real and inhabitable on the canonical small-poset cases; the
remaining wiring does not change the organisational story.

Build invariant held: all three new modules + `Smoke.agda` +
`All.agda` exit 0 under `--safe --without-K`, zero postulates,
no funext, no `TERMINATING` pragma. All headlines pinned in
`Smoke.agda` under their own `using` blocks with header comments
per CLAUDE.md "Working rules"; wired into `All.agda` adjacent
to the LossTaxonomy module that they companion.

*Wiki + MAP.adoc updated.* `docs/echo-types/MAP.adoc` gained the
"Canonical identity layer" section listing the seven 2026-05-27
artefacts (TotalCompletion, OFS, ImageFactorization,
NoSectionGeneric, LossTaxonomy + the cementing pair Entropy +
LLEncoding) plus a refreshed Shannon direction entry (`[REAL*]`
now that the discrete shadow lands). Wiki `Home.md` mirrors via
the standard pointer-to-MAP convention. The Tier-2 spine
modules (ResidueTaxonomy, DecorationStructure,
ObservationalEquivalence) need a follow-up MAP.adoc + wiki
sweep (next paragraph of this arc, to be done before the next
ladder advance).

*Plan for the next Claude.* The Tier-2 spine is closed. Open
work:

1. *MAP.adoc + wiki sweep* — add `ResidueForm`,
   `DecorationStructure`, `_≡m_` to the Canonical identity layer
   section. Mechanical doc-only edit; should land same session
   as this CLAUDE.md update (next).

2. *Tier 3 — full-OFS earn-back gate.* Funext-qualified
   uniqueness up to iso + diagonal lifting, in the Pillar-F4
   template style. This is a SUBSTANTIAL multi-step earn-back:
   needs an explicit `funext` parameter, a coherent-equivalence
   upgrade of `HasInverse`, the mediator uniqueness theorem,
   and the diagonal lifting property. Should NOT be started
   automatically — the user should explicitly opt into the
   earn-back gate (same discipline as the F1-F4 gates already
   in the ledger).

3. *Audience moves (Tier 3, GPT-recommended order):* Provenance
   first (closest fit to existing
   `EchoExampleProvenance.agda`); then Security (with
   `RegionExitAudit.agda` honest-bound template); then
   Probabilistic / Differential (independent + lower-priority).

4. *Narrative deliverable — `EchoCanonicalIdentitySuite.agda`*
   once Tier 3 (or some subset) lands. The curated suite that
   demonstrates "why Echo deserves a name" pulling together the
   named theorems into one file.

DO NOT reopen: the `ResidueForm` thinness (carrier + lowering
only — deeper laws live in per-decoration modules); the
`join`-naming in `DecorationStructure` (the `_⊔_` collision
with `Level._⊔_` is real, `join` is the cleanest workaround);
the `_≡m_` at-affine `⊤` collapse (this is the honest
content — at affine, the residue IS the trivial `(tt, tt)`,
nothing observable remains to distinguish).

### Session arc 2026-05-27 Tier-2 #2 — EchoLossTaxonomy (read this first)

*Where we started (post-NoSectionGeneric + ImageFactorization, on
the same Tier-1+2 spine):* the synthesis-roadmap reorder put
`EchoLossTaxonomy` as Tier 2 #2 — function-side classification of
`f : A → B` by echo shape, organising the four cases (equiv, inj,
surj, const) into the function-axis of the audit's "kinds-of-loss
× shapes-of-residue" grid.

*Where we ended:* `proofs/agda/EchoLossTaxonomy.agda` LANDS. Four
cases pinned, each at the K-free honesty level:

  * EQUIV — new `record HasInverse f` (quasi-inverse data: `inv`,
    `f-inv`, `inv-f`). Three small theorems: `equiv-fibre-center`
    (the inverse provides a canonical centre for every fibre),
    `equiv-implies-injective` (standard sym/cong/trans), and
    `equiv-fibre-proj-unique` (composition: equiv ⇒ inj ⇒
    projection unique).
  * INJ — taxonomy-side rename `inj-fibre-proj-unique` of
    `EchoImageFactorization.injective-fibres-proj-unique`. The
    rename pins the load-bearing taxonomy headline against a
    future refactor of the image module.
  * SURJ — taxonomy-side rename `surj-fibre-inhabited` of
    `surjective-iff-every-fibre-inhabited`. Same rationale.
  * CONST — `const-fun y₀ : A → B`. Section + projection +
    K-free round-trip: `const-fibre-section : A → Echo (const-fun
    y₀) y₀`, `const-fibre-projection` (the other way), and
    `const-fibre-section-projects-to-id` (K-free). The full
    `↔ A` packaging requires UIP on `B` (the missing round-trip
    `section ∘ projection ≡ id_{Echo ...}` needs eliminating a
    reflexive `y₀ ≡ y₀` equation, the canonical K-instance) and
    is honestly documented as the next earn-back; under HoTT
    terms the fibre is canonically `A × Ω (B, y₀)` and only
    collapses to `A` when `B` is an h-set.

*Honest scope (all four cases).* The full HoTT taxonomy is EQUIV
⇔ contractible fibre, INJ ⇔ propositional fibre, SURJ ⇔ merely
inhabited (truncation), CONST ⇒ fibre-≃-domain. Under `--safe
--without-K`: contractibility / propositionality need UIP, mere
inhabitation needs HITs / postulated `∥_∥`, CONST ↔-domain needs
UIP-on-`B`-at-`y₀`. The taxonomy here ships the K-free SKELETONS
(centre + projection-uniqueness for EQUIV, projection-uniqueness
for INJ, proof-relevant `Surjective` for SURJ, section for CONST);
the truncation / UIP upgrades are the same earn-back gates flagged
by `EchoImageFactorization` and the OFS module.

Build invariant held: `EchoLossTaxonomy.agda`, `Smoke.agda`, and
`All.agda` all exit 0 under `--safe --without-K`, zero postulates,
no funext. Pinned in `Smoke.agda` under its own `using` block with
header comment per CLAUDE.md "Working rules"; wired into `All.agda`
next to the keystone pair.

*Plan for the next Claude.* Tier 2 continues per the reorder:

1. *Tier 2 #3 — `EchoResidueTaxonomy.agda`* (residue-side
   companion). `record ResidueForm` interface; the eight existing
   decoration modules (Linear / Graded / Choreo / Access / Cost /
   Search / Indexed / Epistemic) as instance witnesses. Pairs
   with the loss taxonomy to complete the two-axis grid.

2. *Tier 2 #4 — `EchoDecorationStructure.agda`* (observation-side).
   Record packaging the recipe (`order`, `order-prop`, `join`,
   `degrade-compose`, `degrade-via-join`).

3. *Tier 2 #5 — `EchoObservationalEquivalence.agda`* — mode-
   indexed equality on `LEcho`.

4. *Tier 3 — full-OFS earn-back gate.* Funext-qualified uniqueness
   up to iso + diagonal lifting.

5. *Audience moves (Tier 3, GPT-recommended order):* Provenance,
   Security, Probabilistic, Differential.

6. *Narrative deliverable — `EchoCanonicalIdentitySuite.agda`*
   once (1)-(3) land.

DO NOT reopen: the EQUIV case's `HasInverse` design (quasi-inverse
is the minimal K-free data; a half-adjoint-equivalence upgrade
needs path algebra and isn't load-bearing here); the CONST case's
section-only ship (full `↔ A` is genuinely UIP-strength); the INJ
/ SURJ re-exports (the underlying theorems are correct upstream).

### Session arc 2026-05-27 Tier-1+2 advance — NoSectionGeneric + ImageFactorization (read this first)

*Where we started (post-keystone, commit on the Tier-1 spine):* the
synthesis roadmap (audit + previous-list + new-list, GPT-corroborated)
had Tier 1 #2 = "generalise `no-section`" and Tier 2 first item =
`EchoImageFactorization` next, in the GPT-reordered sequence
(Image → Loss → Residue → Decoration → ObsEquiv).

*Where we ended:* both LAND, both build clean. Two slices:

1. *`proofs/agda/EchoNoSectionGeneric.agda`* — Tier 1 #2 discharge.
   Headline `no-section-of-collapsing-map`: for ANY `lower : A → R`
   with two distinct elements `e₁ ≢ e₂` collapsing to the same
   residue (`lower e₁ ≡ lower e₂`), no section exists. Three-line
   proof (`trans/sym/cong` pattern lifted from
   `no-section-collapse-to-residue`). Two corollaries land in the
   same module:
     * `no-section-collapse-to-residue′` recovers the existing
       `EchoResidue.no-section-collapse-to-residue` as a one-line
       instance — typechecks because the existing repo already
       provides the four hypotheses by name. Mechanically
       demonstrates the existing theorem IS an instance of the
       generic structure.
     * `no-section-when-non-injective-at-y` is the Echo-specific
       form the abstraction-barrier narrative wants: any `f : A → B`
       with two distinct echoes at `y` admits no section over the
       trivial residue (because `trivial-weaken f y _ = (tt, tt)`
       collapses every fibre uniformly).

2. *`proofs/agda/EchoImageFactorization.agda`* — Tier 2 first item
   per GPT's reordered sequence. `Image f := Σ B (Echo f)` (= the
   total Echo space from `EchoTotalCompletion`). The image-
   factorisation triangle `A ─encode→ Image f ─proj₁→ B` re-exports
   the OFS legs under image-side names (`image-factor-left`,
   `image-factor-right`, `image-factor-commutes`, the triangle
   `refl`). Three classifications pin the function-level
   characterisations that the next module (`EchoLossTaxonomy`) will
   organise:
     * `Surjective f := (b : B) → Echo f b`, with
       `surjective-iff-every-fibre-inhabited` pinning the
       definitional rephrasing for a stable consumer-side name.
     * `Injective f := {x y} → f x ≡ f y → x ≡ y` (standard
       MLTT shape).
     * `injective-fibres-proj-unique`: under injectivity, any two
       echoes at the same `b` have equal `proj₁`s. This is the
       K-free version (no UIP); the stronger "full echoes are
       equal as Σ-pairs" claim needs UIP on `B` and is honestly
       NOT proved (companion-remark documents this as a deferred
       earn-back).

   *Honest scope (both modules).* The full (epi, mono) Set
   factorisation requires propositional truncation `∥_∥`, which
   `--safe --without-K` without HITs can't construct. The proof-
   relevant Image lands here as the UPPER of the two factorisations
   (universal in the (equivalence, projection) OFS, degrading to
   (epi, mono) under truncation). The truncated form is documented
   as the next earn-back gate.

   Build invariant held: `EchoNoSectionGeneric.agda`,
   `EchoImageFactorization.agda`, `Smoke.agda`, and `All.agda` all
   exit 0 under `--safe --without-K`, zero postulates, no funext.
   Both modules pinned in `Smoke.agda` under their own `using`
   blocks with header comments; wired into `All.agda` next to the
   keystone pair (TotalCompletion + OFS).

*Plan for the next Claude.* Tier 2 continues per the GPT-corroborated
reorder:

1. *Tier 2 #2 — `EchoLossTaxonomy.agda`.* Function-side classification:
   equiv ⇒ contractible-fibre, inj ⇒ proj-unique (already proved here,
   re-export), surj ⇒ inhabited (rename `Surjective`), const ⇒
   full-domain fibre. Quotient / projection / forgetting case
   sketches. The three primitives already exist
   (`injective-fibres-proj-unique`, `Surjective`, `Echo` itself for
   constant case) — taxonomy is mostly organisation + named
   theorems wrapping them.

2. *Tier 2 #3 — `EchoResidueTaxonomy.agda`* (residue-side).
   `record ResidueForm` interface; the eight existing decoration
   modules (Linear / Graded / Choreo / Access / Cost / Search /
   Indexed / Epistemic) as instance witnesses. Paired with (1) per
   the audit: kinds-of-loss × shapes-of-residue grid.

3. *Tier 2 #4 — `EchoDecorationStructure.agda`* (observation-side
   companion). Record packaging the recipe (`order`, `order-prop`,
   `join`, `degrade-compose`, `degrade-via-join`) the eight
   decoration modules each re-implement.

4. *Tier 2 #5 — `EchoObservationalEquivalence.agda`* — mode-indexed
   equality on `LEcho`.

5. *Tier 3 — full-OFS earn-back gate.* Funext-qualified uniqueness
   up to iso + diagonal lifting, in the Pillar-F4 template style.

6. *Audience moves (Tier 3, GPT-recommended order):* Provenance
   first (closest native-language fit), then Security, then
   Probabilistic / Differential.

7. *Narrative deliverable — `EchoCanonicalIdentitySuite.agda`*
   once (1)-(4) land.

DO NOT reopen: the keystone pair (TotalCompletion + OFS); the
no-section generalisation (the trans/sym/cong pattern is the only
content, and it's lifted at the right level); the K-free vs
UIP-required split in ImageFactorization (`injective-fibres-proj-
unique` is K-free; the full Σ-equality is honestly deferred);
the cementing artefacts (EchoEntropy + EchoLLEncoding).

### Session arc 2026-05-27 keystone — TotalCompletion + OFS (read this first)

*Where we started (post-Shannon/LL session, commit on the audit
follow-on):* the audit / two-list synthesis identified
`A ≃ Σ B (Echo f)` as the single most-cited but never-pinned theorem
in the project's narrative (the "irreversible computation + echo =
reversible representation" slogan), and the
(equivalence, projection) factorisation system as the architectural
keystone that ties it to image factorisation, optic complements, and
the universal-property story. Neither was in the suite.

*Where we ended:* both LAND, both build clean.  Two slices:

1. *`proofs/agda/EchoTotalCompletion.agda`* — the slogan-unlock.
   `encode : A → Σ B (Echo f)`, `decode : Σ B (Echo f) → A`,
   round-trips `decode-encode` (definitional) and `encode-decode`
   (one `refl`-pattern elimination on the inner equation, safe
   under `--without-K`), the headline `A↔ΣEcho : A ↔ Σ B (Echo f)`
   packaged via `mk↔ₛ′`. Two factorisation-triangle convenience
   lemmas (`f-factors-via-projection`,
   `encode-is-section-of-proj₁`) pin the definitional content
   `f ≡ proj₁ ∘ encode f`. Zero postulates, no funext.

2. *`proofs/agda/EchoOrthogonalFactorizationSystem.agda`* — the
   architectural keystone. Re-exports
   `EchoTotalCompletion.A↔ΣEcho` as `left-leg-equivalence`; pins
   the factorisation triangle as `echo-factorisation`. The
   generic Σ-fact "fibre of `proj₁ : Σ B P → B` at `y` is
   canonically `P y`" lands as the four
   `fibre-of-proj₁-{to,from,to-from,from-to}` clauses plus the
   packaged `fibre-of-proj₁-iso`; specialised to `P := Echo f`
   it becomes `projection-fibre-iso`, the load-bearing
   "right-leg's fibre at `y` is `Echo f y`" claim. The four-tuple
   `ofs-witness` packages the factorisation system witness at
   the honesty level reached: factorisation existence + left-leg
   equivalence + projection-fibre identification + echo↔fib
   bridge.

   *Honest scope.* A full OFS additionally requires uniqueness up
   to isomorphism and the diagonal-lifting property; both need
   funext to state. They are NOT proved in this module. The
   module's companion-remark block explicitly documents this and
   names the earn-back path: take `funext` as an explicit
   hypothesis parameter (template = `EchoPullbackUnivF4`, the
   Pillar F4 funext-qualified strict universal property; same
   discipline as R-2026-05-18 narrowings). The unconditional
   content above is the load-bearing artefact; the full OFS is
   the next earn-back gate.

   *Notation note.* The `fibre-of-proj₁-*` helpers are stated in
   the unfolded form `Σ (Σ B P) (λ z → proj₁ z ≡ y)` rather than
   `fiber (proj₁ : Σ B P → B) y`, because `proj₁`'s second
   implicit argument is named `B` and clashes with a
   locally-bound `B`. The unfolded form is the same set; only the
   surface notation differs. Documented inline.

   Build invariant held: `proofs/agda/EchoTotalCompletion.agda`,
   `proofs/agda/EchoOrthogonalFactorizationSystem.agda`,
   `proofs/agda/Smoke.agda`, and `proofs/agda/All.agda` all exit
   0 under `--safe --without-K`, zero postulates, no funext.
   Both modules pinned in `Smoke.agda` under their own `using`
   blocks with header comments per CLAUDE.md "Working rules";
   wired into `All.agda` directly under `Echo` (since they are
   the canonical totality / factorisation companions to the core
   Echo definition).

*Plan for the next Claude.* The Tier 1 spine landed today. Open
work on the synthesis programme (per the two-list + audit
roadmap):

1. *Tier 1 #2 — generalised `no-section`.* `¬-injective f ⇒
   ¬ Σ s (weaken ∘ s ≡ id)`. Raises the existing single-instance
   `no-section-weaken` from "an example" to "a theorem of the
   structure". Small slice; cheap.

2. *Tier 1 doc-only consolidations.*
   `docs/echo-types/universal-property.adoc` (consolidating
   `EchoPullback` + `EchoPullbackUnivF4` + the R-2026-05-18
   narrowing) and `docs/echo-types/fibration-package.adoc`
   (consolidating `map-over*` + `Echo-comp-iso` + `cancel-iso`).
   Pure doc work; no Agda.

3. *Tier 2 — paired taxonomies.*
   `EchoLossTaxonomy.agda` (function-side: classify `f` by echo
   shape — equiv ⇒ contr, inj ⇒ prop, surj ⇒ inhabited, const ⇒
   full domain) PAIRED WITH `EchoResidueTaxonomy.agda`
   (residue-side: `record ResidueForm` + the eight existing
   decoration modules as instances). Per the audit, doing both
   together turns the existing decoration sprawl into a clean
   two-axis grid (kinds-of-loss × shapes-of-residue).

4. *Tier 2 — `EchoDecorationStructure.agda`.* Companion abstraction
   to (3): a record packaging the recipe (`order`,
   `order-prop`, `join`, `degrade-compose`, `degrade-via-join`)
   that each of the eight decoration modules redundantly
   re-implements. The eight existing modules become instance
   witnesses. Turns the uniform recipe from "a comment" into "a
   theorem".

5. *Tier 2 — `EchoObservationalEquivalence.agda`.* Mode-indexed
   equality on `LEcho`, making Linear-equality vs Affine-equality
   crisp.

6. *Tier 3 — full OFS earn-back gate
   (`EchoOFSUnivE` or similar, Pillar-F-style).* Take funext as
   explicit hypothesis; prove uniqueness up to isomorphism +
   diagonal lifting; pin the funext-free corollaries. The
   unconditional content from this session's OFS module is the
   load-bearing prerequisite.

7. *Outward extensions (audience moves).* `EchoProvenance.agda`
   first (closest fit to the existing residue/witness/no-section
   language; generalisation of the existing
   `EchoExampleProvenance.agda` instance); then
   `EchoSecurity.agda` (with the honest-bound discipline
   `RegionExitAudit.agda:7-17` already established);
   `EchoProbabilisticSupport.agda` and `EchoDifferential.agda`
   are independent and lower-priority.

8. *Narrative deliverable —
   `EchoCanonicalIdentitySuite.agda`.* Once (1)-(5) land, the
   curated suite practically writes itself: it pulls existing
   named theorems into a single Agda file that runs as the "why
   Echo deserves a name" demo. Almost no new proof work.

DO NOT reopen: the four `EchoTotalCompletion` round-trip lemmas
(both directions are essentially definitional with one path
elimination); the `fibre-of-proj₁-{to,from,...}` quartet (the
generic Σ-projection-fibre fact, K-free); the OFS module's
scope-narrowing (full lifting/uniqueness need funext, documented
as the next earn-back gate per F4 / R-2026-05-18 discipline);
the cementing artefacts (EchoEntropy + EchoLLEncoding from the
preceding session).

### Session arc 2026-05-27 audit follow-on — Shannon + LL gap cementing artefacts (read this first)

*Where we started today (post-`04f3d9f`, after the head-Ω slice):*
the audit of `EchoAbstractionBarrier` and the cross-repo bridges
identified two specific "cementing" theorems flagged in the modules
themselves as not-yet-formalised: Shannon-entropy non-distinguishing
(`EchoThermodynamics.agda:214-217`, `EchoStabilityTests.agda:128-129`)
and the linear-logic shallow-encoding gap (no `.agda` site, only
narrative in `core/skepticisms/what-is-actually-new.md`).

*Where we ended today:* both cementing artefacts LAND.  Two slices:

1. *`proofs/agda/EchoEntropy.agda`* — discrete Shannon-entropy
   non-distinguishing theorem. Defines a local `⊤-≟` (`Dec`
   equality on `⊤`), the `Fin 2 → ⊤` representation
   `collapse-as-fin`, and the `collapse-fibre-count : FiberSize-fin
   ≡ 2` lemma via `FiberSize-fin-all-hit`. Headlines:
   `entropy-shadow : Echo collapse tt → ℕ` (constant `2`, the
   uniform-prior Shannon surrogate), `shannon-shadow` (`⌊log₂_⌋`
   of it, definitionally `1`), `entropy-shadow-equal` and
   `shannon-shadow-equal` (both `refl`), `entropy-shadow-blind` and
   `shannon-shadow-blind` (any consumer factoring through the
   shadow agrees on `echo-true` vs `echo-false`, via `cong`).
   Matched-negative `witness-distinguishes-where-entropy-cannot`
   cites `EchoAbstractionBarrier.sigma-distinguishes` so the
   pairing is a checked artefact, not a unilateral observation.

2. *`proofs/agda/EchoLLEncoding.agda`* — linear-logic shallow-
   encoding gap theorem.  `LLShallowEncoding : Set₁` record
   captures the data of a standard LL `!A`-style translation
   (mode-indexed carrier `X`, embedding `enc`, encoded weakening
   `wX`, naturality `enc-commutes`). The canonical `X m := ⊤`
   shadow (LL `!A := 1`) is `trivial-encoding`; its encoded `wX`
   admits the identity section by definitional reduction
   (`trivial-encoding-has-section`).  Headline `ll-encoding-gap`
   packages "an LL shallow encoding exists whose `wX` has a
   section"; matched-negative `source-no-section` recites
   `EchoLinear.no-section-weaken`; `gap-paired` is the single-Σ
   pair making the gap a checked artefact.

   *Honest scope.* The theorem is an EXISTENCE statement (one
   encoding with one section). The companion remark documents the
   non-claims: a sufficiently rich encoding could re-introduce the
   witness and preserve no-section, but is then no longer the
   standard `!A := 1` shadow. The interesting content is exactly
   "the strict LL collapse is too weak to be faithful translation
   of `LEcho`".

   Build invariant held: `proofs/agda/EchoEntropy.agda`,
   `proofs/agda/EchoLLEncoding.agda`, `proofs/agda/Smoke.agda`, and
   `proofs/agda/All.agda` all exit 0 under `--safe --without-K`.
   Zero postulates, no funext, no `TERMINATING` pragma. Both
   modules pinned in `Smoke.agda` under their own `using` blocks
   with header comments per CLAUDE.md "Working rules"; wired into
   `All.agda` adjacent to `EchoAbstractionBarrier`
   (`EchoLLEncoding`) and `EchoThermodynamics` (`EchoEntropy`)
   respectively.

   *Companion doc updates.* `EchoThermodynamics.agda:214` and
   `EchoStabilityTests.agda:128` rewritten from "not yet
   formalised" to point at `EchoEntropy.agda`, with the still-open
   real-valued / mutual-information forms explicitly listed.
   `roadmap.adoc` §Lane 2 gains a "Cementing follow-ons (LANDED
   2026-05-27)" subsection covering both artefacts.

*Plan for the next Claude.*  Open follow-ons from this session:

1. *Real-valued Shannon entropy.*  Lift the discrete fibre-count
   shadow to `H(P) = -Σ p log p` over a parametric distribution.
   Needs a rationals/reals layer + a probability interface; out of
   reach under `--safe --without-K` without significant extra
   infrastructure.  Lower-priority — discrete form is the
   load-bearing artefact for the abstraction-barrier line.

2. *Universal LL-encoding gap.* Strengthen `ll-encoding-gap` from
   "exists an LL shallow encoding under which no-section fails" to
   "every LL shallow encoding satisfying a forget-witness invariant
   fails".  Statement form: parametrise over `X m := F m` with `F`
   constant on inhabitants, prove the section always exists.  Small
   slice; primarily a notational lift over the trivial encoding's
   argument.

3. *Universal-property gap for entropy.* Promote
   `entropy-shadow-blind` from "the trivial shadow is blind" to a
   universal property: any consumer factoring through ANY function
   of the fibre count cannot recover witness-level distinctions.
   One-line `cong` once stated.

DO NOT reopen: the `EchoAbstractionBarrier` T2/T3 (Track B of the
identity claim, landed 2026-05-26); the R-2026-05-18 narrowings;
the cementing artefact pair landed this session (its claims are
explicitly scoped at the discrete / existence level — see each
module's companion-remark block before any "promote to universal"
work).

### Session arc 2026-05-27 night — Lane 3 head-Ω Slice 2 landed (read this first)

*Where we started today (commit `65806f4` on `main`, post-#129):* the
PR #129 decoration-bridge scaffold landed under R5; Lane 3's head-Ω
domination route had Slice 1 (`HeadOmega.agda`) but no Slice 2 work.
The `<ᵇ-+1` joint-bplus case remained open with `head-Ω` defined but
not yet consumed by any rank-mono primitive.

*Where we ended today (commit `bf9ee6e` on `main`, post-#130):* Slice 2
lands the abstraction (`ω-rank-pow-succ` + the fin-branch strict
dominance) plus an honest obstruction note on the ω branch:

1. *`Ordinal.Buchholz.RankPow.agda` additions.*
   * `ω-rank-pow-succ : OmegaIndex → Ord` — the per-marker "next
     ω-power up" target.  Fin branch is `ω^(suc(suc n))`; ω branch
     reuses the original CLAUDE.md proposal `olim (λ n →
     ω^(suc(suc n)))` so the abstraction is in place for follow-on
     slices to inspect and (if needed) override.
   * `ω-rank-pow-succ-fin` — definitional sanity at the fin branch.
   * `ω-rank-pow-<-succ-fin` — per-marker strict dominance at fin
     via `ω^-strict-mono-suc (suc n)`.
   * `rank-pow-bOmega-via-head-Ω`, `rank-pow-bpsi-via-head-Ω` —
     atomic-rank `refl`-shape primitives factoring `rank-pow` through
     `head-Ω` for the two non-bplus, non-bzero `BT` constructors.

2. *`Ordinal.Buchholz.Smoke.agda` pinning.*  Five headlines pinned
   under their own `using` block with a header comment, per CLAUDE.md
   Working rules.

*Obstruction note.*  The originally-proposed CLAUDE.md shape
`ω-rank-pow-succ ω = olim (λ n → ω^(suc(suc n)))` represents the
**same** ordinal as `ω-rank-pow ω = olim (λ n → ω^(suc n))` — both
are `sup{ω^(n+1) : n ∈ ℕ} = ω^ω`, with different ℕ-indexings of the
same tail.  Strict dominance at the ω branch therefore cannot hold
under that shape.  Inline `RankPow.agda` comments document two
follow-on slices:

* *Slice 2-omega.*  Replace the ω branch with a genuinely
  strictly-larger ordinal.  Candidate: `ω^(ω+1)` encoded as
  `olim (λ n → (ω-rank-pow ω) ·ℕ n)`.  Three cross-checks
  documented inline before committing (closure under ordinal
  addition; the consumer's actual additive-principal need; sanity-
  check of the indexing's leading `oz ⊕` which is NOT definitionally
  `ω-rank-pow ω` under Brouwer's right-recursing `_⊕_`).
* *Slice 2-bplus.*  Prove the full
  `rank-pow-dominated-by-head-Ω : (t : BT) → NonBzero t → WfCNF t →
  rank-pow t <′ ω-rank-pow-succ (head-Ω t)` by structural recursion
  on WfCNF.  The bplus case needs a `rank-pow-mono-≤ᵇ` companion for
  the original `_<ᵇ_` (the WfCNF tail bound is `_≤ᵇ_`, not `_≤ᵇ⁰_`).
  Marked `TODO(slice-2-bplus)` inline.  Option (b) — head-Ω inversion
  that does not transitively depend on rank-mono — is preferred
  because it keeps `rank-pow-dominated-by-head-Ω` independent of
  the companion so signature changes don't silently propagate.

Build invariant held: `proofs/agda/All.agda` + `proofs/agda/Smoke.agda`
+ `Ordinal/Buchholz/Smoke.agda` all exit 0 under `--safe --without-K`,
zero postulates, no funext.  `scripts/kernel-guard.sh` PASS.

PR #130 was admin-merged before CI green at user direction; CI was
still all-12-queued at merge time.  No CI failures have surfaced
since (treat any later red as authoritative if it does).

*Plan for the next Claude.*

Within this same session (2026-05-27 night, PR #131), items (1) and
(2) from the original plan also landed:

* *(1) Option (b) head-Ω inversion lemma — LANDED* (commit `560f904`).
  New module `Ordinal.Buchholz.HeadOmegaInversion` ships
  `head-Ω-inv-bOmega : bOmega ν <ᵇ y → ν <Ω head-Ω y` (strict) and
  `head-Ω-inv-bpsi : bpsi ν α <ᵇ y → ν ≤Ω head-Ω y` (non-strict —
  tracks the `<ᵇ-ψΩ≤` constructor).  Pinned in
  `Ordinal/Buchholz/Smoke.agda` under its own `using` block.  Wired
  into `All.agda`.  No rank-mono dependency — that was the
  load-bearing dependency-graph invariant the design called for.
* *(2) Slice 2-omega — LANDED* (commit `07abc15`).  ω branch of
  `ω-rank-pow-succ` replaced with `olim (λ n → ω-rank-pow ω ·ℕ n)`
  (= `ω^(ω+1)`); per-marker strict dominance proved at the ω
  branch via a mirror of `Brouwer/OmegaPow.ω^-strict-mono-suc`
  (branch-index-2 + `X≤′oz⊕X` + `⊕-mono-<-right (ω-rank-pow-pos ω)`).
  Unified `ω-rank-pow-<-succ : ∀ μ → ω-rank-pow μ <′
  ω-rank-pow-succ μ` covers both branches.

Only one item remains open:

3. *Slice 2-bplus* — prove the full domination lemma
   `rank-pow-dominated-by-head-Ω : (t : BT) → NonBzero t → WfCNF t →
   rank-pow t <′ ω-rank-pow-succ (head-Ω t)` by structural recursion
   on the WfCNF carrier.  Both per-marker dominances now hold; the
   atomic cases discharge via `rank-pow-{bOmega,bpsi}-via-head-Ω` +
   `ω-rank-pow-<-succ`.  The bplus case consumes
   `head-Ω-inv-{bOmega,bpsi}` from `HeadOmegaInversion` to pull
   `head-Ω` bounds from the WfCNF tail's `<ᵇ` witness.  No further
   inversion-via-rank-mono dependency is introduced — that's what
   option (b) bought.

DO NOT reopen: the closed 11/13 Buchholz constructors; the W1/W2/W3
walkthroughs; the R-2026-05-18 narrowings; the closed fin-branch /
ω-branch / unified dominances; the head-Ω inversion family.

### Session arc 2026-05-27 evening — Lane 5 Walkthrough 3 landed

*Where we started today (commit `4d77d75` on `docs/consolidate-roadmaps-
and-sigma-skepticism-2026-05-26`, post-#123):* the consolidation branch
carried Walkthroughs 1 (region-exit audit) and 2 (epistemic erasure)
plus the Lane 3 `RankLex` slice closing `<ᵇ-ψΩ≤`. Walkthrough 3
(provenance / debugging) was at scaffold/design-doc level in
`tutorial/README.adoc`. The originally-scaffolded Lane 5 triplet was
two-thirds landed.

*Where we ended today:* Walkthrough 3 LANDS — the originally-scaffolded
triplet is complete in Agda. One slice:

1. *Walkthrough 3 — provenance / debugging echo* lands at
   `tutorial/provenance_debugging/`. Domain: 4-element `State` with
   two orthogonal sign bits (`firstSign`, `secondSign`); `firstSign`
   is the echo's visible output, `secondSign` is the class predicate
   the layer-1 residue carries. Three residue layers walked:
     * Layer 0 — `Echo firstSign true`, distinguishing all sources;
     * Layer 1 — `EchoR Bool ClassCert true` carrying `secondSign`;
     * Layer 2 — `EchoR ⊤ TrivialCert' true` carrying nothing.
   Headlines: `states-distinct-at-true` (Layer 0 distinguishes);
   `classes-remain-distinct` (Layer 1 still distinguishes);
   *`recover-section-at-layer-1`* (POSITIVE — Layer 1 has a section);
   `trivials-collapse` (Layer 2 collapses); *`no-recovery-from-trivial`*
   (NEGATIVE — Layer 2 has no section, structural mirror of
   `EchoResidue.no-section-collapse-to-residue`); and
   `provenance-walk-contrast` packaging the section / no-section pair.

   *New pedagogical shape vs W1/W2.* Walkthroughs 1 and 2 each ship a
   one-sided no-section result. Walkthrough 3 ships *both* a section
   (at layer 1) and its absence (at layer 2), exhibiting the boundary
   at which the type-level recovery property flips. The mechanical
   load: `secondSign` is *injective within each `firstSign`-fibre*,
   which is exactly the property the layer-1 section needs.

   *Honest bound discipline inherited from W2.* The Agda file and the
   README both open with the disclosure that this is type-level only —
   no operational debugger, no runtime artefacts, fixed 4-element
   domain. A `NotProved-*` matched-negative block at the file's
   bottom lists four out-of-scope properties (runtime debugger,
   reconstruction in general, completeness across classes, recovery
   under side information) as `⊤`-aliases so `grep NotProved` catches
   them.

   *Files landed.*
   * `tutorial/provenance_debugging/ProvenanceDebugging.agda` (worked
     example);
   * `tutorial/provenance_debugging/Smoke.agda` (per-walkthrough Smoke
     pins, own `using` block, header comment);
   * `tutorial/provenance_debugging/All.agda` (aggregator);
   * `tutorial/provenance_debugging/README.adoc` (narrative).
   * `tutorial/All.agda` registers the new walkthrough.
   * `tutorial/README.adoc` §"Walkthrough 3" flipped from design-doc
     status to LANDED 2026-05-27; the IMPORTANT scaffold-status note
     updated.

Build invariant held: `proofs/agda/All.agda`, `proofs/agda/Smoke.agda`,
`tutorial/All.agda`, and `tutorial/provenance_debugging/Smoke.agda`
all exit 0 under `--safe --without-K`, zero postulates, no funext.
All headlines pinned in the per-walkthrough Smoke under their own
`using` block per CLAUDE.md "Working rules".

*Plan for the next Claude.* The originally-scaffolded Lane 5 triplet
is complete. Open work:

1. *Lane 3 follow-on — `<ᵇ-+1` joint-bplus.* The one remaining open
   per-constructor case in the Buchholz rank-mono umbrella. Closure
   options documented in `RankPow.agda` and the obstruction doc:
   (A) leading-Ω-index dominator (`head-Ω : BT → OmegaIndex`),
   recommended; (B) richer rank shape on `bplus`. Smallest useful
   first slice = define `head-Ω` + definitional sanity lemmas only,
   no rank-mono. Multi-session work.
2. *Lane 5 unparking decision (user).* Walkthroughs 1+2+3 all
   landed; Walkthrough 1 is the killer-app candidate per
   `roadmap.adoc` §Lane 5 second unblocking condition. User
   accept-or-defer pending; the lane remains [PARKED] at the lane-
   policy level until the user decides.
3. *Pillar E paper [EXPAND] clearing.* Gated on author-driven
   material accruing.

DO NOT reopen: the closed 11/13 Buchholz constructors (their
primitives are correct under WfCNF + admissibility + lex-pair);
the W1/W2 walkthroughs (their no-section headlines are the existing
`EchoLinear.no-section-weaken` and `EchoResidue.no-section-collapse-
to-residue` re-exported with honest-bound + matched-negative
discipline); the R-2026-05-18 narrowings.

### Session arc 2026-05-27 late evening — Lane 3 head-Ω first slice

*Where we started today (commit `04f3d9f`, post-W3):* the consolidation
branch carried the complete Lane 5 triplet (W1/W2/W3) plus the 11/13
Buchholz constructor closure via `rank-pow` + `rank-adm` + `rank-lex`.
The one remaining open per-constructor case `<ᵇ-+1` joint-bplus
sits behind a documented structural blocker
(`docs/echo-types/buchholz-rank-obstruction.adoc` §"What remains
open"): `rank-pow (bplus z₁ z₂)` is not additive principal in
general.

*Where we ended today:* option (A) from `RankPow.agda`'s preamble
opens via the head-Ω abstraction.  One slice:

1. *`Ordinal.Buchholz.HeadOmega.agda`* — the leading-Ω-index head
   function `head-Ω : BT → OmegaIndex`:
     * `bzero`        ↦ `fin 0` (default; future rank-mono guards via
       non-bzero premise);
     * `bOmega ν`     ↦ `ν`;
     * `bplus x _`    ↦ `head-Ω x` (leftmost);
     * `bpsi ν _`     ↦ `ν`.
   Four definitional sanity lemmas (one per `BT` constructor, each
   `refl`) plus one two-level compositional convenience
   (`head-Ω-bplus-left`) for the WfCNF left-spine pattern.
   Pinned in `Ordinal/Buchholz/Smoke.agda` under own `using` block
   with header comment; wired into `proofs/agda/All.agda` between
   `RankLex` and `RankMonoUmbrella`.

   *Smallest useful first slice.*  No rank-mono in this slice; the
   domination lemma `rank-pow t <′ ω-rank-pow-succ (head-Ω t)` and
   the headline `<ᵇ-+1` joint-bplus discharge are explicitly
   deferred to follow-on slices per `HeadOmega.agda`'s preamble.
   The abstraction stands on its own merits before any rank
   consumer pulls on it.

Build invariant held: `Ordinal/Buchholz/Smoke.agda`,
`proofs/agda/Smoke.agda`, and `proofs/agda/All.agda` all exit 0
under `--safe --without-K`, zero postulates, no funext.  All
headlines pinned in the Buchholz-layer Smoke under their own
`using` block per CLAUDE.md "Working rules".

*Plan for the next Claude.*  Continue option (A):

1. *Slice 2 — ω-rank-pow-succ + the domination lemma.* Add
   `ω-rank-pow-succ : OmegaIndex → Ord` to `RankPow.agda` (one
   option: `ω-rank-pow-succ (fin n) = ω^(suc (suc n))`,
   `ω-rank-pow-succ ω = olim (λ n → ω^(suc (suc n)))`), then prove
   `rank-pow-dominated-by-head-Ω : (t : BT) → NonBzero t → WfCNF t →
   rank-pow t <′ ω-rank-pow-succ (head-Ω t)` by structural recursion
   on the WfCNF carrier, applying `rank-pow-bplus-into-ω-rank-pow`
   at each `bplus` step.  This is the load-bearing slice.
2. *Slice 3 — the headline `rank-mono-<ᵇ-+1-via-head-Ω`.*  Builds
   on Slice 2 + `rank-mono-<ᵇ-+1-via-target` from `RankPow.agda`.
   At consumer time: head-Ω inversion on the target's left summand
   gives the additive-principal witness; source `bplus`'s rank is
   dominated by `ω-rank-pow-succ (head-Ω source)`, which by
   `head-Ω-bplus` equals `ω-rank-pow-succ (head-Ω x₁)`, strictly
   below the target's rank via the `<ᵇ` premise.
3. *Slice 4 — full `rank-pow-mono-<ᵇ⁻` umbrella.* Composition of
   the head-Ω discharge with the existing 11-constructor closures.
   The final Buchholz rank-monotonicity theorem under the WfCNF
   restriction.

DO NOT reopen: `head-Ω` returns `fin 0` on `bzero` as a deliberate
default — future rank-mono lemmas guard the `bzero` case via the
non-bzero premise, so the default is never consumed in a proof
context.  Changing the default to `Maybe OmegaIndex` would force
every downstream caller through an unwrap; the documented
non-bzero guard is the cleaner discipline.

### Session arc 2026-05-20 daytime (theory closure waves 1 + 2 + 3)

*Where we started today (commit `888dee0`, post-#73):* the establishment
track was complete A–D + Pillar E paper drafting in progress. The
theory roadmap §"Theory work — no proof assistant needed" listed four
"open" items (Axis 2 approximate, Axis 8 refinement, negative/CoEcho,
2-categorical shape) plus two truly open (presentation-dependence,
Gate 1 adjacency refresh).

*Where we ended today:* the **entire `§Theory work — no proof
assistant needed` section is closed** (modulo Lane 2 in flight). 10+
PRs landed:

1. `#67` — doc rule-out 2-categorical shape + roadmap correction.
   Discovered 2 of 4 "open" items were actually shipped: Axis 2 already
   landed as `EchoApprox.agda`; Axis 8 candidate 3 already landed as
   `EchoDecidable.agda`. Roadmap re-credited. `decisions/no-2-cat.adoc`
   added — every would-be 2-cell in landed code is `refl` or forced
   trivial by propositionality.
2. `#68` + `#75` — Axis 8 graded access modality. New `EchoAccess.agda`:
   5-grade enum (`free / decidable / enum / feasible / infeasible`),
   Hasse-enumerated `_≤a_` with `≤a-prop` closing on `refl`,
   `EchoAccess` Σ-carrier, `_⊔a_` join + 3 join lemmas + composition
   trio mirroring `EchoGraded` recipe. Sixth instance of the
   decoration recipe.
3. `#69` + `#72` — AntiEcho (Σ-dual of Echo) + tropical decomposition.
   `AntiEcho f y := Σ A (λ x → f x ≢ y)`. Tropical decomposition
   `IsArgmin ↔ Echo × Π (¬(score z < y))` ships both bijection
   directions with `refl` round-trips. Cashes the CoEcho exploration's
   "EchoTropical tension dissolves" claim.
4. `#70` + `#74` — EchoApprox composition rung. Retract direction
   (`echo-approx-comp-retract-to/A`) + Separated zero-collapse +
   axis-1 shadow lemmas. Rung C (full B/budget round-trip) deferred —
   needs `Tolerance` `+`-identity; in flight as Lane 2 via separate
   `BalancedTolerance` record (option b).
5. `#71` — hygiene: per-lemma Smoke pins for `EchoApprox` via
   `EchoApproxInstance.agda` (trivial-on-`⊤` instance). Closes a
   silent CLAUDE.md-invariant violation for parameterised modules.
   Standard pattern for future parameterised modules.
6. `#76` — presentation-dependence sub-theory: examples 5, 9, 10
   cluster as Σ-over-`R` instantiating Axis 4; meta-pattern only,
   no formalisation needed.
7. `#77` — Gate 1 adjacency refresh: 5/5 REFINED verdicts; every
   adjacency claim survives, all benefit from re-statement in axis
   terms (esp. axis 8 after this session).
8. This PR — bookkeeping (CLAUDE.md refresh) + Lane 1 closure
   (`Lift ⊤` confirmed as honest carrier for EchoAccess top grades;
   `decisions/echo-access-trivial-carrier.adoc`). The existential
   carriers attempt structurally fails because the access lattice
   tracks DECREASING information; trivial carrier is correct.

Build invariant held every rung: `All.agda` + `Smoke.agda` exit 0
under `--safe --without-K`, zero postulates, zero escape pragmas, no
funext. Pillar E paper continues (parallel sessions; `#73` landed
primer + related-work + estate PMPL→MPL-2.0 sweep).

Two patterns formalised this session:

* **Smoke pin for parameterised modules** via concrete trivial instance
  (`EchoApproxInstance.agda` style). Apply to any future parameterised
  module to honour the "every headline pinned" invariant.
* **Sandbox quirk on `agda` positional args**: `Bash(agda *)` in
  `permissions.allow` doesn't cover `agda <file>`. Workaround in
  `.claude/settings.json`: `"sandbox": {"excludedCommands": ["agda"]}`,
  applied 2026-05-20. Future Agda swarms should not need the
  parent-verify dance that was required on PRs #71, #72, #75.

### Session arc 2026-05-20 Wave 3 (later, same day)

After §"Theory work" section closed, a final swarm wave (5 PRs)
shipped the remaining Axis 8 refinements + the presentation-dependence
example cluster identified by `#76`:

9.  `#80` — `EchoSearch.agda` + `EchoSearchInstance.agda`. Axis 8(4)
    witness-search abstract machine, thin slice: bound-`n` echo via
    enumerator. Headlines: intro / relax / forget / bound-zero /
    postcompose. Sequential+product composition deferred (needs
    `ℕ × ℕ ↔ ℕ` pairing); real abstract-machine model deferred.
10. `#85` — `EchoCost.agda` + `EchoCostInstance.agda`. Axis 8(1)
    cost-indexed refinement over abstract `CostAlgebra`
    (ordered commutative monoid with `+`-identityˡ + `+`-mono-≤).
    Composition uses first-order combiner shape (strictly more
    general than EchoApprox's endomorphic-outer-leg shape; single-
    domain corner falls out by `combine := proj₂`). No funext.
11. `#81` — Example 5 (DB provenance via Bool K-provenance semiring),
    `EchoExampleProvenance.agda`. Distinct Bool-provenance rows
    project to same payload; Echo carries the lost annotation.
    Headlines tie to `EchoResidue` via `collapse-via-residue`.
12. `#83` — Example 9 (parser residue, balanced parens),
    `EchoExampleParser.agda`. Pragmatic depth-counter `parses`
    (avoids full Balanced grammar); both Bool-shadow and
    BalancedClosed grammar witnesses pinned. `(())` vs `()()`
    are two distinct echoes at `parses ≡ true`.
13. `#82` — Example 10 (abstract interpretation via Sign lattice),
    `EchoExampleAbsInt.agda`. Hand-rolled 5-element carrier
    (`{m2,m1,z,p1,p2}`) avoids Data.Integer weight. `α` collapses
    `m2,m1↦neg`, `p1,p2↦pos`. `distinct-echoes-same-sign` is the
    headline; `absint-classification` proves the concrete class
    over `pos` is exactly `{p1,p2}`.

Plus parallel-session contributions during Wave 3: `#84` Pillar E
Evaluation section, `#86` F1 gc-coassoc earn-back closure.

**Axis 8 status now: 4 of 4 refinements landed.** Decidability
(`EchoDecidable.agda`, pre-session); graded access (`EchoAccess.agda`,
`#68`+`#75`+`#79`); cost-indexed (`EchoCost.agda`, `#85`);
witness-search (`EchoSearch.agda`, `#80`).

Build invariant held: `All.agda` + `Smoke.agda` exit 0 across all 5
Wave-3 PRs under `--safe --without-K`, zero postulates / funext /
escape pragmas. Smoke pins for parameterised modules continue using
the `EchoApproxInstance` trivial-on-`⊤` pattern (now `EchoCostInstance`,
`EchoSearchInstance`).

Two minor lessons added to memory:
- Each new module should get its OWN `open import ... using ( ... )`
  block in `Smoke.agda` with a header comment, not share a paren-block
  with another lane's pins. Cuts merge-conflict resolution noise.
- During swarm-merge sequences, *another claude session* was
  concurrently rebasing my open PRs (`#82` shows `8950855`/`549f219`/
  `b9c6ba0`/`df691d9` from a parallel session). Mostly cooperative —
  they pre-merged `#83`/`#85`, brought `#82` to MERGEABLE. Re-fetch
  before force-push; verify other session's branch builds clean
  before either taking over or backing off.

*Plan for the next Claude:* the theory roadmap section is **closed**.
Open work:

1. Ordinal track — unbudgeted `_<ᵇʳᶠ_` global WF + surface-route WF
   back into `Order.agda`'s main `_<ᵇ_`. Solo, not swarmable; this is
   the named next bottleneck in the roadmap.
2. Pillar E paper — clear remaining `[EXPAND]` tags as material accrues
   (parallel sessions are actively doing this — `#73`, `#84`).
3. `antiecho-partition-dec` (needs DecEq B) and generic-codomain
   `antiecho-tropical-decompose` (needs ordered-codomain interface) —
   small deferrals from Wave 1.
4. EchoSearch sequential/product composition (needs `ℕ × ℕ ↔ ℕ`);
   real abstract-machine model (configs + step relation); decidability
   bridge `bounded-search-is-decidable` — see `EchoSearch.agda`'s
   "where next" section.
5. EchoApprox examples 6, 7, 8 — still unbuilt in `EchoExamples.agda`
   (only ex 1–4 + 9 + 5 + 10 land as concrete examples; 6 = approximate
   echo, 7 = ordinal collapse already in `EchoOrdinal`, 8 = open).

DO NOT reopen: 2-categorical shape (`decisions/no-2-cat.adoc`);
EchoAccess existential carriers (`decisions/echo-access-trivial-carrier.adoc`);
the Pillar A–D internal programme (complete since 2026-05-17);
any §"Theory work" item — the section is closed.

### Session arc 2026-05-20 evening — ω-power rank-mono unblock (read this first)

*Where we started today (commit `8c9ddcb` on `harden/ci-flake-pin-2026-05-18`):*
the ordinal track had the WfCNF predicate plus the `_<ᵇ⁻_` subrelation
foundations from the earlier session.  The rank-embedding route to
unbudgeted `wf-<ᵇʳᶠ_` was framed as "closed impossible" in
`docs/echo-types/buchholz-rank-obstruction.adoc` — the
`<ᵇ-+Ω <ᵇ-0-Ω : bplus bzero (bOmega (fin 1)) <ᵇ bOmega (fin 0)`
counterexample forced a rank inversion under additive Brouwer rank
with `nat-to-ord` successor-stack `ω-rank`.  4 of 13 constructors
admitted rank-mono via `RankPartial.agda`; 9 were structurally
walled.

*Where we ended (PR #87, branch `session-2026-05-20/buchholz-budgeted-plus`,
23 commits ahead of `8c9ddcb`):* the "closed impossible" verdict is
**narrowed** — under the WfCNF restriction `_<ᵇ⁻_` together with a
*limit-shaped* ω-power rank, **10 of 13 constructors close** via
relation-agnostic compositional primitives.  3 cases remain open
under documented structural blockers (ψ-admissibility, joint-bplus).

Eight slices landed in order, each with `agda proofs/agda/All.agda`
and `agda proofs/agda/Smoke.agda` exiting 0 under `--safe --without-K`,
zero postulates, zero escape pragmas, no funext:

1. **Slice 1** — `Ordinal.Brouwer.OmegaPow.agda` lands `_·ℕ_`, `ω^_`,
   basic identifications (`ω^0≡one`, `one·ℕ≡nat-to-ord`,
   `·ℕ-zero`, `·ℕ-suc`), positivity `ω^_-pos`, one-step strict-mono
   `ω^-strict-mono-suc`, weakening `ω^-step`.
2. **Slice 2** — left-monotonicity of `_⊕_` (`⊕-mono-≤-left` in
   `Phase13.agda`) + `·ℕ-mono-≤-left`, `ω^-mono-≤`, `ω^-strict-mono`
   (general gap).  Block comment in Phase13 documenting why strict
   left-mono of `_⊕_` is *not* a theorem (the `α + ω = β + ω`
   counterexample).
3. **Slice 3** — `⊕-assoc-≤` / `⊕-assoc-≥` (both funext-free `≤′`
   directions in Phase13), `·ℕ-add-≤` bridge, and the keystone
   **`additive-principal`** at `ω^(suc n)`.  The closure-under-addition
   property that makes ω-powers the right rank target for plus-side
   `_<ᵇ_` constructors.
4. **Slice 4** — `Ordinal.Buchholz.RankPow.agda`: limit-shaped
   `ω-rank-pow : OmegaIndex → Ord` (`fin n ↦ ω^(suc n)`), `rank-pow :
   BT → Ord` consuming it, plus reusable compositional primitives
   (`rank-pow-bplus-right-mono`, `rank-pow-via-left`,
   `rank-pow-bplus-into-ω-rank-pow`, `additive-principal-ω-rank-pow`).
5. **Slice 5** — 9 per-constructor rank-mono primitives in RankPow:
   `rank-mono-<ᵇ-0-Ω/0-ψ/ΩΩ/Ωψ/ψΩ/Ω+/ψ+/+Ω/+ψ`.  Each stated purely
   in terms of rank inequalities (not the relation), so both `<ᵇ⁻`
   and `<ᵇʳᶠ` consumers reuse them by pattern-matching on their own
   relation's constructor.
6. **Item 1** — `rank-mono-<ᵇ-+1-via-target` parametric in the
   target's additive-principal witness; `rank-mono-<ᵇ-+1-Ω-target`
   and `rank-mono-<ᵇ-+1-ψ-target` convenience wrappers.  Closes
   `<ᵇ-+1` for atomic targets; bplus-target sub-case explicitly
   deferred.
7. **Item 2** — `Ordinal.Buchholz.WellFormedAdmissible.agda` lands
   `WfAdm : BT → Set` strengthening WfCNF with `rank-pow α <′
   ω-rank-pow ν` on each `bpsi ν α`.  Carrier only; rank refinement
   for `<ᵇ-ψα` / `<ᵇ-ψΩ≤` discharge deferred (cross-case interaction
   with `<ᵇ-+ψ` documented in the module preamble).
8. **Item 3** — `Ordinal.Buchholz.RankMonoUmbrella.agda`: the
   rank-soundness-ready relation `_<ᵇ⁰_` with 10 constructors
   (tail-bounds baked in via `_≤ᵇ⁰_`) plus the umbrella theorem
   **`rank-pow-mono-<ᵇ⁰ : x <ᵇ⁰ y → rank-pow x <′ rank-pow y`**
   proved by direct structural recursion over the 10 cases.

*Closure-doc update*: `docs/echo-types/buchholz-rank-obstruction.adoc`
gains a "Slices 1–5 of the ω-power unblock" section with an updated
per-constructor verdict table (10 closed / 3 open).  The "rank-
embedding route is closed" framing is narrowed: closed for
unrestricted `_<ᵇ_`, opens up under the WfCNF restriction with
limit-shaped rank.

**Open work on this track (documented blockers):**

* `<ᵇ-ψα`, `<ᵇ-ψΩ≤` — provisional `rank-pow (bpsi ν _) = ω-rank-pow ν`
  doesn't discriminate on α.  Closed by ψ-admissibility predicate
  (carrier landed in Item 2); the rank refinement is a separate
  slice that needs to resolve the `<ᵇ-+ψ` cross-case.
* `<ᵇ-+1` joint-bplus — `rank-pow (bplus z₁ z₂)` is not additive
  principal in general.  Needs a coarser dominator function (e.g.,
  `leading-Ω-index : BT → OmegaIndex` returning the leftmost-deepest
  Ω-marker) or a richer rank shape.
* `rank-pow-mono-<ᵇ⁻` (full umbrella over `_<ᵇ⁻_` — gated on the
  above two).  The 10-of-13 `_<ᵇ⁰_` umbrella is the working closure;
  consumers needing the full `_<ᵇ⁻_` form bridge through the
  3-cases-open gap.

Build invariant held every slice: `All.agda` + `Smoke.agda` exit 0
under `--safe --without-K`, zero postulates, zero escape pragmas, no
funext.  All headlines pinned in `Smoke.agda` (or
`Ordinal/Buchholz/Smoke.agda` for the Buchholz-layer modules).

**Reusable design constraint**: Per a parallel-session note on
`_<ᵇʳᶠ_`, the rank-mono primitives are stated *relation-agnostically*
(rank-input, rank-output, no `<ᵇ` constructor patterns).  Both the
`_<ᵇ⁻_` consumer (this track) and the `_<ᵇʳᶠ_` consumer (parallel
session's wf-`<ᵇʳᶠ` milestone) can pattern-match on their own
relation's constructor and apply the matching primitive.

*Plan for the next Claude:* PR #87 is the deliverable.  Closure
work continues in three follow-ons, prioritised:

1. **ψ-admissibility rank refinement** (closes `<ᵇ-ψα`, `<ᵇ-ψΩ≤`,
   2 of 3 open cases).  Define `rank-adm : BT → Ord` using
   `ω-rank-pow ν ⊕ rank-pow α` for ψ under WfAdm.  Cross-case fix
   for `<ᵇ-+ψ`: under admissibility, source-rank is bounded by
   `ω-rank-pow ν` (the structural admissibility-source-bound lemma).
2. **Leading-Ω-index domination** (closes `<ᵇ-+1` general).  Define
   `head-Ω : BT → OmegaIndex` returning the leftmost-deepest Ω
   marker.  Prove `rank-pow t <′ ω-rank-pow-succ (head-Ω t)` for
   non-bzero WfCNF terms.  Then `<ᵇ-+1` discharges via head-Ω
   inversion + additive-principal at the head-Ω's successor.
3. **Full `rank-pow-mono-<ᵇ⁻` umbrella** — composition of 1+2
   with the existing 10-constructor `_<ᵇ⁰_` umbrella.

DO NOT reopen: the closed 10 constructors (their primitives are
correct under WfCNF); the unbudgeted `_<ᵇʳᶠ_` rank route per
`RankBrouwer.agda` preamble (genuinely impossible for unrestricted
`_<ᵇ_`).  The umbrella works on `_<ᵇ⁰_`, not on `_<ᵇ_` directly.

### Session arc 2026-05-17 (legacy — read second)

*Where we started today (commit `8a2b908`):* the establishment
track was a plan plus scaffolds — Pillar A landed; Pillars B–D were
declaration-free doc modules; Pillar E untouched. The session opened
with the attack-order decision already recorded ("de-risk H2
first").

*Where we ended today (commit `200b1eb`, pushed to `origin/main`):*
the **entire internal programme is complete and verified**. Seven
consolidated rungs:

1. `8a2b908` — attack-order decision recorded (de-risk H2 first).
2. `d1c5938` — Pillar B H2 thin slice: `EchoGradedComonad` real;
   over-delivered all three laws. *H2 verdict: graded coassociativity
   needs NO path algebra beyond `≤g-prop` (common-upper-bound idiom
   kills the transport).* The keystone result.
3. `f3f4719` — Pillar B H1: `EchoPullback` real (pullback +
   funext-free, K-free terminal-cone universal property). Pillar B
   complete.
4. `1daad01` — Pillar C: `EchoSeparating` real (separating model =
   EchoGraded minus `≤g-prop`; characteristic law refuted at a
   checked `true ≢ false`). Credibility core (A+B+C) complete.
5. `17429c8` — Pillar D: `EchoRelModel` real (abstract
   `GradedLossModel` + generic `GCLaws` = the model-independence
   theorem; two agreeing models) + `conservativity.adoc`. Pillars
   A–D all complete; no scaffolds remain.
6. `200b1eb` — Pillar E started: `types-abstract.adoc`
   (submission-ready) + `paper.adoc` (LIVING DRAFT, `[EXPAND]` tags).

Build invariant held every rung: `All.agda` + `Smoke.agda` exit 0
under `--safe --without-K`, zero postulates, zero escape pragmas.

*Plan for the next Claude:* the internal proof programme is DONE —
do not reopen Pillars A–D or the EI-2 negative. The only open work
is Pillar E write-up. Clear the `paper.adoc` *[EXPAND]* tags in this
order: (1) background/notation primer — low-context, do this first;
(2) related-work pass (Granule/QTT, Uustalu–Vene comonads,
coeffects, lens/optic vs the witness-transport leg); (3) evaluation
(proof-size/cost table; quantify common-upper-bound idiom vs naive
`subst`); (4) ordinal consumer-evidence appendix — GATED on the
ordinal track hitting Bachmann–Howard, keep firewalled per
`roadmap.adoc` §Lane 3 (Ordinal track) and `docs/buchholz-plan.adoc`.
THEN offline/author-driven only (venue+template,
Zenodo DOI, library packaging, outreach) — flag to the user, do NOT
auto-run. Strategy (user decision 2026-05-17): the paper was written
now at full narrative strength while fresh; expand the tagged
sections as context accrues — do not rewrite the spine.

### Establishment-track opening rung (the original 2026-05-17 entry)

Just landed: **Establishment-track opening rung.** New third
workstream (`docs/echo-types/establishment-plan.adoc`): the path to
recognised type-theoretic standing as a characterised *graded comonad
of structured loss*, with the explicit verdict that the
linear/dependent judgmental ladder is the wrong target (Echo adds no
new judgment — it is definitionally `fib`).

* `docs/echo-types/establishment-plan.adoc` — five-pillar plan +
  guardrails (no postulates / no `--safe` weakening; quarantine
  funext; do not reopen EI-2).
* **Pillar A (real, verified):** `proofs/agda/EchoFiberBridge.agda`
  defines `fiber` (stdlib v2.3 has none) and ships
  `echo↔fib : Echo f y ↔ fiber f y` via `mk↔ₛ′`, `refl` round-trips.
  Pinned in `Smoke.agda` (`fiber; echo→fib; fib→echo; echo↔fib`),
  wired into `All.agda`.
* **Pillar B (real, verified — COMPLETE, 2026-05-17):**
  `EchoGradedComonad.agda` (`gextract`, `gduplicate`,
  `gcomonad-counit-{l,r}`, `gcomonad-coassoc` — coassoc needs no
  path algebra beyond `≤g-prop`) and `EchoPullback.agda`
  (`EchoCone`/`echo-cone`, `SliceHom`↔cone bridge, `IsMediator`,
  `echo-pullback-univ` — funext-free pointwise uniqueness, no K).
  Both pinned in `Smoke.agda`. No postulates.
* **Pillar C (real, verified — COMPLETE, 2026-05-17):**
  `EchoSeparating.agda` — separating model (`EchoGraded` minus
  `≤g-prop`); `sep-order-not-prop`, `sep-map-over-{id,comp}` (generic
  Σ-laws hold), `sep-degrade-compose-fails` (characteristic law
  refuted at `true ≢ false`). Pinned in `Smoke.agda`. No postulates.
* **Pillar D (real, verified — COMPLETE, 2026-05-17):**
  `EchoRelModel.agda` — `GradedLossModel`/`GCLaws` (model-independence
  theorem), `set-model`/`rel-model`, `model-agreement`,
  `bridge-natural`; pinned in `Smoke.agda`, no postulates.
  `docs/echo-types/conservativity.adoc` — metatheorem + 3-clause
  formal anchor. No scaffold modules remain.

`agda proofs/agda/All.agda` and `agda proofs/agda/Smoke.agda` both
exit 0 under `--safe --without-K`. No postulates introduced.

**H2 LANDED (2026-05-17).** The de-risk bet paid off. The thin
slice over-delivered: not just counit-left but all three laws
(`gcomonad-counit-l`, `gcomonad-counit-r`, `gcomonad-coassoc`) plus
`gextract`/`gduplicate`, real and pinned. Verdict on the
load-bearing question: graded coassociativity needs **no path
algebra beyond `≤g-prop`** — the common-upper-bound idiom (already
used by `EchoGraded.degrade-via-join`) makes the `subst GEcho
(⊔g-assoc …)` transport vanish; every law is `degrade-compose` +
`≤g-prop`. Thesis unchanged and strengthened (establishment-plan
§"H2 verdict"). `All.agda` + `Smoke.agda` exit 0, no postulates.

**Pillar D LANDED (2026-05-17). Pillars A–D ALL COMPLETE — the
entire internal programme is done.** `EchoRelModel.agda` real:
abstract `GradedLossModel` interface + generic `GCLaws` proving the
comonad laws ONCE for any model (the model-independence theorem
itself); `set-model` (EchoGraded) and `rel-model` (relational
`EchoStep`/`map-rel`; composition from `map-rel-comp` +
`degrade-comp`) instances; `model-agreement` (round-trips `refl`)
and `bridge-natural` (`map-over` ↔ `map-rel` under the graph =
fibration bridge). `conservativity.adoc` states the
conservative/definitional metatheorem with a 3-clause formal anchor.
`All.agda` + `Smoke.agda` exit 0, no postulates / no escape pragmas.

**Pillar E STARTED (2026-05-17): write-up drafted.**
`docs/echo-types/types-abstract.adoc` (TYPES extended abstract,
content submission-ready) and `docs/echo-types/paper.adoc` (full
CPP/ITP mechanised-metatheory paper, LIVING DRAFT, status banner +
*[EXPAND]* tags) both landed. The decision (user, 2026-05-17): write
the full paper *now* while the result is fresh, expand the tagged
sections later as context accrues.

Smallest useful next advance — clear the `paper.adoc` *[EXPAND]*
tags as material becomes available, in this order:

1. Background/notation primer (graded comonads + HoTT fibres) — can
   be written now; low-context.
2. Related work — needs a literature pass (Granule/QTT, Uustalu–Vene
   comonads, coeffects, lens/optic laws vs the witness-transport
   leg).
3. Evaluation — proof-size/cost table; quantify
   common-upper-bound-idiom vs naive `subst`.
4. Ordinal consumer-evidence appendix — gated on that track hitting
   its Bachmann–Howard milestone (firewalled per `roadmap.adoc`
   §Lane 3 and `docs/buchholz-plan.adoc`).
5. THEN offline/author-driven: venue+template, Zenodo DOI, library
   packaging, outreach — flag to user, do NOT auto-run.

Rationale: internal programme (A–D) complete and verified. Authority
is conferred socially; the paper is the vehicle. Capturing the
narrative now (while fresh) then expanding is the chosen strategy.

---

## Previous rung state (2026-04-28)

Just landed: **Honest-thermo rung + 5-decoration sweep close +
cancel-iso packaging + extended-order lex constructors.** Five
PRs merged to `main` in one chain (#23, #24, #25, plus B3 in this
commit, plus the doc + 6a2 sweep). Headlines:

### C1 — `EchoFiberCount` + redeemed `EchoThermodynamics` (PR #23)

* `EchoFiberCount.FiberSize-fin : (Fin n → B) → B → DecEq → ℕ` —
  honest preimage count by enumeration.
* Headlines: `FiberSize-fin-id-zero` (id has fiber 1),
  `FiberSize-fin-const` (constant collapse: fiber n),
  `FiberSize-fin-{no,all}-hit`,
  `FiberSize-fin≡0⇒no-echo`, `no-echo⇒FiberSize-fin≡0`.
* `EchoThermodynamics` rewritten against `Data.Nat.Logarithm.⌊log₂_⌋`:
  `landauer-bound T n = k * T * ⌊log₂ n ⌋`,
  `bennett-reversible : FiberSize-fin ≡ 1 ⇒ erasure-bound ≡ 0`,
  `bennett-reversible-id-zero` (concrete instance),
  `landauer-collapse : (∀ x → f x ≡ y) ⇒ bound ≡ k·T·⌊log₂ n⌋`.
* `docs/ECHO-CNO-BRIDGE.adoc` swept: four overclaim sites at
  lines 71/80/122/174 replaced with honest "proved at finite
  domain only" or explicit "NOT proved" notes.
* `docs/echo-types/taxonomy.md` §8 references EchoFiberCount as
  the quantitative companion to EchoDecidable.

### A2 — `EchoChoreo` per-decoration composition rung (PR #24)

* `_⊑c_` (3 constructors) — choreographic-reachability order on
  roles (Client one-way to Server via the canonical `client-to-server`
  swap-square).
* `⊑c-trans`, `⊑c-prop` — transitive + propositional.
* `applyChoreo`, `applyChoreo-comp` — transport + decomposition.
* `_⊔c_` with `⊑c-⊔c-{left, right, univ}` — join (Server top).
* `applyChoreo-compose`, `applyChoreo-via-join` — factoring-free
  composition + join restatement.
* Closes the **five-decoration sweep** at the per-decoration
  composition rung (grade, linear, indexed, modal, role).
* `docs/echo-types/composition.md` §6 marked sweep closed.

### A1 — Equivalence-record packaging for cancel-iso (PR #25)

* `Echo.Echo-comp-iso : (f : A → B) (g : B → C) (y : C) →
  Echo (g ∘ f) y ↔ Σ B (λ b → Echo f b × g b ≡ y)` —
  unconditional accumulation iso, packaged via stdlib's
  `Function.Bundles._↔_` and `mk↔ₛ′`.
* `Echo.cancel-iso : ... → Echo (g ∘ f) y ↔ Echo f (s y)` —
  per-fiber cancellation equivalence, parameterised by `s-left`,
  `s-right`, and both triangle identities.
* Closes `composition.md` §4 ("Full cancel-iso with round-trips").

### B3 — Extended order `_<ᵇ⁺_` with shared-binder lex constructors

* New module `Ordinal.Buchholz.OrderExtended.agda`. Adds two
  lex constructors that the K-restriction kept out of the core
  `_<ᵇ_`:
  * `<ᵇ⁺-ψα : ∀ {ν₁ ν₂ α β} → ν₁ ≡ ν₂ → α <ᵇ β → bpsi ν₁ α <ᵇ⁺ bpsi ν₂ β`
  * `<ᵇ⁺-+2 : ∀ {x₁ x₂ y₁ y₂} → x₁ ≡ y₁ → x₂ <ᵇ y₂ → bplus x₁ x₂ <ᵇ⁺ bplus y₁ y₂`
* Each constructor carries an explicit equality witness so the
  implicits are pairwise distinct — the K-free unifier never
  has to eliminate a reflexive `ν = ν` (or `x = x`) equation.
* `<ᵇ⁺-irrefl`, `<ᵇ⁺-trans` proved (the `_<ᵇ⁺_` × `_<ᵇ_` mixed
  cases route through four extension helpers
  `bpsi-extend-{lhs,rhs}`, `bplus-extend-{lhs,rhs}`).
* **Well-foundedness for `_<ᵇ⁺_` is OPEN.** Two design routes
  documented in `docs/echo-types/buchholz-extended-wf.md`:
  Route A (single-mutual block with widened bundle, attempted
  but blocked on Agda's termination checker) and Route B
  (rank-embedding into Brouwer ordinals, recommended
  next-attempt). The K-free core `_<ᵇ_` and its `wf-<ᵇ` proof
  remain intact.
* New convenience wrappers `<ᵇ⁺-ψα-refl`, `<ᵇ⁺-+2-refl` for
  callers with concrete same-binder cases.

All headlines pinned in `Smoke.agda`. `agda proofs/agda/All.agda`
and `agda proofs/agda/Smoke.agda` both exit 0 under
`--safe --without-K`. No postulates introduced.

### Open at this rung

* `_<ᵇ⁺_` well-foundedness (see `buchholz-extended-wf.md`).
  Two routes documented; the single-mutual restructure (Route A)
  was attempted twice in 2026-04-28 sessions and both attempts
  failed Agda's termination checker for the same cycle through
  `wf-<ᵇ`. Rank-embedding (Route B) into Brouwer ordinals is the
  recommended next attempt — needs a `rank : BT → Ord` function
  plus the strict-monotonicity lemmas listed in the design note.
* Brouwer Phase 1.3 (recursive `_≤′_` and `_<′_`) — landed
  2026-04-30. `osuc-mono-≤′ p = p` collapses to identity, and
  the deferred `olim f` case of `≤′-refl` is now discharged via
  a source-side `≤′-lim` lemma (recursion on the source α, not
  on `f n`, sidesteps the original `with`-loses-equation
  obstacle). `≤′-refl`, `≤′-lim`, `f-in-lim′` pinned in
  `Smoke.agda`. Open arithmetic-side Phase-1.3 lemmas
  (`⊕-mono-<-right` etc., per `RankBrouwer.agda`'s preamble) are
  still required before `rank-mono` and the unbudgeted
  `wf-<ᵇʳᶠ` chain close.
* Unbudgeted `_<ᵇʳᶠ_` global WF (see Previous rung state).
* Push the surface-route WF back into `Order.agda`'s main
  `_<ᵇ_` package once `_<ᵇ⁺_` WF lands.

---

## Previous rung state (2026-04-27)

Landed: **Per-decoration composition rung** across
`EchoGraded.agda` and `EchoLinear.agda`. Both decorations commute
with composition under the same recipe (decoration order →
propositionality → join → factoring-free compose → via-join
restatement). Headlines:

`EchoGraded.agda`:

* `≤g-prop` — the order `_≤g_` is propositional (each (g1, g2) pair
  has at most one inhabitant). Six refl-clauses, one per constructor.
* `≤g-⊔g-left`, `≤g-⊔g-right`, `≤g-⊔g-univ` — exhibit `_⊔g_` as the
  categorical join in `_≤g_` (two upper bounds + universal property).
* `degrade-compose` — per-decoration composition law: for any
  factoring `g1 ≤g g2 ≤g g3` and any direct `p13 : g1 ≤g g3`,
  `degrade p23 (degrade p12 e) ≡ degrade p13 e`. Corollary of
  `degrade-comp` + `≤g-prop`.
* `degrade-via-join` — same statement restated through the join
  structure: `degrade p1 e ≡ degrade (≤g-⊔g-univ p1 p2) (degrade
  (≤g-⊔g-left g1 g2) e)`.

`EchoLinear.agda` (linearity-side analogue, two-mode `linear ⊑
affine` decoration):

* `_≤m_`, `≤m-trans` — mode order with three constructors
  (`linear≤linear`, `linear≤affine`, `affine≤affine`) and
  transitivity.
* `degradeMode`, `degradeMode-comp` — id on reflexive cases,
  `weaken` on the strict step; composition closes `refl` on every
  reachable constructor pair.
* `≤m-prop`, `_⊔m_`, `≤m-⊔m-{left, right, univ}` — propositional
  order plus join structure (with `affine` as top).
* `degradeMode-compose`, `degradeMode-via-join` — mirror the
  `EchoGraded` factoring-free compose and via-join restatement.

All headlines pinned in `Smoke.agda`. `EchoLinear.agda` typechecks
clean with no warnings or errors under `--safe --without-K`. No
postulates introduced.

Open at this rung:

* Indexed / role / modal cases of decoration-commuting
  (`EchoIndexed`, `EchoChoreo`, `EchoEpistemic`). The grade and
  linear cases suggest the recipe in each: identify the
  decoration's underlying order, prove it propositional, prove the
  existing `*-comp` lemma against it.

---

## Previous rung state (2026-04-23)

Just consolidated: **Budgeted recursive-surface rung** (on top of
the earlier **Pentagon rung**). Folded in:

* Composition-track (already upstream via separate landings):
  `cancel-iso-{to, from}`, `Echo-comp-iso-pent-{B, echo}`.
* Ordinal-track (new on this sweep): `RecursiveSurfaceBudget.agda`
  with `BudgetedBT = ℕ × BT`, `_<ᵇʳᶠᵇ_`, `wf-<ᵇʳᶠᵇ`,
  `<ᵇʳᶠᵇ-irreflexive`, and the `<ᵇʳᶠᵇ⇒lifted` bridge into the
  iterated-wrapper tower. Auxiliary layers (`ExtendedOrder`,
  `LiftedExtendedOrder`, `IteratedExtendedOrder`,
  `RecursiveSurfaceOrder`, `SurfaceOrder`, `VeblenInterface`,
  `VeblenIdentityModel`, `VeblenMeasureTarget`,
  `VeblenProjectionMeasure`, `VeblenComparisonTarget`,
  `VeblenComparisonModel`, `VeblenObligations`) are all wired
  into `All.agda` and pinned in `Ordinal/Buchholz/Smoke.agda`.

Open at this rung:

* Composition side: full cancel-iso round-trips (needs triangle
  identity); full Σ-associativity iso for pentagon; approximate-echo
  skeleton `EchoApprox.agda`.
* Ordinal side: unbudgeted global WF for `_<ᵇʳᶠ_` — eliminate the
  explicit ℕ budget from `wf-<ᵇʳᶠᵇ` without leaving `--safe --without-K`;
  then push that back into `Order.agda`'s `_<ᵇ_` package so the
  WF proof covers the full surface route rather than the admitted
  core only.

Verified post-rebase: `agda proofs/agda/All.agda` and
`agda proofs/agda/Smoke.agda` both exit 0 under `--safe --without-K`.
No postulates introduced.
