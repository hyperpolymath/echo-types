<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell -->

# Echo bridge repository inventory — 2026-11-06

Original source-inspection stage: a read-only inventory, not a new compiler run, theorem certification, or novelty claim. Queried GitHub through the connected GitHub file reader and authenticated `gh api`; every source link below is commit-pinned. Related repositories were not changed. Ordinal mathematics and dormant mirrors were excluded.

Echo's observed remote main is `c3407350844fe4d882fe2c63e9b97f5bbbf441b5` (2026-11-06T15:23:09Z). The foundation implementation discussed here was merged at `007d749ec02b3836b45a2183ebbbaf72935c9d91`; this inventory does not establish compatibility of any sibling's older pins with today's Echo. Local coordinating work after these pins is outside the remote snapshot.

The subsequent [local sibling compatibility checks](2026-11-06-sibling-compatibility.md)
rechecked three named integration roots with Echo's toolchain and current imported
core/residue sources. Those successful checks extend the evidence for that bounded
cone; they do not turn every direction below into a checked bridge. This inventory
retains its original repository pins, remote receipts and source-only conclusions.
Raw local paths in either report identify local-only receipts, not remotely
available evidence links.

## Identity and proof receipts

All seven repositories resolve to the listed `hyperpolymath` owner, have default branch `main`, and are not archived. No repository rename was observed through these API responses; stale names inside comments are not treated as canonical names.

| Repository | Exact main SHA | Relevant check observed at that SHA |
|---|---|---|
| mathesis | `1a582f2e860bb395207b4b181f9fdfb2fa313fa8` | No Agda/typecheck check found among 40 check-runs. Its path-filtered Agda workflow last succeeded at older `d0e5dcb41ce15c62c2e10c9a1814606f809bed7a`, [run 41261830874](https://github.com/hyperpolymath/mathesis/actions/runs/41261830874). |
| tropical-types | `168f09d1df8bc239d41bc0f9d9d18575b2c9c9d5` | `lake-build` SUCCESS, [40522723416](https://github.com/hyperpolymath/tropical-types/actions/runs/40522723416). |
| choreographic-types | `5a2a6cf1c657d7819558bf38b85ed11e2170ad1b` | Core, Echo-additive, rejection and minimal-law job SUCCESS, [42098842465](https://github.com/hyperpolymath/choreographic-types/actions/runs/42098842465). |
| epistemic-types | `a4a7a533f11996e9f57e67466566d950322b0d4f` | Both core/rejection and Canonical Echo correspondence SUCCESS, [42049048670](https://github.com/hyperpolymath/epistemic-types/actions/runs/42049048670). |
| secret-types | `42ac315bc8ec1f8d9ce30e4b8d97c02830645bd9` | Actual Agda core/countermodels/rejections/minimal-laws job SUCCESS, [42015215879](https://github.com/hyperpolymath/secret-types/actions/runs/42015215879). Separate template “Proven” job FAILED ([42015215543](https://github.com/hyperpolymath/secret-types/actions/runs/42015215543)); Cargo job skipped. Not blanket green. |
| residual-evidence-types | `14c93f4e19aaacbcfeca91bf5f2368d3e7b5a4bc` | Core/rejections/sibling comparisons SUCCESS, [41852563779](https://github.com/hyperpolymath/residual-evidence-types/actions/runs/41852563779). |
| resource-algebra | `e25d35d8facd773860f094979598facf92d38412` | Core/rejections SUCCESS, [41678685615](https://github.com/hyperpolymath/resource-algebra/actions/runs/41678685615). Added because choreographic code actually imports it. |

A successful check-run is remote execution evidence for its named scope; job logs and every theorem body were not independently recompiled here.

## Mathesis: discovery/evidence seam, not an Echo mathematics library

[README](https://github.com/hyperpolymath/mathesis/blob/1a582f2e860bb395207b4b181f9fdfb2fa313fa8/README.adoc) explicitly keeps proofs in their home repositories. [Atlas contract](https://github.com/hyperpolymath/mathesis/blob/1a582f2e860bb395207b4b181f9fdfb2fa313fa8/docs/atlas/README.adoc) describes generated repository discovery from census counts, not theorem-level certification. Useful paths: `docs/catalogue/census/catalogue-rows.json`, `docs/atlas/generated/index.json`, `scripts/atlas/census-atlas.mjs` (`build/check/find/context`).

`src/core/` and `src/bridges/` contain only .gitkeep in the inspected tree. [Properties.agda](https://github.com/hyperpolymath/mathesis/blob/1a582f2e860bb395207b4b181f9fdfb2fa313fa8/verification/proofs/agda/Properties.agda) is a generic template (list append length, monotone successor); `verification/proofs/lean4/ApiTypes.lean` is explicitly a replace-your-API template. These are not independent Echo proof legs. The Agda policy workflow uses floating Ubuntu apt Agda/stdlib, then `scripts/check-proofs.sh agda` adds safe/without-K/cubical-compatible. Its older receipt does not certify current catalogue claims.

**Direction only:** a source-anchored Echo claims/context pack could feed Mathesis discovery. The atlas explicitly says its summarized data cannot supply theorem names, assumptions, equivalence or independent-check receipts; a claims registry is future work.

## Tropical + resource algebra: distinguish the contracts

[Lean ResidueMeasure](https://github.com/hyperpolymath/tropical-types/blob/168f09d1df8bc239d41bc0f9d9d18575b2c9c9d5/Resource/EchoBridge.lean#L53) contains `combine, empty, measure, measure_empty, measure_combine`; the latter preserves sequential resource multiplication. It does **not** require associativity or unit laws on the residue carrier despite its “monoid” prose. Theorems about combining with empty prove equality of measured grades, not equality of residues. Its inhabited example measures `List Unit` length into max-plus. No actual Echo dependency is imported.

[Lean ResourceSemiring](https://github.com/hyperpolymath/tropical-types/blob/168f09d1df8bc239d41bc0f9d9d18575b2c9c9d5/Resource/Algebra/Interface.lean#L58) requires semiring laws including distributivity and annihilation, but not additive idempotence. [ResourceAlgebra](https://github.com/hyperpolymath/tropical-types/blob/168f09d1df8bc239d41bc0f9d9d18575b2c9c9d5/Resource/Algebra/Ordered.lean#L39) adds a supplied preorder and monotonicity; antisymmetry is in a separate record. `Instances/MaxPlus.lean`: bot plus Nat; alternative=max, sequence=addition. `Resource/Bridge.lean` relates session grade and adapter-cost results. `Resource.lean` imports the bridge modules.

The Lean workflow pins 4.35.0, builds both Lake roots, and audits selected declarations for `sorry`/Classical.choice; its documented allowance includes propext/Quot.sound. This is not Agda's assumption profile, nor cross-prover equivalence.

[Agda ResourceAlgebra.Core](https://github.com/hyperpolymath/resource-algebra/blob/e25d35d8facd773860f094979598facf92d38412/src/ResourceAlgebra/Core.agda) instead requires an idempotent commutative alternative monoid plus a sequential monoid. Its induced order `a ≼ b := a ⊕ b ≡ b` has derived antisymmetry. Monotonicity, distributivity and annihilation are separate `IsOrdered/IsDioid/IsAnnihilating` records.

[Agda Morphism](https://github.com/hyperpolymath/resource-algebra/blob/e25d35d8facd773860f094979598facf92d38412/src/ResourceAlgebra/Morphism.agda) separates strict Hom (both units and operations) from LaxHom (one, alternatives, and an upper bound for sequencing). HWM→MaxPlus is lax, not strict. MaxPlus and Loss are transcriptions with re-proved local laws; their comments explicitly leave Lean/Agda or copied-definition correspondence as review obligations. Current proof script uses 2.6.4.3, safe/without-K/no-libraries/ignore-interfaces/double-check. Workflow image/runner float.

**Directions only:** Echo residue measurement can target these algebras with explicit preservation laws. A Lean↔Agda record bridge needs additional idempotence, law and order correspondence; no blanket interface equivalence follows. Measure equality does not recover source identity or confer a full graded (co)monad.

## Choreographic Types: existing grade bridge, scoped projection theorems

[KCut](https://github.com/hyperpolymath/choreographic-types/blob/5a2a6cf1c657d7819558bf38b85ed11e2170ad1b/src/Choreographic/KCut.agda): `proj-cut`; `grade-proj` assumes Projectable; `kcut-loss` assumes Consistent cut; `kcut-loss-full` assumes Projectable. [Projection](https://github.com/hyperpolymath/choreographic-types/blob/5a2a6cf1c657d7819558bf38b85ed11e2170ad1b/src/Choreographic/Projection.agda) makes merge/projectability/consistency explicit for the finite binary-choice syntax.

[EchoAdditive](https://github.com/hyperpolymath/choreographic-types/blob/5a2a6cf1c657d7819558bf38b85ed11e2170ad1b/src/Choreographic/Base/EchoAdditive.agda) imports Echo's actual additive Grade and proves a ResourceAlgebra instance and maps to/from Loss, including old-grade embedding agreement. It is a separate root from the builtins-only All. `Base/RoleGraded.agda` shows the three-grade embedding is not closed under sequential addition (`seq-escapes`). `Base/EchoProjection.agda` requires supplied grade/projection equalities for its commutation statements; it does not prove arbitrary-party transport. `WarrantClaim.agda` imports actual epistemic Warrant/SoundWarrant; `Transport.agda` imports its Preorder.

[Sibling pins](https://github.com/hyperpolymath/choreographic-types/blob/5a2a6cf1c657d7819558bf38b85ed11e2170ad1b/scripts/fetch-siblings.sh): resource-algebra `b2c9f1f6bc7ed7cc83c7573014cdf88d49d2a881`; epistemic `495db9cca003e12066a3cb9c9f2d7afa1a953aec`; Echo `da140cc26fd174b20d5d7fcfafcb4febd3276ff3`. CI uses Debian Agda 2.6.4.3/stdlib 2.1-4, safe/without-K/cubical-compatible/ignore-interfaces/double-check; UnsupportedIndexedMatch is suppressed in its strict pass. Core/tests reject postulates; one sanctioned RapidNJ application postulate block is outside the proof gate.

**Direction only:** instantiate relation/fibre observations of projected behaviours while keeping Projectable/Consistent premises. Grade embedding and witness retention are distinct obligations. Recursion/full merge/delegation are not established by this source inspection.

## Epistemic Types: certificates, recovery and sound transport

[EchoBridge](https://github.com/hyperpolymath/epistemic-types/blob/a4a7a533f11996e9f57e67466566d950322b0d4f/src/EpistemicTypes/EchoBridge.agda) has Retention(observe, retain, Cert, sound), certificate-bearing Echo, MatchesSource (compatibility rather than execution provenance), Recovery with a left inverse of the actual retained pair, Migration with target-specific adequacy, and `collisionForbidsMigration`. Names alone do not make Cert sound for an unstated interpretation.

[CanonicalEcho integration](https://github.com/hyperpolymath/epistemic-types/blob/a4a7a533f11996e9f57e67466566d950322b0d4f/tests/integration/CanonicalEcho.agda) imports actual Echo/EchoResidue and proves representation round trips and lowering agreement. CI pins Echo `46cd1a32d4dcf1020f01dd1aab41f816742da10e`, not current main.

[Warrant](https://github.com/hyperpolymath/epistemic-types/blob/a4a7a533f11996e9f57e67466566d950322b0d4f/src/EpistemicTypes/Warrant.agda) is deliberately non-factive; SoundWarrant adds Evidence→A. `ProofTransport.agda` requires a supplied Meaning and a verifier whose successful check entails that exact holder/artifact/claim meaning. `Kripke/Residual.agda` represents evidence-refined candidate accessibility and proves presence without identification; it locally reconstructs the residual shape rather than importing that repository.

CI pins Agda 2.6.4.3; core is builtins-only, recursive per-module checking, safe/without-K/cubical-compatible/double-check/ignore-interfaces. A strict pass suppresses UnsupportedIndexedMatch, paired with a second pass matching exactly 23 allowed source spans. Canonical Echo uses stdlib 2.1-4 and suppresses that warning category. Do not describe either as warning-free.

**Directions only:** connect current Echo's source-preserving criterion to retained-pair recovery; lift residue transformations through explicit certificate preservation; distinguish pointwise correctness from function equality and execution provenance.

## Residual Evidence: the most direct existing Echo correspondence

[Core](https://github.com/hyperpolymath/residual-evidence-types/blob/14c93f4e19aaacbcfeca91bf5f2368d3e7b5a4bc/src/ResidualEvidence/Core.agda):
`Candidate observe r E = Σ world, (observe world ≡ r) × E world`.
Case stores one consistency witness; Holds quantifies over **all** candidates. Identified requires one query value shared by every candidate. Actual-world soundness explicitly needs both observation equality and evidence at that actual world.

[EchoComparison](https://github.com/hyperpolymath/residual-evidence-types/blob/14c93f4e19aaacbcfeca91bf5f2368d3e7b5a4bc/tests/integration/EchoComparison.agda) imports actual Echo, proves round trips with `Σ (Echo observe r) (E ∘ proj₁)`, transports evidence-context composition with a joint Case premise, and transports coarse claims back to fine cases. It explicitly does not identify evidence-context composition with Echo function-composition isomorphism.

[EpistemicComparison](https://github.com/hyperpolymath/residual-evidence-types/blob/14c93f4e19aaacbcfeca91bf5f2368d3e7b5a4bc/tests/integration/EpistemicComparison.agda) constructs actual SoundWarrants, proves inhabited-case non-vacuity, and supplies a counterexample token showing arbitrary warrants can remain non-factive. Retraction/revision require retained support and, for revision, an inhabited revised case. Core Revision represents removal/replacement of evidence assumptions, not unrestricted truth preservation.

CI: Agda 2.6.4.3, builtins-only core, safe/without-K/no-libraries/ignore-interfaces/double-check. [Pinned comparisons](https://github.com/hyperpolymath/residual-evidence-types/blob/14c93f4e19aaacbcfeca91bf5f2368d3e7b5a4bc/scripts/fetch-siblings.sh) use Echo `9c4b72b52972c7e084c8f569635eb01caef64e7a`, epistemic `dd948fbdddbdd06282cda8425e3e644e013c11ff`, stdlib `97bc55e47367c562b3032bf104f2a00b19716f88`. Actual script is `scripts/check-siblings.sh`; a guessed `check-comparisons.sh` returned 404 and was not treated as evidence.

**Direction only:** recheck the existing comparison against current Echo before adding a new representation; dependent pushforward may package evidence-bearing fibres, but coherence/revision semantics need their own statements and checks.

## Secret Types: checked TINI, not declassification

Its GitHub description says specification-only, but the inspected tree and proof job contain an actual checked core. [Lattice.Record](https://github.com/hyperpolymath/secret-types/blob/42ac315bc8ec1f8d9ce30e4b8d97c02830645bd9/src/SecretTypes/Lattice/Record.agda) requires transitivity and two join upper-bound laws, not a full lattice. Observer is a downward-closed visible-label predicate.

[Generic noninterference](https://github.com/hyperpolymath/secret-types/blob/42ac315bc8ec1f8d9ce30e4b8d97c02830645bd9/src/SecretTypes/Noninterference/Generic.agda) proves TINI. [Statement](https://github.com/hyperpolymath/secret-types/blob/42ac315bc8ec1f8d9ce30e4b8d97c02830645bd9/src/SecretTypes/Noninterference/Statement.agda) requires a typed command, observer-equivalent initial stores and **both successful** fuelled executions; fuels may differ. Stores are Var→Nat, and observer equivalence is pointwise equality of visible coordinates. The generic proof uses decidable Nat equality to establish stability of this pointwise agreement; it does not add decidability of every visible-label predicate or global function extensionality. Lang has skip/assignment/sequence/if/while, no declassification constructor. Witness has real explicit/implicit leaks and a termination-sensitive counterexample. Declassification and termination-sensitive NI remain open.

CI pins Agda 2.6.4.3, safe/without-K/no-libraries/ignore-interfaces/double-check with warnings as errors. Cubical-compatible is explicitly waived; template proof files are not independent theorem legs. PROOF-STATUS's “Mathesis Grade 3” is that repository's report, not an endorsement of a ratified Mathesis grading standard (Mathesis itself calls its architecture proposal unratified).

**Direction only:** an observer's equivalence class can supply a relation-valued Echo observation seam. Do not turn pointwise store equality into function equality without an explicit principle, or infer audited declassification from TINI.

## Reproduction / evidence boundary

Successful commands used, with each REPO/SHA set to the table above:

```powershell
gh api repos/hyperpolymath/REPO
gh api repos/hyperpolymath/REPO/commits/main
gh api "repos/hyperpolymath/REPO/git/trees/SHA?recursive=1"
gh api "repos/hyperpolymath/REPO/commits/SHA/check-runs?per_page=100"
gh api "repos/hyperpolymath/mathesis/actions/workflows/agda-proof-policy.yml/runs?per_page=3"
```

Source contents were read through GitHub `fetch_file(repository_full_name, path, ref=SHA)`, including the linked interfaces, their scripts and workflows. Recursive trees were not truncated. During this original source-inspection stage, no sibling compiler, package installer, migration, mutation, mirror or external review was run. “Source inspected” and “remote check observed” are the evidence levels here; each proposed new bridge remains unverified until its actual statement, assumptions and current source pin are checked.
