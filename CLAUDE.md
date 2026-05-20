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
- ArghDA (planned) — lightweight proof-workspace manager for Agda;
  triage folders (inbox → working → proven/rejected), linter, DAG view.
  Split as `arghda-core` (language-agnostic engine) + `arghda-panll`
  (Gossamer/ReScript presentation). See docs/buchholz-plan.adoc appendix
  for the motivating proof pipeline.

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
   `docs/echo-types/roadmap.md`, `docs/echo-types/overview.md` and
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

## Current rung state (2026-05-20)

### Session arc 2026-05-20 (read this first)

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

*Plan for the next Claude:* the theory roadmap section is essentially
closed. Open work:

1. Lane 2 (EchoApprox `BalancedTolerance` + B/budget round-trip) —
   should land cleanly per the agent's recommendation; verify when it
   completes.
2. Ordinal track — unbudgeted `_<ᵇʳᶠ_` global WF + surface-route WF
   back into `Order.agda`'s main `_<ᵇ_`. Gated on the K-free shared-binder
   restructure (B1).
3. Pillar E paper — clear remaining `[EXPAND]` tags as material accrues
   (parallel sessions are already doing this — see `#73`).
4. `antiecho-partition-dec` (needs DecEq B) and generic-codomain
   `antiecho-tropical-decompose` (needs ordered-codomain interface) —
   small deferrals from this session.
5. New `EchoCost.agda` / `EchoSearch.agda` slices (mentioned in the
   2026-05-20 Gate 1 refresh; presumably from other sessions) extend
   Axis 8 further — no action needed here, but downstream callers may
   need to mirror their composition recipes.

DO NOT reopen: 2-categorical shape (ruled out via `decisions/no-2-cat.adoc`);
EchoAccess existential carriers (closed via `decisions/echo-access-trivial-carrier.adoc`);
the Pillar A–D internal programme (complete since 2026-05-17).

### Session arc 2026-05-17 (read this first)

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
`roadmap.md`. THEN offline/author-driven only (venue+template,
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
   its Bachmann–Howard milestone (firewalled per roadmap.md).
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
