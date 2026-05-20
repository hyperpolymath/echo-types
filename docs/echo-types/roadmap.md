# Echo Types — Roadmap

**Status:** planning document. Partitions work by dependency on the
two identified bottlenecks:

For current cross-repo progress snapshots, see
`cross-repo-bridge-status.md`.

- **Bottleneck B1 (RECAST 2026-05-20).** The remaining gap between
  the closed Veblen/current-core route and the full intended
  Buchholz order: the historically blocked shared-binder shapes in
  `_<ᵇ_`. `wf-<ᵇ` is landed for the currently admitted core; the
  shared-binder shapes (`<ᵇ⁺-ψα`, `<ᵇ⁺-+2`) now have a *budgeted*
  WF carrier in `Ordinal.Buchholz.OrderExtendedBudget.wf-<ᵇ⁺ᵇ`
  (mirroring the existing `wf-<ᵇʳᶠᵇ` for the recursive surface).
  **The unbudgeted promotion is structurally impossible** for the
  current `_<ᵇ_` — see `buchholz-rank-obstruction.adoc`. The
  Echidna-SA-recommended rank-into-Brouwer route fails on the
  ordinally-unsound `<ᵇ-+Ω` constructor; all four alternative
  routes (direct mutual structural recursion, tower-stratification,
  lex measure into ℕ, inverse-image into the budgeted relation) are
  also walled. Recovering unbudgeted WF requires either restricting
  `_<ᵇ_` to a `WellFormed` subset (2–3 weeks of constructor-by-
  constructor rework) or providing a non-additive denotational
  measure (essentially solving Buchholz WF "from the model up").
  The "B1" framing is therefore now: *accept the budgeted forms as
  canonical*, or *commit to one of the two substantial paths*.
- **Bottleneck B2.** Tool-scope limitations on adjacent repos
  (`maa-framework/absolute-zero`, `januskey`,
  `tropical-resource-typing`). Blocks end-to-end bridge audits.

Paths marked **[unblocked]** can proceed today. Paths marked
**[gated on B1]** or **[gated on B2]** cannot.

---

## Theory work — no proof assistant needed

- **[landed]** Axis 2 (approximate echoes): formal definition,
  distinguishing test, examples, and composition theorem all in
  `taxonomy.md` §2 (lines 38–64). `EchoApprox.agda` ships
  `EchoR ε f y`, three headline lemmas (`echo-approx-intro`,
  `echo-approx-relax`, `echo-approx-compose`). Pinned in
  `Smoke.agda`. Compiler-analysis widening application worked in
  `applications-compiler-analysis.adoc` example 2.
- **[landed]** Axis 8 (information-theoretic vs computational
  access): four refinements all have first artifacts (2026-05-20):
  `EchoCost` (refinement 1, scalar ledger), `EchoAccess`
  (refinement 2, two-point modal lattice), `EchoDecidable`
  (refinement 3, Dec layer, earlier), `EchoSearch` (refinement 4,
  bounded-enumeration extractor). The four form a small lattice
  with bridges between them. Operational upgrades remain open
  (resource monad for refinement 1, step-counter abstract machine
  for refinement 4).
- **[unblocked]** Negative / co-echoes: formulate `CoEcho(f)` and its
  relationship to `Echo(f)`. Possibly resolves the quantitative /
  structural tension hinted at by `EchoTropical`.
- **[unblocked]** 2-categorical shape: commit to a 2-category or
  rule it out. Either answer unblocks the composition roadmap.
- **[unblocked]** Presentation-dependence sub-theory: examples 5, 9,
  10 cluster here; write up the common pattern.
- **[unblocked]** Gate 1 adjacency refresh: the five existing
  adjacency notes predate the taxonomy. Cross-check each against the
  current axes and flag any neighbour whose identity claim should
  be re-evaluated.

---

## Formalisation work — Agda, no bottleneck

- **[landed]** `Echo-comp-iso` in `Echo.agda`: the accumulation
  isomorphism `Echo(g ∘ f) y ≃ Σ B (λ b → Echo(f) b × (g b ≡ y))`.
  Shipped as `Echo-comp-iso-{to, from, from-to, to-from}`; both
  round-trips are definitional. See `composition.md` §1.
- **[landed]** `cancel-iso-to` / `cancel-iso-from` /
  `cancel-iso-from-to` / `cancel-iso-to-from` in `Echo.agda`,
  packaged as `Echo.cancel-iso : ... → Echo (g ∘ f) y ↔ Echo f (s y)`
  via stdlib's `Function.Bundles._↔_` and `mk↔ₛ′`. Both round-trips
  parameterised by their respective triangle identities (one
  triangle implies the other in HoTT but the adjustment is
  non-trivial path algebra, so both stay explicit). Companion
  `Echo.Echo-comp-iso` packages the unconditional accumulation iso
  the same way. See `composition.md` §3 + §4.
- **[landed]** Pentagon coherence for three-fold composition.
  Projection lemmas `Echo-comp-iso-pent-B` and `Echo-comp-iso-pent-echo`
  both `refl` in `Echo.agda`. The full Σ-associativity iso between the
  two nested Σ-shapes (outer-first carries an extra intermediate
  `c : C` with `g b ≡ c`; inner-first absorbs it) now ships as
  `Echo-comp-pent-Σ-assoc-{to, from, from-to, to-from}`. The forward
  map collapses `c` against `g b ≡ c` and transports the outer
  h-equation; the backward map sets `c := g b` with `refl`. Both
  round-trips reduce definitionally once the `g b ≡ c` has been pinned,
  so this is a strict iso (no transport coherence required) and lives
  inside `--safe --without-K`. All four pinned in `Smoke.agda`.
- **[landed]** Budgeted recursive-surface WF on the ordinal track.
  `Ordinal/Buchholz/RecursiveSurfaceBudget.agda` ships
  `BudgetedBT = ℕ × BT`, the budgeted relation `_<ᵇʳᶠᵇ_` with its
  `spend` constructor, `wf-<ᵇʳᶠᵇ : WellFounded _<ᵇʳᶠᵇ_` (via
  subrelation on ℕ), and `<ᵇʳᶠᵇ⇒lifted` transporting each budgeted
  step into the iterated-wrapper tower (`IteratedExtendedOrder`).
- **[landed, 2026-05-20]** Budgeted shared-binder WF for the
  K-restricted extended order.
  `Ordinal/Buchholz/OrderExtendedBudget.agda` ships
  `BudgetedBT⁺ = ℕ × BT`, the budgeted relation `_<ᵇ⁺ᵇ_` with its
  `spend` constructor, and `wf-<ᵇ⁺ᵇ : WellFounded _<ᵇ⁺ᵇ_`. Mirrors
  the recursive-surface pattern but for the depth-1 shared-binder
  cases (`<ᵇ⁺-ψα`, `<ᵇ⁺-+2`).
- **[closed-impossible, 2026-05-20]** The unbudgeted global
  theorem — eliminate the explicit ℕ budget from `wf-<ᵇʳᶠᵇ` to get
  `WellFounded _<ᵇʳᶠ_`, or analogously for `_<ᵇ⁺_` — is
  structurally impossible for the current `_<ᵇ_`. The
  Echidna-SA-recommended rank-into-Brouwer route in
  `RankBrouwer.agda` was refuted by a worked counterexample on
  `<ᵇ-+Ω`. All four alternative routes also walled. See
  `buchholz-rank-obstruction.adoc` for the full analysis and the
  two substantial-work paths that could re-open the question
  (WF-restricted `_<ᵇ_` or non-additive denotational measure).
- **[landed]** `EchoApprox.agda`: new module for ε-indexed echoes
  over a metric codomain. First-class taxonomy axis 2 artifact.
  Ships `EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)` parametric over
  a `Tolerance` monoid and a `PseudoMetric`, with three headline
  lemmas: `echo-approx-intro` (exact ⇒ zero-ε), `echo-approx-relax`
  (monotone in ε), and `echo-approx-compose` (additive composition
  under a non-expansive outer leg, realising the taxonomy §2
  conjecture). Wired into `All.agda` and `Smoke.agda`.
- **[landed]** Per-decoration composition lemmas across the
  five-decoration family — **sweep complete** (2026-04-28):
  `EchoGraded.degrade-compose`, `EchoLinear.degradeMode-compose`,
  `EchoIndexed.map-role-indexed-comp`,
  `EchoChoreo.applyChoreo-{comp, compose, via-join}` along the
  choreographic-reachability order `_⊑c_`, and
  `EchoEpistemic.knowledge-monotone-{comp, id}`. Each follows the
  same recipe (decoration order → propositionality → join →
  factoring-free compose → via-join restatement). All headlines
  pinned in `Smoke.agda`.
- **[landed]** Honest finite-domain Landauer/Bennett bounds
  (2026-04-28). `EchoFiberCount.agda` provides the actual fiber
  count `FiberSize-fin : (Fin n → B) → B → DecEq → ℕ` plus four
  headline lemmas (`FiberSize-fin-id-zero`, `FiberSize-fin-const`,
  bidirectional `FiberSize-fin ≡ 0 ⟺ ¬ Echo`).
  `EchoThermodynamics.agda` rewritten against
  `Data.Nat.Logarithm.⌊log₂_⌋`: `bennett-reversible`,
  `bennett-reversible-id-zero`, `landauer-collapse`. Replaces the
  earlier `FiberSize = 1` hardcode that rendered the prior
  CNO-zero-energy claims vacuous. Infinite-domain
  (`ProgramState = ℕ → ℕ`) case explicitly out of scope.
  `docs/ECHO-CNO-BRIDGE.adoc` swept to remove four overclaim sites.
- **[partial]** Buchholz extended order `_<ᵇ⁺_` (2026-04-28,
  updated 2026-05-20). `Ordinal.Buchholz.OrderExtended.agda` adds
  the two K-restricted shared-binder lex constructors (`<ᵇ⁺-ψα`,
  `<ᵇ⁺-+2`) on top of the K-free core `_<ᵇ_`, with explicit
  equality witnesses to keep implicits pairwise distinct.
  `<ᵇ⁺-irrefl` and `<ᵇ⁺-trans` proved (mixed cases via four
  `extend-{lhs, rhs}` helpers).
  Well-foundedness in **budgeted form** for `_<ᵇ⁺_` landed
  2026-05-20: `Ordinal.Buchholz.OrderExtendedBudget` ships
  `wf-<ᵇ⁺ᵇ` (mirrors `wf-<ᵇʳᶠᵇ`). The **unbudgeted** form is
  CLOSED-IMPOSSIBLE for the current `_<ᵇ_` — see
  `docs/echo-types/buchholz-rank-obstruction.adoc` for the
  structural impossibility (`<ᵇ-+Ω` ordinal unsoundness)
  refuting all five plausible routes. The historical "Route A /
  Route B" framing in `buchholz-extended-wf.md` is now
  superseded.
- **[unblocked]** Add example-library Agda files matching
  `examples.md`: start with examples 1–4 already in-suite, then
  example 7 (ordinal collapse is in `EchoOrdinal`); examples 5, 6,
  9, 10 are new Agda candidates.

---

## Example work — mostly writing, some coding

- **[unblocked]** Complete worked numeric example (ex. 6) with the
  approximate-echo shape, once the definition lands.
- **[unblocked]** Parser residue example (ex. 9) as a toy Agda
  example: parse of balanced parens, echo carries token stream.
- **[unblocked]** Abstract-interpretation example (ex. 10) via a
  Sign lattice.
- **[unblocked]** Database provenance example (ex. 5) via
  K-provenance semiring — text-only pass first, Agda optional.
- **[unblocked]** Extend `EchoExamples.agda` with two to three
  further canonical entries.

---

## Application work — no proof assistant needed for first-pass prose

- **[unblocked]** **Compiler-analysis residue.** Write up how Echo
  Types names the residue produced by abstract interpretation,
  register allocation, SSA conversion, and constant folding.
  Cross-reference existing literature (e.g. Cousot/Cousot for AI,
  various works on "explainable compilation").
- **[unblocked]** **Database provenance.** Tie to K-provenance and
  the `Bag`-semiring tradition. The adjacency note already exists;
  extend into a discipline-specific Echo Types chapter.
- **[unblocked]** **Verification / refinement.** Relate Echo Types
  to refinement types and to proof-carrying code. The intensional
  witness is a "refinement that survives erasure".
- **[unblocked]** **ML interpretability / AI abstraction.** The most
  speculative. Echo Types could name the residue of information-
  losing layers in neural networks (pooling, attention heads,
  embedding projections). Write as a *speculative* chapter with
  explicit open questions; do not overclaim.
- **[unblocked]** **Concurrency / choreography.** `EchoChoreo.agda`
  already models role-observation echoes. Extend to a distributed-
  systems residue discipline.

---

## Proof-assistant-dependent work — gated

- **[partial]** Internalize the missing shared-binder shapes as
  actual constructors of the Buchholz order. **Done** for the
  irrefl + trans layer in `Ordinal.Buchholz.OrderExtended._<ᵇ⁺_`
  with `<ᵇ⁺-ψα` and `<ᵇ⁺-+2` (2026-04-28). Well-foundedness for
  the enlarged order is open — see the gated entry below.
- **[gated on `_<ᵇ⁺_` WF]** Re-close well-foundedness for the
  enlarged order. Two design routes documented in
  `docs/echo-types/buchholz-extended-wf.md`: single-mutual block
  with widened bundle (Route A — attempted, blocked on Agda
  termination) or rank-embedding into Brouwer ordinals (Route B
  — recommended next-attempt; scaffolded by
  `Ordinal.Buchholz.RankBrouwer.agda` from the parallel session).
- **[gated on B1]** Ordinal semantics of BT terms: denotation
  `BT → Ordinal` preserving order. Requires a formal `Ordinal` type
  as a prerequisite, which is itself downstream of WF.
- **[partial]** Landauer / Shannon rigorous bridge. **Done** for
  the finite-domain Landauer/Bennett shape in
  `EchoThermodynamics.agda` (rewritten 2026-04-28 against
  `EchoFiberCount.FiberSize-fin` and `Data.Nat.Logarithm.⌊log₂_⌋`).
  Open: infinite-domain `ProgramState = ℕ → ℕ` extension (needs a
  capacity / measure / equivalence-class-quotient framework);
  Shannon-entropy formalisation (no probability-monad in stdlib v2
  at the level needed); physical heat-dissipation realisation
  (the bound is information-theoretic, not a physical claim).
- **[gated on B2]** CNO-equivalence verification across echo-types
  and `absolute-zero`. Needs cross-repo access.
  Bridge slot now exists on the adjacent side at
  `absolute-zero/proofs/agda/EchoBridgeScaffold.agda`; theorem-level
  alignment remains open.
- **[gated on B2]** Janus reversible-file-operations bridge
  verification against `januskey`'s actual API. Needs cross-repo
  access.
- **[gated on B2]** Tropical-resource-typing alignment: first do a repo
  inventory (it is currently not recently audited), then validate
  `EchoTropical` witness/residue claims against that neighbouring
  tropical typing development.
- **[gated on B2]** `maa-framework` integration. Out of scope for
  the current tooling; needs scope expansion or file export.

---

## Suggested immediate ordering

This is my honest suggested ordering, conservative about what's
tractable today:

1. ~~**Theory: axis 2 formal definition**~~ — **landed**.
   Formal definition + composition theorem in `taxonomy.md` §2;
   `EchoApprox.agda` artifact with three headline lemmas; example 10
   (abstract interpretation widening) worked in
   `applications-compiler-analysis.adoc`.
2. ~~**Agda: `Echo-comp-iso` + cancellation**~~ — **fully landed**.
   Accumulation iso (`Echo-comp-iso`), both cancellation maps, plus
   **full cancellation iso with round-trips** (`cancel-iso-{to, from,
   from-to, to-from}` + packaging `Echo.cancel-iso : ... ↔ ...`
   parameterised by `s-left`, `s-right`, and both triangle
   identities) live in `Echo.agda`. All five pinned in `Smoke.agda`.
3. ~~**Agda: pentagon coherence for `Echo-comp-iso`**~~ —
   **fully landed**. Projection pentagon (`Echo-comp-iso-pent-{B,
   echo}`) and the full Σ-associativity iso between the two nested
   Σ-shapes (`Echo-comp-pent-Σ-assoc-{to, from, from-to, to-from}` +
   equivalence-record packaging `Echo-comp-pent-Σ-assoc : ... ↔ ...`)
   are both in `Echo.agda`. All pinned in `Smoke.agda`.
4. **Agda: unbudgeted `_<ᵇʳᶠ_` WF on the ordinal track** —
   **VERDICT NARROWED 2026-05-20 evening.** The "closed impossible"
   framing held for *unrestricted* `_<ᵇ_`.  Under the WfCNF
   restriction `_<ᵇ⁻_` together with a limit-shaped *ω-power* rank
   (`Ordinal.Brouwer.OmegaPow` + `Ordinal.Buchholz.RankPow`), the
   path-1 closure is now **10 of 13 constructors** via
   relation-agnostic rank-mono primitives (PR #87).  The umbrella
   theorem `rank-pow-mono-<ᵇ⁰ : x <ᵇ⁰ y → rank-pow x <′ rank-pow y`
   lives in `Ordinal.Buchholz.RankMonoUmbrella`; consumers
   (whether `_<ᵇ⁻_` or `_<ᵇʳᶠ_` based) construct `_<ᵇ⁰_`
   derivations and apply the umbrella.

   **3 cases remain open** under documented structural blockers
   (see `buchholz-rank-obstruction.adoc` for the per-constructor
   verdict table):
   * `<ᵇ-ψα`, `<ᵇ-ψΩ≤` — ψ-admissibility predicate carrier landed
     (`Ordinal.Buchholz.WellFormedAdmissible.WfAdm`); rank-refinement
     for the discharge is a follow-on slice with a `<ᵇ-+ψ`
     cross-case to manage.
   * `<ᵇ-+1` joint-bplus — `rank-pow (bplus z₁ z₂)` is not additive
     principal in general.  Needs a coarser dominator (e.g.,
     `leading-Ω-index : BT → OmegaIndex`).

   The keystone is the **additive-principal lemma at ω^(suc n)**
   (`Ordinal.Brouwer.OmegaPow.additive-principal`).  Budgeted forms
   (`_<ᵇʳᶠᵇ_`, `_<ᵇ⁺ᵇ_`) remain the canonical well-founded
   carriers until the 3-case gap closes.
5. **Gate 1 adjacency refresh against the new taxonomy** — 1 day.
   Cheap coherence pass on existing docs. Cross-check each of the
   13 notes in `docs/adjacency/` against the 8 axes in `taxonomy.md`
   and flag any neighbour whose identity claim should be re-evaluated.
6. **Theory: pick one axis-8 refinement and formalise it** — 1–2
   days. Four candidates in `taxonomy.md` §8 (cost-indexed echo,
   graded access modality, decidability-respecting echo, witness-
   search abstract machine). Choosing commits the repo to one
   formal handle on computational vs information-theoretic access.
7. ~~**Agda: `EchoApprox.agda`**~~ — **landed**.
   First artifact of axis 2. Ships `EchoR ε f y = Σ A (λ x → dist
   (f x) y ≤ ε)` parametric over a `Tolerance` monoid and a
   `PseudoMetric`, with three headline lemmas: `echo-approx-intro`
   (exact ⇒ zero-ε), `echo-approx-relax` (monotone in ε),
   `echo-approx-compose` (additive composition under a non-expansive
   outer leg). Wired into `All.agda` + pinned in `Smoke.agda`.
8. ~~**Applications chapter: compiler-analysis residue**~~ —
   **first draft landed 2026-05-20**.
   `docs/echo-types/applications-compiler-analysis.adoc` with two
   worked examples (parser error recovery on axis 4;
   abstract-interpretation widening on axis 2), all four axis-8
   refinements applied to source-mapping, pipeline composition,
   scope demarcation, and cross-references to every relevant
   adjacency note. Follow-up: full Agda exhibits for each example
   (tracked as `[unblocked]` example-library items below).
9. ~~**Per-decoration composition lemmas**~~ — **sweep complete**
   (2026-04-28). All five decorations landed:
   `EchoGraded.degrade-compose`, `EchoLinear.degradeMode-compose`,
   `EchoIndexed.map-role-indexed-comp`,
   `EchoChoreo.applyChoreo-{comp, compose, via-join}` along the
   choreographic-reachability order `_⊑c_`, and
   `EchoEpistemic.knowledge-monotone-{comp, id}`. Each follows the
   same recipe (decoration order → propositionality → join →
   factoring-free compose → via-join restatement). All headlines
   pinned in `Smoke.agda`.

The remaining open work in this list is **steps 1, 5, 6, 8**. Steps 1
and 5–6 are ~3–4 days of honest work that require nothing from proof
assistants, external repos, or the blocked Buchholz path. Step 5 is
the natural next coherence pass; steps 6 and 8 extend into Agda or
prose but depend only on infrastructure we already have in-suite.

Everything **[gated]** waits for its unblocker. The pack above gives
3–4 weeks of disciplined parallel work without touching the remaining
full-order Buchholz gap.

---

## What this roadmap deliberately does not include

- No week-by-week date estimates beyond the rough "days" above.
  These are order-of-magnitude guides, not commitments.
- No claim about which application area will yield the largest
  payoff — ML interpretability, compiler analysis, and database
  provenance are all plausible; that decision should come from the
  consumer, not the theory.
- No tie to any release tag. `v0.2.0` should be decided on the basis
  of actual landed content, not on this roadmap.
- No gating on `docs/buchholz-plan.adoc`'s own milestones (E4, E5,
  etc.) — those are a parallel workstream that can advance or stall
  without affecting the Echo Types theory development here.

---

## Revision policy for this document

This roadmap should be updated when:

- A **[gated]** item becomes unblocked (e.g. Agda upgrade, repo
  access granted).
- A new axis is added to `taxonomy.md`.
- An example in `examples.md` gets promoted to formalised Agda.
- The composition laws in `composition.md` get confirmed or refuted.

Keep the revision history in-file (append-only), and annotate each
update with the trigger. The roadmap is a living document; the
stable content lives in `overview.md`, `taxonomy.md`, and
`composition.md`.
