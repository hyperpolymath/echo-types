# Echo Types — Roadmap

**Status:** planning document. Partitions work by dependency on the
two identified bottlenecks:

For current cross-repo progress snapshots, see
`cross-repo-bridge-status.md`.

- **Bottleneck B1.** The remaining gap between the closed
  Veblen/current-core route and the full intended Buchholz order:
  the historically blocked shared-binder shapes in `_<ᵇ_`.
  `wf-<ᵇ` is landed for the currently admitted core, but promoting
  those shapes back into the real order package still needs a
  K-free mediated internalization. Finite same-binder depth is now
  handled by iterated mediated wrappers, but that does not yet close
  the real order package itself.
- **Bottleneck B2.** Tool-scope limitations on adjacent repos
  (`maa-framework/absolute-zero`, `januskey`,
  `tropical-resource-typing`). Blocks end-to-end bridge audits.

Paths marked **[unblocked]** can proceed today. Paths marked
**[gated on B1]** or **[gated on B2]** cannot.

---

## Theory work — no proof assistant needed

- **[unblocked]** Axis 2 (approximate echoes): settle the formal
  definition before touching Agda. Draft in `taxonomy.md` and
  `composition.md`.
- **[landed]** Axis 8 (information-theoretic vs computational
  access): promoted from the candidates list to a numbered axis;
  four candidate refinements of `Echo` (cost-indexed, graded access
  modality, decidability-respecting, witness-search abstract
  machine) are listed. Follow-up: pick one refinement and formalise.
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
- **[partial]** `cancel-iso-to` / `cancel-iso-from` in `Echo.agda`:
  forward and backward maps for the cancellation corollary, each
  needing only the relevant half of g's iso structure. Round-trips
  are **deferred** pending a triangle-identity coherence or a stdlib
  `Function.Bundles.Inverse` shim. See `composition.md` §3.
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
- **[partial]** Budgeted recursive-surface WF on the ordinal track.
  `Ordinal/Buchholz/RecursiveSurfaceBudget.agda` ships
  `BudgetedBT = ℕ × BT`, the budgeted relation `_<ᵇʳᶠᵇ_` with its
  `spend` constructor, `wf-<ᵇʳᶠᵇ : WellFounded _<ᵇʳᶠᵇ_` (via
  subrelation on ℕ), and `<ᵇʳᶠᵇ⇒lifted` transporting each budgeted
  step into the iterated-wrapper tower (`IteratedExtendedOrder`).
  The unbudgeted global theorem — eliminate the explicit ℕ budget
  from `wf-<ᵇʳᶠᵇ` to get `WellFounded _<ᵇʳᶠ_` — is the next
  concrete ordinal-track milestone. Pushing that result back into
  `Ordinal/Buchholz/Order.agda`'s main `_<ᵇ_` package is the step
  after that.
- **[landed]** `EchoApprox.agda`: new module for ε-indexed echoes
  over a metric codomain. First-class taxonomy axis 2 artifact.
  Ships `EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)` parametric over
  a `Tolerance` monoid and a `PseudoMetric`, with three headline
  lemmas: `echo-approx-intro` (exact ⇒ zero-ε), `echo-approx-relax`
  (monotone in ε), and `echo-approx-compose` (additive composition
  under a non-expansive outer leg, realising the taxonomy §2
  conjecture). Wired into `All.agda` and `Smoke.agda`.
- **[partial]** Per-decoration composition lemmas in `EchoGraded`,
  `EchoLinear`, `EchoIndexed`, `EchoChoreo`, `EchoEpistemic`: check
  each commutes with basic composition. Grade case **landed** in
  `EchoGraded.agda` as `degrade-compose` (any factoring of a
  `g1 ≤g g3` transition through an intermediate `g2` collapses to
  the same degraded echo) plus `degrade-via-join` (same statement
  through the join `_⊔g_`), proved from `≤g-prop` (the order is
  propositional) and `degrade-comp`. Supporting lemmas
  `≤g-⊔g-left`, `≤g-⊔g-right`, `≤g-⊔g-univ` exhibit `_⊔g_` as the
  categorical join. Linear case **landed** in `EchoLinear.agda` as
  `_≤m_`, `≤m-trans`, `degradeMode`, and `degradeMode-comp`
  (`linear ⊑ linear ⊑ affine ⊑ affine`; `degradeMode-comp` is the
  per-decoration composition lemma; auxiliary corollaries
  `degradeMode-id-linear`, `degradeMode-id-affine`,
  `degradeMode-strict-is-weaken` make the relationship to the
  existing `weaken` definitional). Indexed / role / modal cases
  remain unblocked.
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

- **[gated on B1]** Internalize the missing shared-binder shapes as
  actual constructors/comparison principles of the real Buchholz
  order. The current route closes well-foundedness for the admitted
  core and handles arbitrary finite same-binder depth via iterated
  wrappers, but not yet for the full intended constructor package.
- **[gated on B1]** Re-close totality/inversion/transitivity and
  well-foundedness for the enlarged order after that internalization,
  including shared-binder cases such as `<ᵇ-ψα` and `<ᵇ-+2`.
- **[gated on B1]** Ordinal semantics of BT terms: denotation
  `BT → Ordinal` preserving order. Requires a formal `Ordinal` type
  as a prerequisite, which is itself downstream of WF.
- **[gated on B1]** Landauer / Shannon rigorous bridge (separate
  handoff pack in `docs/echo-types/roadmap.md` would cross-reference
  this). The current `EchoThermodynamics.agda` is a stub; genuine
  content requires a preimage-count that itself needs ordinal / finite
  type infrastructure.
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

1. **Theory: axis 2 formal definition** — 1–2 days.
   Unblocks `EchoApprox.agda`, which is required for examples 6 and 10.
2. ~~**Agda: `Echo-comp-iso` + cancellation**~~ — landed. Accumulation
   iso plus both cancellation maps now live in `Echo.agda`; the full
   cancellation iso (with round-trips) is the first deferred item —
   needs a triangle-identity coherence (see composition.md §3).
3. ~~**Agda: pentagon coherence for `Echo-comp-iso`**~~ — projection
   pentagon landed as `Echo-comp-iso-pent-{B, echo}`. Full
   Σ-associativity iso between the two nested Σ-shapes is one of
   two next composition-track follow-ups (the other is
   full-cancel-iso round-trips, which needs a triangle identity).
4. **Agda: unbudgeted `_<ᵇʳᶠ_` WF on the ordinal track** — eliminate
   the explicit ℕ budget from `wf-<ᵇʳᶠᵇ` in
   `RecursiveSurfaceBudget.agda`. Sharpest next ordinal-track move
   since the budgeted version already ships. Keep `--safe --without-K`.
   Pushing the result back into `Order.agda`'s `_<ᵇ_` is the step
   after.
5. **Gate 1 adjacency refresh against the new taxonomy** — 1 day.
   Cheap coherence pass on existing docs.
6. **Theory: pick one axis-8 refinement and formalise it** — 1–2
   days. Four candidates in `taxonomy.md` §8 (cost-indexed echo,
   graded access modality, decidability-respecting echo, witness-
   search abstract machine). Choosing commits the repo to one
   formal handle on computational vs information-theoretic access.
7. **Agda: `EchoApprox.agda`** — 2–3 days. First artifact of axis 2.
8. **Applications chapter: compiler-analysis residue** — 2 days.
   Largest reader value; entirely unblocked.
9. **Per-decoration composition lemmas** — 1 day each. Useful
   coverage. *Grade case landed* (`EchoGraded.degrade-compose`,
   `degrade-via-join`); linear / indexed / role / modal still open.

Steps 1 and 5–6 are ~5–6 days of honest work that require nothing
from proof assistants, external repos, or the blocked Buchholz path.
Steps 5–7 extend into Agda but depend only on infrastructure we
already have in-suite.

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
