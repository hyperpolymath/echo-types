# Echo Types — Roadmap

**Status:** planning document. Partitions work by dependency on the
two identified bottlenecks:

- **Bottleneck B1.** The `--without-K` shared-binder constructor
  block in the Buchholz `_<ᵇ_` order. `wf-<ᵇ` is landed for the
  currently admitted core, but full totality + full-constructor
  well-foundedness remain gated on a K-free treatment of the shared-
  binder cases.
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

- **[unblocked]** `Echo-comp-iso` in `Echo.agda`: the accumulation
  isomorphism `Echo(g ∘ f) y ≃ Σ B (λ b → Echo(f) b × (g b ≡ y))`.
  Sonnet-class proof; see composition.md §1.
- **[unblocked]** `Echo-comp-cancellation`: corollary for sectioned
  `g`. Follows from the iso plus an existing section-lemma pattern
  (`no-section-weaken` in `EchoLinear`).
- **[unblocked]** Pentagon coherence for three-fold composition.
  Routine.
- **[unblocked]** `EchoApprox.agda`: new module for ε-indexed echoes
  over a metric codomain. First-class taxonomy axis 2 artifact.
- **[unblocked]** Per-decoration composition lemmas in `EchoGraded`,
  `EchoLinear`, `EchoIndexed`, `EchoChoreo`, `EchoEpistemic`: check
  each commutes with basic composition.
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

- **[gated on B1]** Full `_<ᵇ_` totality on Buchholz terms.
  Requires the shared-binder constructors, which the current Agda
  2.6.3 `--without-K` blocks via pattern-matching. Either an Agda
  upgrade or a rank-embedding proof strategy unblocks this.
- **[gated on B1]** Extension of totality + well-foundedness proofs to
  the full constructor set (including shared-binder cases such as
  `<ᵇ-ψα` and `<ᵇ-+2`).
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
2. **Agda: `Echo-comp-iso` + cancellation** — 1 day.
   Concrete, compiling, unblocks the composition roadmap.
3. **Gate 1 adjacency refresh against the new taxonomy** — 1 day.
   Cheap coherence pass on existing docs.
4. **Theory: pick one axis-8 refinement and formalise it** — 1–2
   days. Four candidates in `taxonomy.md` §8 (cost-indexed echo,
   graded access modality, decidability-respecting echo, witness-
   search abstract machine). Choosing commits the repo to one
   formal handle on computational vs information-theoretic access.
5. **Agda: `EchoApprox.agda`** — 2–3 days. First artifact of axis 2.
6. **Applications chapter: compiler-analysis residue** — 2 days.
   Largest reader value; entirely unblocked.
7. **Per-decoration composition lemmas** — 1 day each. Useful
   coverage.

Steps 1–4 are ~5–6 days of honest work that require nothing from
proof assistants, external repos, or the blocked Buchholz path.
Steps 5–7 extend into Agda but depend only on infrastructure we
already have in-suite.

Everything **[gated]** waits for its unblocker. The pack above gives
3–4 weeks of disciplined parallel work without touching blocked
paths.

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
