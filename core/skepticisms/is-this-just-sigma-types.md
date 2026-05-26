# Is this just Sigma Types?

## The Skeptical Position
Yes, at the lowest level of Agda code, this is `Σ (x : A) , (f x ≡ y)`.
It relies entirely on the standard dependent pair type and propositional
equality.

## The Burden of Proof
Any claim of utility must show why working with the `Echo` wrapper is
better than directly pattern-matching on the Sigma type. If every proof
immediately unpacks the `Echo` and does standard Sigma-type manipulation,
the abstraction is leaky and pointless.

## Collapse Conditions
If the `Echo` interface requires the user to manually manage the
underlying `Σ` structure to accomplish basic composition or mapping
tasks, the abstraction fails.

## Reinterpretation vs. Novelty
The novelty must reside in the API and the categorical/compositional
properties exposed by the wrapper, demonstrating that `Echo` behaves
coherently under lossy operations in a way that bare Sigma types do not
automatically communicate.

---

## Answer: the in-tree evidence

This section is the index reviewers can walk to confirm Echo is not
"renamed Σ". It is organised under five demands a sceptic typically
makes. Each item points at a machine-checked Agda artefact (pinned in
`proofs/agda/Smoke.agda`), a doc, or both. Statements stay inside the
*narrowed* claims of `docs/retractions.adoc` R-2026-05-18 — no "full
universal property", no "graded comonad", no "model-independence".

### 1. Irreversibility is a theorem family, not a property

A raw `Σ (x : A) (f x ≡ y)` gives `proj₁` trivially; the user can
always extract the original `x`. The Echo programme proves that *no*
section exists once specific lossy interfaces are applied. The witness
is a *family* across five separate decoration layers:

- `EchoCharacteristic.no-section-collapse` — no section of the
  `Bool → ⊤` collapse map.
- `EchoCharacteristic.no-section-visible` — no section recovering the
  pre-image from a visible output alone.
- `EchoResidue.no-section-collapse-to-residue` — weakening to a residue
  is provably one-way.
- `EchoLinear.no-section-weaken` — the `linear → affine` mode shift is
  one-way (defined as the residue lemma).
- `EchoOrdinal.no-section-ordinal-collapse` — ordinal collapse case.
- `EchoEpistemicResidue.no-section-to-epistemic` — epistemic-residue
  case.

All six are pinned in `Smoke.agda`. The family is what carries the
weight: each decoration *separately* refuses the section that a raw Σ
would admit. See also `docs/theorem-index.md` and the prose write-up at
`docs/characteristic.adoc`.

### 2. Loss is graded, and downgrades cannot be reversed

A raw Σ has no built-in notion of "degrading from strict to loose".
Echo equips the fibre with a lattice of grades and a monotone reindexing
along it. The two halves of the asymmetry are:

- *Down-step is admissible.* `EchoGraded.degrade-compose` and
  `EchoGraded.degrade-via-join` — the per-decoration composition law
  for the loss-grade order. Same recipe lands at:
  - `EchoLinear.degradeMode-compose` (linearity-mode order),
  - `EchoChoreo.applyChoreo-compose` (role/reachability order),
  - `EchoAccess` (graded access modality),
  - `EchoCost` (cost-indexed refinement),
  - `EchoSearch` (witness-search refinement).
- *Up-step is not.* `no-section-weaken` (item 1) is the same
  statement on the other diagonal — once degraded, no inverse exists.

Honest framing: this is a *thin-poset reindexing modality*, not a
graded comonad. The retraction at `docs/retractions.adoc#R-2026-05-18`
narrowed an earlier "graded comonad" claim. The reindexing modality is
the load-bearing structure and is the right answer to "is Σ enough?":
Σ alone gives neither the monotone reindex nor the no-section dual.

### 3. Echo is the homotopy fibre; bridges from other "loss-tracker" frameworks exist

The categorical/identity claim is **deflationary** and owned in
`docs/echo-types/establishment-plan.adoc`: `Echo f y` is *definitionally*
the homotopy fibre `fib f y` (HoTT book Def. 4.2.4). The bridge is
`EchoFiberBridge.echo↔fib`, both round-trips `refl` (Pillar A; pinned
in `Smoke.agda`).

For the "is this just a pullback" question, `EchoPullback.echo-pullback-univ`
exhibits `Echo f y` as the pullback of `f` along `y : ⊤ → B` with a
*pointwise, funext-relative* mediator property. The retraction note in
that module is loud: this is **not** a full categorical universal
property in the absence of funext. Bridges from named neighbour
frameworks land as separate modules:

- `EchoFiberBridge.agda` — homotopy fibre identity.
- `EchoJanusBridge.agda` — Janus-style reversible debugger bridge.
- `EchoTropical.agda` / `AntiEchoTropical.agda` — tropical
  semiring / argmin decomposition.
- `EchoCNOBridge.agda` — categorical neighbour bridge.
- `EchoFiberCount.agda` + `EchoThermodynamics*.agda` — finite-fibre
  Landauer / Bennett correspondence.

These are independent witnesses, not one universal theorem. The honest
verdict is "Echo is *a* canonical target with concrete bridges in"
rather than "Echo is *the* terminal residue tracker by unique mediator".

### 4. The abstraction barrier (consumer-side)

A raw `Σ A (λ x → f x ≡ y)` exposes `proj₁`, so a consumer can always
distinguish two preimages of the same output. The Echo interface at the
affine mode does not export that projection: the residue carrier is
contractible (`EchoLinear.affine-canonical`, `affine-all-equal`), so
any consumer assigns the same value to the weakened images of two
known-distinct linear echoes.

**Status:** the consumer-side abstraction-barrier theorem is the one
genuine gap relative to the five demands. It is planned as
`proofs/agda/EchoAbstractionBarrier.agda` (Track B in the work plan).
The model-side counterpart — *carrier-parametricity* over a fixed
grade poset — already lands as `EchoRelModel` (Pillar D, narrowed per
R-2026-05-18 from the original "model-independence" wording).

### 5. Canonical examples — what Σ would let through

The example modules exhibit echo as the explanatory unit on real
artefacts:

- `EchoExampleParser` — `(())` vs `()()` are two distinct echoes at the
  same `parses ≡ true`.
- `EchoExampleProvenance` — distinct Bool-provenance rows collapse to
  the same payload; the echo carries the lost annotation.
- `EchoExampleAbsInt` — `{p1, p2}` collapse to `pos` under sign
  analysis; the echo retains which.
- `EchoExampleSignAnalysis`, `EchoExampleTruncation` — further
  collapse-with-residue exhibits.
- `EchoFiberCount` + `EchoThermodynamics*` — finite-fibre Landauer
  bound for the erasure cost.
- `EchoEpistemicResidue` — observation-discipline residue.

Each is positive evidence. The matched *negative* — a small raw-Σ
counter-program that would let the bug through — is planned as
`proofs/agda/examples/EchoVsSigma.agda` (Track C). Until that lands,
the "raw Σ would leak" claim is prose, not a checked artefact.

---

## Cross-references

- Gate 2 audit (closest reviewer touchpoint):
  `docs/characteristic.adoc`.
- Theorem-by-theorem ledger: `docs/theorem-index.md`.
- Adjacency notes (per neighbour framework): `docs/adjacency/`.
- Honest scope of the establishment claim:
  `docs/echo-types/establishment-plan.adoc` and
  `docs/echo-types/paper.adoc` §"Reframing note".
- AsciiDoc reviewer companion to this file:
  `docs/echo-types/sigma-distinctness-map.adoc`.
- Companion skepticisms: `is-this-just-fibers.md`, `what-is-actually-new.md`,
  `failure-conditions.md`.
