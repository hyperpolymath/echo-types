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

*Plan for the next Claude.*  Continue option (A) per
`RankPow.agda`'s preamble, in priority order:

1. *Option (b) head-Ω inversion lemma* — `bOmega ν <ᵇ x → ν <Ω
   head-Ω x` and the ψ-analogue `bpsi ν α <ᵇ x → ν ≤Ω head-Ω x`.
   Independent of Slice 2-omega's ω-branch question; smallest useful
   next step.  Lands in a new module under `Ordinal/Buchholz/` (e.g.
   `HeadOmegaInversion.agda`) so the existing `HeadOmega.agda` stays
   pure definitions + sanity lemmas.
2. *Slice 2-omega* — replace the ω branch of `ω-rank-pow-succ` with
   the documented `ω^(ω+1)` candidate after running the three
   cross-checks listed in `RankPow.agda`'s Slice 2-omega comment.
   Brouwer ordinal arithmetic; non-trivial.
3. *Slice 2-bplus* — prove the full domination lemma.  Composes
   (1) + (2).

DO NOT reopen: the closed 11/13 Buchholz constructors; the
W1/W2/W3 walkthroughs; the R-2026-05-18 narrowings; the closed
fin-branch dominance just landed.

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
