<!-- SPDX-License-Identifier: MPL-2.0 OR CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Proof debt

Per the estate Trusted-Base Reduction Policy
(hyperpolymath/standards `docs/TRUSTED-BASE-REDUCTION-POLICY.adoc`), every
soundness-relevant escape hatch in this repository is enumerated below
under one of (a) discharged / (b) budgeted / (c) necessary axiom / (d) debt.

## (a) Discharged in this repo

- **Propositional truncation `∥_∥` + the (epi, mono) image
  factorisation** — discharged 2026-06-15 in the `--cubical --safe`
  lane by `proofs/agda/EchoImageFactorizationPropCubical.agda` (zero
  postulates). The module CONSTRUCTS `∥_∥` as a higher inductive type
  and realises the four `TruncInterface` obligations as theorems
  (`is-prop-∥∥` from the `squash` higher constructor transported to
  the inductive `_≡_`; `rec-∥∥` via the path recursor, its boundary
  closing by the cubical endpoint rule), then re-proves
  `prop-factor-right-injective` (mono) and
  `prop-factor-left-mere-surjective` (epi). This realises the axiom
  the `--without-K` demo under (c) only assumes — see (c).

- **Bachmann–Howard target structure (`BHNotation` + its
  well-foundedness)** — discharged 2026-06-15 in the `--safe --without-K`
  kernel by `proofs/agda/Ordinal/Buchholz/BHTarget.agda` (zero
  postulates; wired into `All.agda`, pinned in
  `Ordinal/Buchholz/Smoke.agda`). The abstract `BHNotation` interface and
  a concrete `bh-notation-from : Ord → BHNotation` are CONSTRUCTED from
  the repo's existing Brouwer order (`Ord` / `_<′_` / `wf-<′`), so the
  fidelity target's order AND its well-foundedness are now proved, not
  assumed. This reduces the order-type fidelity trust boundary under (d)
  from three postulates to two; the candidate BH HEIGHT (which `Ord`
  value is ψ₀(Ω_ω)) is now an explicit module parameter
  (`Fidelity.AtHeight`), not a postulate. Order-type fidelity ITSELF
  remains OPEN — see (d).

## (b) Budgeted — tested with refutation budget

- (none)

## (c) Necessary axiom

- `proofs/agda/EchoImageFactorizationPropPostulated.agda:102` — top-level
  `postulate` introducing four propositional-truncation primitives
  (`Trunc-pos`, `∣_∣-pos`, `is-prop-pos`, `rec-pos`)
  - **Justification**: propositional truncation `∥_∥` cannot be
    constructed in plain `--safe --without-K` Agda without HITs /
    Cubical. The four postulates encode the standard `TruncInterface ℓ`
    record (existence + propositionality + propositional-recursion +
    introduction). The construction is **exploratory** — the base
    module `EchoImageFactorizationProp.agda` remains `--safe
    --without-K` with zero postulates; `…Postulated` exists solely
    to demonstrate the interface concretely.
  - **Citation**: see `docs/echo-types/echo-kernel-note.adoc` (Tier-2
    classification — "Exploratory / postulated"); HoTT Book §3.7
    (propositional truncation); agda-stdlib does not currently expose
    this in `--safe --without-K`.
  - **Guardrail status**: explicitly allow-listed in
    `tools/check-guardrails.sh` and in the inline `hypatia: allow`
    pragma at the head of the module.
  - **Realised (2026-06-15)**: the same four obligations are
    CONSTRUCTED (zero postulates) in the `--cubical` lane by
    `EchoImageFactorizationPropCubical.agda` — see (a). The postulates
    here are therefore the `--safe --without-K`-profile shadow of a
    now-constructed object, not an irreducible axiom; they remain only
    because `∥_∥` cannot be built WITHIN `--safe --without-K` itself.

## (d) DEBT — actively to be closed

- `proofs/agda/Ordinal/Buchholz/Fidelity.agda` — **two** top-level
  `postulate`s (reduced from three on 2026-06-15; see (a)) forming the
  trust boundary of the **order-type fidelity scaffold** (open problem
  `D-2026-06-14`,
  `docs/echo-types/decisions/ordinal-bh-order-type-fidelity-open.adoc`):
  - `denotation` — assumed faithful, height-preserving order-embedding
    `⟦·⟧ : BT → 𝒪` into the (now-real) Brouwer target (the missing
    object; **not** `rank2`, which deliberately collapses heights and is
    a termination measure only).
  - `ordinal-upper-bound` — the `⟦·⟧`-level upper half of the sandwich
    (downstream of `denotation`).
  - **Discharged (2026-06-15)**: the former `bh-notation` postulate (an
    opaque whole BH structure) is gone — the `BHNotation` interface and a
    real `bh-notation-from` instance now live in the `--safe` kernel
    module `Ordinal.Buchholz.BHTarget`, so the target order and its
    well-foundedness (Brouwer `_<′_` / `wf-<′`) are proved, not assumed.
    The candidate BH height is an explicit parameter to
    `Fidelity.AtHeight`, not a postulate. See (a).
  - **Classification**: DEBT, to be discharged when order-type fidelity
    is proved — these are *not* permanently-accepted axioms. Each is
    annotated inline with an `AXIOM:` leading comment.
  - **Justification / scope**: the module is quarantined — `--without-K`
    only, NOT imported by `All.agda` / `Smoke.agda` — so the `--safe`
    kernel cone depends on neither postulate. Nothing in the module
    asserts that order type ψ₀(Ω_ω) is *proven*; the status surfaces
    (appendix, decision log, roadmap) read "written at WF milestone;
    order-type fidelity OPEN".
  - **Citation**: `D-2026-06-14`; full per-postulate spec (statement /
    what closes it / owner) in `Fidelity-OPEN-postulates.md`.
  - **PARKED (2026-06-20, `D-2026-06-20`)**: the transfinite ladder these
    postulates sit atop is now *consumer-less* — the Groove cleave (the
    only consumer of ψ₀(Ω_ω) order-type fidelity) is resolved as a finite
    exact-round-trip zipper needing well-foundedness only, and RC-11
    forbids ε₀+ in cleave ranks. The debt is therefore *parked,
    resumable*, not actively being closed. No postulate closed;
    `D-2026-06-14` stands. See
    `docs/echo-types/decisions/ordinal-fidelity-ladder-parked.adoc`.
  - **Guardrail status**: allow-listed in `tools/check-guardrails.sh`
    (`EXPLORATORY_EXEMPT`) and the inline `hypatia: allow` pragma at the
    module head. (`BHTarget` is NOT exempt — it is real kernel content
    and passes the guardrail.)

## Notes

The `EchoDecorationBridge.agda` module is tagged exploratory in the
guardrail but contains no escape hatches; it is excluded from the
guardrail's "no postulates" rule for naming convenience (the
`-Postulated` suffix would be misleading there). The trusted-base
script does not flag this module because it scans for actual
`^[[:space:]]*postulate` lines.

## Independent ground-truth audit (2026-06-16)

An out-of-band trust audit (cold rebuild + flag/guardrail probes, not
doc-trust) was run before an external project (the `ephapax` L1
re-foundation) built on this repo. **Verdict: trustworthy — build on the
WIRED layer only.** It is consistent with, and complements, the (a)–(d)
ledger above.

- **Wired vs orphaned.** Against the transitive closure of the 4 CI roots
  (`All` / `Smoke` / `characteristic/All` / `examples/All`): ~**164 files /
  ~32.5k lines WIRED** (`--safe --without-K`, exit 0, zero postulates/holes
  in the cone) vs ~**15 orphaned files** (~8%). The often-cited
  "676 files / 52k lines" headline is inflated by `.claude/worktrees/`
  duplicate snapshots; real source ≈ 190 `.agda` files / ~36k lines.
- **The quarantined postulates are correctly *outside* the wired cone.**
  The audit independently confirms the two postulate-bearing files this
  ledger already lists — `EchoImageFactorizationPropPostulated.agda` (c)
  and `Ordinal/Buchholz/Fidelity.agda` (d) — are guardrail-exempt,
  `--without-K`-only, and imported by no `All.agda`, so the `--safe`
  kernel cone depends on neither. Nothing slipped into the wired layer.
- **⚠ Variance is NOT a proven result.** The `experimental/echo-additive/`
  track (`GradedComonad` / `GradedMonad` / `GradedAdjunction` /
  `VarianceGate.agda`) is present on `main` but **orphaned** (in no
  `All.agda`, not CI-verified), and `VarianceGate.agda` self-declares
  "This file contains NO proven theorems … OBLIGATION comments" + variance
  **RETRACTED R-2026-05-18**. It typechecks `--safe` only because the
  obligations are comments. **Do not cite the monad / comonad / adjunction
  variance question as settled** — it remains genuinely open. Build instead
  on the wired `Echo` / `EchoResidue`, `EchoGradedComonad` (coassoc/counit),
  the composition isos, and `DyadicEchoBridge`.
- **Env gotcha (fix before handoff).** A *dangling* libraries config
  (nix-store name mismatch + a non-existent `…/absolute-zero` path) causes
  **false "library name not found" failures** under the default config.
  Correct invocation points `--library-file` at the v2.3 stdlib worktree
  (`/home/hyperpolymath/developer/worktrees/agda-stdlib-tweak`). A config
  artefact, NOT a proof defect.
