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

- `proofs/agda/Ordinal/Buchholz/Fidelity.agda` — three top-level
  `postulate`s forming the trust boundary of the **order-type fidelity
  scaffold** (open problem `D-2026-06-14`,
  `docs/echo-types/decisions/ordinal-bh-order-type-fidelity-open.adoc`):
  - `bh-notation` — assumed checked Bachmann–Howard order structure.
  - `denotation` — assumed faithful, height-preserving order-embedding
    `⟦·⟧ : BT → 𝒪` (the missing object; **not** `rank2`, which
    deliberately collapses heights and is a termination measure only).
  - `ordinal-upper-bound` — the `⟦·⟧`-level upper half of the sandwich
    (downstream of `denotation`).
  - **Classification**: DEBT, to be discharged when order-type fidelity
    is proved — these are *not* permanently-accepted axioms. Each is
    annotated inline with an `AXIOM:` leading comment.
  - **Justification / scope**: the module is quarantined — `--without-K`
    only, NOT imported by `All.agda` / `Smoke.agda` — so the `--safe`
    kernel cone depends on none of these. Nothing in the module asserts
    that order type ψ₀(Ω_ω) is *proven*; the status surfaces (appendix,
    decision log, roadmap) read "written at WF milestone; order-type
    fidelity OPEN".
  - **Citation**: `D-2026-06-14`; full per-postulate spec (statement /
    what closes it / owner) in `Fidelity-OPEN-postulates.md`.
  - **Guardrail status**: allow-listed in `tools/check-guardrails.sh`
    (`EXPLORATORY_EXEMPT`) and the inline `hypatia: allow` pragma at the
    module head.

## Notes

The `EchoDecorationBridge.agda` module is tagged exploratory in the
guardrail but contains no escape hatches; it is excluded from the
guardrail's "no postulates" rule for naming convenience (the
`-Postulated` suffix would be misleading there). The trusted-base
script does not flag this module because it scans for actual
`^[[:space:]]*postulate` lines.
