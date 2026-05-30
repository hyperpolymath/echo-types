# Proof debt

Per the estate Trusted-Base Reduction Policy
(hyperpolymath/standards `docs/TRUSTED-BASE-REDUCTION-POLICY.adoc`), every
soundness-relevant escape hatch in this repository is enumerated below
under one of (a) discharged / (b) budgeted / (c) necessary axiom / (d) debt.

## (a) Discharged in this repo

- (none — entries are removed here when proofs land)

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

## (d) DEBT — actively to be closed

- (none — the kernel is `--safe --without-K` clean; all
  `…Postulated` modules are intentionally scoped to (c).)

## Notes

The `EchoDecorationBridge.agda` module is tagged exploratory in the
guardrail but contains no escape hatches; it is excluded from the
guardrail's "no postulates" rule for naming convenience (the
`-Postulated` suffix would be misleading there). The trusted-base
script does not flag this module because it scans for actual
`^[[:space:]]*postulate` lines.
