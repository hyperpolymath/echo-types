# Buchholz `_<ᵇ⁺_`: well-foundedness gap

`Ordinal.Buchholz.OrderExtended._<ᵇ⁺_` adds two shared-binder lex
constructors on top of `Ordinal.Buchholz.Order._<ᵇ_`:

* **`<ᵇ⁺-ψα`** — `bpsi ν α <ᵇ⁺ bpsi ν β` whenever `α <ᵇ β`
  (lex on the ψ-argument at a fixed Ω-index).
* **`<ᵇ⁺-+2`** — `bplus x y₁ <ᵇ⁺ bplus x y₂` whenever `y₁ <ᵇ y₂`
  (lex on the right summand at a fixed left summand).

`<ᵇ⁺-irrefl` and `<ᵇ⁺-trans` are proved. **Well-foundedness for
`_<ᵇ⁺_` is open.** This note records why and sketches the two
viable design routes.

## Why `wf-<ᵇ` does not extend directly

`Ordinal.Buchholz.WellFounded.wf-<ᵇ` is built from a per-Ω-index
bundle:

```agda
ΩBundle μ = Acc _<ᵇ_ (bOmega μ) × ((α : BT) → Acc _<ᵇ_ (bpsi μ α))

<ᵇ-bundle-fromΩ : ∀ {μ} → Acc _<Ω_ μ → ΩBundle μ
```

The bundle's `psiAcc α` returns `Acc _<ᵇ_ (bpsi μ α)` for any `α`,
discharging predecessors via case analysis on `_<ᵇ_`'s
constructors. The new `<ᵇ⁺-ψα` constructor introduces predecessors
shaped `bpsi μ β` for arbitrary `β <ᵇ α`. Discharging those needs
recursion on `Acc _<ᵇ_ α` — but `psiAcc` does not carry an `Acc α`
argument, so the natural attempt

```agda
predPsi α (<ᵇ-ψα {α = β} refl _) = psiAcc β
```

calls `psiAcc β` with `β` strictly smaller than `α` only via
`<ᵇ`, not structurally. Agda's termination checker rejects the
mutual cycle `predPsi → psiAcc → predPsi` because the first
argument does not decrease.

Symmetrically, `<ᵇ⁺-+2` introduces predecessors `bplus α y₁` for
arbitrary `y₁ <ᵇ y₂`, and the existing `<ᵇ-acc-bplus-from` only
threads `Acc _<ᵇ_ α` (the left summand), so the right-summand lex
case has no decreasing measure either.

## Two design routes

### Route A — single-mutual block with widened bundle

Replace the per-Ω-index bundle with a single mutual block in
which:

```agda
ΩBundle μ = Acc _<ᵇ_ (bOmega μ)
          × ((α : BT) → Acc _<ᵇ_ α → Acc _<ᵇ_ (bpsi μ α))

<ᵇ-acc-bplus-from-both :
  ∀ {α β} → Acc _<ᵇ_ α → Acc _<ᵇ_ β → Acc _<ᵇ_ (bplus α β)
```

i.e. the ψ-side of the bundle takes `Acc _<ᵇ_ α` as a parameter,
and `bplus`-acc takes `Acc _<ᵇ_` for **both** summands. `wf-<ᵇ`
becomes mutual with the bundle and supplies the extra `Acc` args
via BT structural recursion (`wf-<ᵇ α` for the smaller subterm).

**Status of attempt.** Drafted twice (in this PR and again by a
parallel session on 2026-04-28); both attempts are
constructionally identical and both are rejected by Agda's
termination checker. The reported cycle is
`pred-bpsi-from → wf-<ᵇ → <ᵇ-acc-bpsi → <ᵇ-acc-bpsi-from`. The
cycle is well-founded in lex order on
`(BT-structure of carrier, witness)`, but Agda does not see the
witness as decreasing the BT carrier without an explicit
size-measure annotation. A sized-types or explicit measure
encoding (e.g. via `Induction.WellFounded.<-rec` with a measure
into ℕ × ℕ) is the next thing to try; failing that, fall back
to Route B.

### Route B — rank-embedding into Brouwer ordinals

Define `rank : BT → Ord` (Brouwer, already present in
`Ordinal.Brouwer`) such that `x <ᵇ⁺ y → rank x < rank y`. Then
WF for `_<ᵇ⁺_` follows from `Ordinal.Brouwer.wf-<` by
transport along `rank`.

Sketch of `rank`:

```agda
rank bzero        = oz
rank (bOmega μ)   = ω-rank μ
rank (bplus α β)  = rank α ⊕ rank β
rank (bpsi μ α)   = psi-rank μ ⊕ rank α   -- conjectural form
```

The arithmetic infrastructure (`_⊕_`, `nat-to-ord`, `ω-rank`,
`psi-rank`) is in `Ordinal.Brouwer.Arithmetic`. The strict
decrease must hold on every `<ᵇ⁺` constructor:

* `<ᵇ-ψΩ μ<ν` — Ω-index decrease must dominate the ψ-arg
  comparison; needs `psi-rank` to be strictly monotone in μ at a
  rate that swamps `_⊕_`-additions of the ψ-arg.
* `<ᵇ⁺-ψα` — ψ-arg strict decrease at fixed μ; needs
  `psi-rank μ ⊕ ·` to preserve `<` on the right.
* `<ᵇ⁺-+2` — right-summand strict decrease at fixed left;
  needs `· ⊕ rank α` to be `<`-monotone on the left.

**Status.** Not attempted yet. The constructive Brouwer-ordinal
arithmetic in this repo is light (Phase 1.1/1.2); some of the
strict-monotonicity lemmas the `rank` proof would need are not
yet present.

## Pragmatic interim — leave `_<ᵇ_` and `_<ᵇ⁺_` separate

Today's commit ships the constructors in `_<ᵇ⁺_` only, leaving
`Ordinal.Buchholz.Order._<ᵇ_` (and its `wf-<ᵇ`) intact. Downstream
consumers that need only the K-free core (e.g. the
`VeblenComparisonModel` chain) keep their existing WF guarantee.
Consumers that need the lex cases use `_<ᵇ⁺_` and accept that
WF is not yet established for it.

## Recommended next attempt

Route B (rank-embedding) is lower-risk: the arithmetic lemmas
needed are bounded and discoverable, and `Ordinal.Brouwer.wf-<`
is already proved. Route A's failure mode is Agda's termination
checker, which is harder to debug than provable mathematics.

## See also

* `proofs/agda/Ordinal/Buchholz/Order.agda` — the K-free core.
* `proofs/agda/Ordinal/Buchholz/OrderExtended.agda` — the
  extended relation defined in this PR.
* `proofs/agda/Ordinal/Buchholz/WellFounded.agda` — the bundle
  proof for `_<ᵇ_`.
* `proofs/agda/Ordinal/Brouwer.agda`,
  `proofs/agda/Ordinal/Brouwer/Arithmetic.agda` — the rank
  target if Route B is taken.
* `docs/buchholz-plan.adoc` — the broader Buchholz workstream.
