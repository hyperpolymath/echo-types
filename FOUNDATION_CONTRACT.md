<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Echo Types Foundation Contract

Echo Types exports the **residual-modality axis**. This document is the
stable contract that downstream languages (e.g. my-lang) build against.
It fixes the vocabulary, the exported interface, and — above all — the
boundary invariant that keeps Echo from being collapsed into a
resource/semiring instance.

The contract is backed by mechanised Agda. The four curated public
modules are:

| Concern | Module | File |
|---|---|---|
| Echo index (thin poset) | `Echo.Index.ThinPoset` | `proofs/agda/Echo/Index/ThinPoset.agda` |
| Echo modality (core) | `Echo.Modality.Core` (+ `Echo.Modality.Interface`) | `proofs/agda/Echo/Modality/` |
| Anti-collapse / separation | `Echo.Separation.NotResourceInstance` | `proofs/agda/Echo/Separation/NotResourceInstance.agda` |
| Residue-measure seam | `Echo.Measure.Interface` (+ `Echo.Measure.Examples`) | `proofs/agda/Echo/Measure/` |

All build under `--safe --without-K`, with zero postulates.

## Echo index

The modality is indexed by a **thin poset/order of degradation or
retention**. The canonical instance is the three-point loss order

```
keep ≤ residue ≤ forget
```

exported as `grade-thinPoset : ThinPoset 0ℓ 0ℓ`. The abstract interface
`ThinPoset` carries exactly: a carrier/index type `Ix`, an order `_≤_`,
reflexivity `≤-refl`, transitivity `≤-trans`, and **thinness**
`≤-thin` — propositionality of order proofs (any two proofs of `i ≤ j`
are equal). Thinness is load-bearing, not cosmetic: it is the single
hypothesis that makes degradation path-independent (see *Anti-collapse*
below).

## Echo core

Echo core proves degradation, composition, no-section/irreversibility,
and residue/fibre behaviour:

- the fibre functor `Echo f y := Σ (x : A) , (f x ≡ y)` — the
  structured remainder of an information-losing `f`;
- the index-graded modality with `degrade`, the unit law `degrade-id`,
  and the path-independence law `degrade-compose`;
- the generic no-section theorem `no-section-of-collapsing-map` (Echo's
  irreversibility is a property of non-injectivity);
- an abstract `EchoModality` record that downstream instantiates at its
  own fibration, with the canonical `grade-echoModality` witness.

**Echo core is measure-independent.** The modules
`Echo.Modality.Core`, `Echo.Modality.Interface`, and
`Echo.Index.ThinPoset` import **no** semiring / resource-algebra
machinery; their entire cone is `Echo`, `EchoGraded`,
`EchoNoSectionGeneric` and agda-stdlib. The proof-relevant content of
`degrade` is carried by the thin order of the index, not by any
semiring-valued grade.

**Echo core is not a semiring/resource algebra instance.** See the
boundary invariant.

## Residue measure

A resource algebra may be consumed as an **external measure** on Echo
residues. The seam is `Echo.Measure.Interface`:

```
record ResidueMeasure (E : EchoModality P ℓc) (R : OrderedCarrier ℓm ℓo) where
  field
    measure  : ∀ {i} → ⟦ i ⟧ → Carrier R
    monotone : ∀ {i j} (p : i ≤ j) (x : ⟦ i ⟧) →
               measure x ≤R measure (degrade p x)
```

The target is a minimal local `OrderedCarrier` (carrier, reflexive-
transitive order). Concrete semiring-valued measures — a cost measure, a
tropical-cost measure (valued in the order-reduct of the min-plus
semiring), and a probability/confidence measure (valued in the opposite
order) — are downstream refinements that supply an `OrderedCarrier` view
of their carrier; three are mechanised in `Echo.Measure.Examples`. The
seam is order-only, so these examples exercise the order, not the
semiring's `min`/`+` operations.

Such a measure is an **observation/decorating seam, not the definition
of Echo**. `Echo.Measure.*` may depend on order/resource interfaces;
`Echo.Modality.Core` must not. This direction of dependency is the
contract.

## Boundary invariant

> **Echo IS-NOT a resource instance.**
>
> **Equal residue measure does not imply equal Echo.**
>
> Do not model Echo as a `Soundness(S)` resource-algebra instance in
> downstream languages.

This is mechanised in `Echo.Separation.NotResourceInstance` along two
complementary lines (neither claims the impossible universal "no
semiring can ever encode any echo-like quotient"; both claim the useful
project invariant that the proof-relevant Echo structure is not
determined by a semiring-valued grade/measure):

1. **Structural** — `echo-degrade-not-generic-sigma`
   (= `EchoSeparating.sep-degrade-compose-fails`). The characteristic
   law `degrade-compose` is carried *precisely* by thinness of the echo
   index. The separating model keeps the generic Σ-functoriality laws
   but drops thinness, and composition then breaks at a checked
   `true ≢ false`. The graded Echo structure is genuine structure on an
   axis no semiring grade supplies.

2. **Measure** — `equal-measure-does-not-imply-equal-echo` and
   `measure-not-injective`. A residue measure (the trivial-residue
   projection) sends two genuinely-distinct Echo residues (`echo-true`,
   `echo-false`) to the *same* value, while the modality keeps them
   apart. And the sharper witness
   `equal-informative-measure-does-not-imply-equal-echo` makes the same
   point against a measure that is *not* a strawman: `visible-measure`
   genuinely reads the residue and lands in a two-point carrier
   (`visible-measure-informative` shows it discriminates elsewhere), yet
   still cannot separate two residues that agree on the visible bit.
   Equal residue measure therefore does not imply equal Echo: any such
   measure is a lossy observation, never the identity criterion of Echo.

## Vocabulary

Use these terms precisely; they name three orthogonal things.

- **resource grade** — a binder/resource quantity, belonging to the
  resource algebra / semiring axis.
- **echo index** — the thin-poset index of the Echo modality, e.g.
  `keep ≤ residue ≤ forget`. Inhabitants of `Ix`.
- **residue measure** — a semiring/resource-algebra-valued *observation*
  of an Echo residue (a `ResidueMeasure`).

Avoid **"echo-grade"**: it ambiguously fuses the orthogonal *echo index*
(retention axis of the modality) and *resource grade* (semiring axis),
which is exactly the collapse this contract forbids. If you must explain
the term, explain it as that ambiguity.
