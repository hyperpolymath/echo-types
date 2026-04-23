# Echo Types — Overview

**Status:** working note. Paths marked *definition* are stable within
this document; paths marked *conjecture* are speculative and will
stay speculative until formal evidence is produced.

---

## Working definition

*Definition (informal).* Echo Types is a theory of the structured
remainder left by information-losing computation. For a map
`f : A → B`, the *echo of `f` at `y : B`* is whatever evidence,
structure, or witness survives the act of applying `f` and looking
at the result `y` — but survives in a form that is explicit,
compositional, and (ideally) formally tractable.

*Definition (current Agda).* The spine of the current formalization
is the fiber-shaped type

```
Echo : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → B → Set (a ⊔ b)
Echo {A = A} f y = Σ A (λ x → f x ≡ y)
```

introduced in `proofs/agda/Echo.agda`. An inhabitant of `Echo f y` is
a pair `(x , p)` where `x : A` and `p : f x ≡ y`. The echo is thus a
proof-relevant witness that `y` was produced by applying `f` to some
specific `x`, with `p` recording exactly which one.

## Core intuition

When a map forgets, merges, erases, compresses, or abstracts
information, the output does not by itself determine its source. But
it may still determine a *typed remainder*:

- **admissible antecedents** — the set of `x` with `f x = y`,
- **retained constraints** — properties of `x` that must hold for any
  antecedent,
- **provenance** — a witnessed history of how `y` was produced,
- **reconstruction bounds** — information about `x` that can be
  recovered up to some equivalence,
- **proof-relevant witness structure** — the specific derivation
  `(x , p)` rather than the mere fact that some `x` exists.

Echo Types names the remainder side explicitly. In the current
formalization this is the dependent sum above; later stages may add
residue quotients, graded annotations, relational witnesses,
ordinal-indexed closure, etc.

## The loss / residue pairing

Every information-losing map `f : A → B` admits two dual framings:

| Framing | What it tracks |
|---|---|
| **Loss side** | What information `y` alone fails to recover about `x`. |
| **Residue side** | What information the typed remainder `Echo f y` *does* record. |

Classical framings of information loss (Shannon entropy, Landauer
erasure, fiber cardinality, quotient by equivalence, abstraction in
program analysis) describe the loss side quantitatively. Echo Types
is the project of naming and reasoning about the residue side
*structurally*. The two sides are dual: loss tells you how much is
gone; residue tells you what shape the "not gone" has.

Crucially, two maps with the same *loss-side* characterisation can
have very different *residue-side* structure. Shannon-entropy-equal
maps can admit different echo types.

## Project goals

1. **Explicit.** Make the residue type a first-class named entity for
   every context in which information loss appears.
2. **Compositional.** Behave well under function composition,
   parallel product, slicing, and change of universe.
3. **Axis-aware.** Distinguish kinds of echoes along the axes in
   `taxonomy.md` rather than presenting "the" echo construction.
4. **Formally tractable.** The theory is implementable in
   `--safe --without-K` Agda without postulates, at least for the
   extensional/intensional core and a growing list of canonical
   examples.
5. **Portable.** Usable outside Agda as a conceptual vocabulary for
   database provenance, compiler analyses, verified abstraction, and
   ML interpretability, even where no proof assistant is involved.

## What Echo Types is *not* claiming

- **Not a new type-former** in its own right, in the bare definition.
  `Echo f y` as defined above is literally a fiber. The claim is
  editorial: that studying fibers systematically *as residues of
  information loss*, in an intensional setting with proof-relevant
  witnesses, is worthwhile. See `docs/adjacency/hott-fibers.adoc`
  for the honest adjacency assessment.
- **Not a theorem of ordinal analysis.** The ordinal-notation /
  Buchholz workstream in this repo (`docs/buchholz-plan.adoc`) is a
  parallel, syntactic development; its relationship to Echo Types
  via `EchoOrdinal.agda` is a bridge, not a reduction. At present,
  the current admitted Buchholz core has a closed well-foundedness
  route, while the full intended order remains open at the
  shared-binder internalization step.
- **Not a completed categorical semantics.** See
  `docs/assessment.adoc` for the current M5 verdict.

## Extensional shadow vs intensional core

This distinction is load-bearing for the rest of the theory and is
developed in detail in `taxonomy.md`. Briefly:

- The **extensional shadow** of `Echo(f)` is the subset of `B` on
  which `Echo f y` is inhabited — equivalent to `image(f)`. The
  shadow forgets every proof-relevant detail.
- The **intensional core** is the full proof-relevant witness family
  `{Echo f y | y : B}`. Two maps with identical extensional shadows
  (same image) can have very different intensional cores (different
  preimage structures, different equality evidence).

Echo Types lives primarily in the intensional core. The shadow
exists, is useful for sanity checks, and is the quantity that
classical information theory measures. It is *not* what this theory
is fundamentally about.

## Next reading

- `taxonomy.md` — axes along which echoes differ.
- `examples.md` — worked cases.
- `composition.md` — how `Echo` behaves under function composition.
- `roadmap.md` — what can advance without the current proof blockers,
  and what cannot.
