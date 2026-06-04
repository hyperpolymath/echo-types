<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
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

## Semantic fibre, avec fibre, sans fibre

The current kernel is literally a preimage fibre, but the intended
use-case is semantic: a value has crossed some declared observation or
degradation map and the question is what typed-origin structure still
lies over the observed artefact.

- **Semantic fibre** names that possible-origin structure: the set,
  approximation, or witness family of typed origins compatible with the
  observation. In the exact Agda spine it is `Echo f y`; in approximate
  or executable settings it may be a finite preimage set, bound, search
  witness, or residue-backed approximation.
- **Avec fibre** means the target-side artefact is accompanied by
  enough semantic fibre to justify the inference being made. For
  example, knowing an output is `true` under a declared projection may
  license "the source was one of these witnesses" but not "the source
  was this unique witness".
- **Sans fibre** means the artefact is only valid on the target side.
  It may be well-typed as a `B`, parse as a JSON object, validate at an
  ABI boundary, or satisfy a checksum format, while still carrying no
  declared possible-origin structure from the source side.

This is deliberately weaker than a universal boundary-system claim.
Echo Types do not replace exact typing, typed-wasm, ABI proofs, FFI
discipline, or structural-fit systems. They become relevant after a
crossing, compression, observation, corruption, archive step, or
translation has already made exact preservation unavailable and a
non-trivial "what could this still have come from?" question remains.

The vocabulary also separates neighbouring notions:

| Term | What it answers | Why it is not enough alone |
|---|---|---|
| Provenance | Where did it come from? | Often records one history or source, not the full compatible-origin type. |
| Trace / lineage | How did it get here? | Records a path, not necessarily the fibre over the final observation. |
| Residue | What lower-level evidence remains after degradation? | A residue may be weaker than the full possible-origin structure. |
| Semantic fibre | What possible typed origins still lie over this observation? | Needs a declared map and honest scope. |
| Warrant | What may we infer or do from this fibre/residue? | Useful internally, but not the headline mathematical object. |

Use **semantic fibre** or **preimage fibre** when clarity matters:
"fibre" aligns with the mathematical homotopy/preimage fibre, but can
otherwise be confused with lightweight-thread fibers or network fibre.

The doc-side prototype
`docs/echo-types/prototypes/warrant_debugger_prototype.jsx` illustrates
the warrant/debugging reading of this vocabulary. It is not a formal
artefact: it shows how an interface might disclose an empty fibre and
the epistemic cost of weakening, widening, or softening the obligations
used to restore support.

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
  for the honest adjacency assessment. *Update 2026-05-27:* the
  2026-05-27 Tier-1+2+3 spine adds NAMED STRUCTURAL ARTEFACTS on
  top of the bare fibre — the orthogonal factorisation system
  witness (`EchoOrthogonalFactorizationSystem.ofs-witness`), the
  proof-relevant image (`EchoImageFactorization.Image`), the
  classification grid (`EchoLossTaxonomy` / `EchoResidueTaxonomy`
  / `EchoDecorationStructure`). The "not a type-former" bound
  still holds at the bare definition; the editorial claim is now
  much more strongly supported by the named structural layer
  sitting on top.
- **Not a theorem of ordinal analysis.** The ordinal-notation /
  Buchholz workstream in this repo (`docs/buchholz-plan.adoc`) is a
  parallel, syntactic development; its relationship to Echo Types
  via `EchoOrdinal.agda` is a bridge, not a reduction. At present,
  the current K-free Buchholz core (`Ordinal.Buchholz.Order._<ᵇ_`)
  has a closed well-foundedness route, finite same-binder depth is
  handled by iterated mediated wrappers, and the shared-binder lex
  cases (`<ᵇ⁺-ψα`, `<ᵇ⁺-+2`) are now internalised in the extended
  relation `Ordinal.Buchholz.OrderExtended._<ᵇ⁺_` with proven
  irrefl + trans; well-foundedness for `_<ᵇ⁺_` is the next open
  step, with two design routes documented in
  `docs/echo-types/buchholz-extended-wf.md`.
- **Not (yet) a completed categorical semantics — but** Pillar F
  Gate F5 FULL PASS (2026-05-27, follow-up F-2026-05-27a)
  mechanises the full (equivalence, projection) orthogonal
  factorisation system on Type *at the qualified level* (funext
  as explicit module parameter, never a postulate). The
  unconditional pointwise content remains the funext-free
  artefact; the function-level OFS clauses are true given funext.
  See `docs/echo-types/universal-property.adoc` for the
  consolidated narrative and `docs/assessment.adoc` for the older
  M5 verdict.

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

- `MAP.adoc` — the master content map (single source of truth);
  start here if you need to find anything.
- `EchoCanonicalIdentitySuite.agda` (in `proofs/agda/`) — the
  curated single-file entry point pulling Tier-1 / Tier-2 / Tier-3
  headlines together as the "why Echo deserves a name" demo.
- `universal-property.adoc` — pullback + F4 + F5 / OFS arc
  end-to-end (the categorical-universal-property story).
- `fibration-package.adoc` — `map-over` + composition iso +
  cancellation iso + pentagon coherence (the fibration-side story).
- `taxonomy.md` — axes along which echoes differ.
- `examples.md` — worked cases.
- `composition.md` — how `Echo` behaves under function composition.
- `roadmap.adoc` — what can advance without the current proof
  blockers, and what cannot (note: `roadmap.md` was consolidated
  into `roadmap.adoc` in 2026-05-26).
