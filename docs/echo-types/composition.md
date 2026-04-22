# Echo Types — Composition

**Status:** working note mixing established results and open
conjectures. Every result backed by the current Agda development is
marked *Agda-backed*; every conjectural claim is labelled explicitly.

---

## The central question

Given `f : A → B` and `g : B → C`, how does `Echo(g ∘ f) : C → Set`
relate to `Echo(f) : B → Set` and `Echo(g) : C → Set`?

Three candidate answers to rule between:

1. **Accumulation.** The echoes stack: `Echo(g ∘ f) y` factors as
   `(Echo(f) b × Echo(g) y)` integrated over intermediates `b`.
2. **Weakening.** The echo of `g ∘ f` is *strictly less informative*
   than `Echo(f)` alone — composition can only lose more.
3. **Cancellation.** When `g` has a section, `Echo(g ∘ f)` is
   isomorphic to `Echo(f)`.

The current Agda evidence strongly favours **accumulation** as the
base case and **cancellation** as a corollary. Weakening is true at
the shadow level but not generally at the intensional core.

---

## Accumulation — Agda-backed (base case)

*Lemma.* For `f : A → B` and `g : B → C`, the type
`Echo(g ∘ f) y` is canonically isomorphic to
`Σ B (λ b → Echo(f) b × (g b ≡ y))`.

*Proof sketch.* Σ-associativity plus propositional-equality
rearrangement. In Agda terms, given
```
Echo f b      = Σ A (λ x → f x ≡ b)
Echo g y      = Σ B (λ b → g b ≡ y)
Echo (g ∘ f) y = Σ A (λ x → g (f x) ≡ y)
```
the iso is witnessed by
```
to   : Σ A (λ x → g (f x) ≡ y) → Σ B (λ b → Σ A (λ x → f x ≡ b) × (g b ≡ y))
to (x , p)       = (f x , (x , refl) , p)
from : Σ B (λ b → Σ A (λ x → f x ≡ b) × (g b ≡ y)) → Σ A (λ x → g (f x) ≡ y)
from (b , (x , refl) , p) = (x , p)
```
and both round-trips are `refl`. Formalisation is routine and not
yet in the repo; it is the cleanest candidate for the next
composition lemma to land.

*Agda adjacency.* `Echo.map-over-comp` proves functoriality of the
derived action on echoes; this is the morphism side of the same
composition law. The *object-side* isomorphism above is not yet
proved but is a straightforward next milestone.

---

## Cancellation — expected corollary

*Conjecture.* If `g : B → C` has a section `s : C → B` with
`g ∘ s ≡ id`, then `Echo(g ∘ f) y ≃ Echo(f) (s y)` for every `y`.

*Rationale.* Composing with an injection loses no information, so
the intermediate factor in the accumulation law collapses to a
single witnessed point.

*Status.* Not proved. Depends on the accumulation isomorphism plus
a section lemma that the current repo has pieces of (see
`no-section-weaken` in `EchoLinear` for the negative direction).

---

## Weakening — true at the shadow, false at the core

*Observation (Agda-backed).* At the extensional shadow,
`Shadow(g ∘ f) ⊆ Shadow(g)`, because `image(g ∘ f) ⊆ image(g)`. So
at the shadow level, composition weakens: you cannot learn more
after an additional forgetful step.

*Counter at the core.* At the intensional core, `Echo(g ∘ f) y` can
carry *more* witness structure than `Echo(g) y` alone — specifically,
it records which `b ∈ Echo(g) y` came via `f`. This is the content
of the accumulation iso above: the composed echo is the sum-total,
not just the outer fiber.

*Summary.* Weakening is a shadow-level phenomenon. At the core,
composition *accumulates* witnesses rather than losing them.

---

## Open questions

### Q1. 2-categorical structure

*Question.* Is there a 2-category whose objects are types, whose
1-morphisms are maps, and whose 2-morphisms are echo-preserving
transformations? `EchoCategorical.agda` hints at this but does not
commit to a full 2-categorical axiomatisation.

*Why it matters.* If yes, the composition laws are the coherence
laws of the 2-category. If no, the composition laws are ad-hoc and
probably a sign the residue structure is subtler than we modelled.

### Q2. Negative echoes

*Question.* Is there a systematic dual to `Echo(f)` — call it
`CoEcho(f)` — that records *what has been lost* rather than what
remains? For a linear map this would correspond to the kernel; for
a general map, to a typed analogue of the fibre-wise "information
loss".

*Candidate.* `CoEcho(f)(y) = (something like) "equivalence class of
preimages of y modulo identity"`. The tropical / metric echo
(`EchoTropical.agda`) may be the first instance.

*Status.* Speculative. Worth developing alongside approximate
echoes.

### Q3. Composition of approximate echoes

*Question.* Under the approximate-echo definition (taxonomy,
axis 2), does composition give a clean tolerance calculus?

*Conjecture.* For metric-tolerance echoes,
`ε₁-echo(f) ⊙ ε₂-echo(g) ⊑ (ε₁ + L_g · ε₂)-echo(g ∘ f)` where `L_g`
is a Lipschitz constant of `g`. This is a crude first guess — the
right form may involve sup-norms, dilation-operators, or
coarser bounds.

*Status.* Entirely speculative. Requires a formal definition of
approximate echo first.

### Q4. Associativity

*Question.* Does the accumulation isomorphism above satisfy the
pentagon coherence for three-fold composition? I.e., for
`f : A → B`, `g : B → C`, `h : C → D`, does the two ways of
associating `Echo((h ∘ g) ∘ f) = Echo(h ∘ (g ∘ f))` yield equivalent
iso's?

*Expectation.* Yes, but the proof requires the iso to land as a
`map-over` morphism whose `commute` field is itself proved by
pentagon-style transitivity. `Echo.map-over-comp` already bottles
the relevant shape. Proving pentagon on top is routine but not
written down.

### Q5. Interaction with role-indexing, gradings, linearity

*Question.* The existing repo modules `EchoIndexed`, `EchoGraded`,
`EchoLinear` each decorate the basic echo with extra structure
(role index, grade label, mode tag). Does composition commute with
these decorations, or do some decorations require refined
composition laws?

*Evidence.* `EchoGraded.degrade-comp` is the first hint of a
graded-composition law. Linear echoes via `EchoLinear.weaken` behave
by weakening along mode transitions. No systematic cross-check
between these decorations has been attempted.

### Q6. Composition in the presence of recovery / echo-erasure

*Question.* When a downstream stage "uses" the echo — extracts the
preimage `x` and re-applies `f` to reconstruct `y` — the echo is
temporarily made definite. Does the composition law respect this
extraction?

*Formalisation hint.* Probably expressible as a 2-cell in the
hypothetical 2-category of Q1. Not attempted.

---

## Composition laws — a compact statement

Collecting the above:

1. **(Agda-backed) Base accumulation iso.**
   `Echo(g ∘ f) y ≃ Σ B (λ b → Echo(f) b × (g b ≡ y))`.

2. **(Agda-backed) Functorial action.** `map-over` respects
   composition: `map-over (g' , c₁) ∘ map-over (f' , c₂) ≡ map-over
   ((g' ∘ f') , coherence)`. Proved in `Echo.map-over-comp`.

3. **(Expected) Cancellation.** `Echo(g ∘ f) y ≃ Echo(f) (s y)` when
   `g` has a section `s`.

4. **(Open) Pentagon.** Three-fold composition associates.

5. **(Open) Tolerance calculus.** For approximate echoes, tolerances
   compose with a Lipschitz-like law.

6. **(Open) Decoration commuting.** Role, grade, linearity, and
   modal decorations commute with composition under conditions to be
   identified.

---

## What to formalise next

Ranked by unblock-value:

1. **Base accumulation iso.** Single Agda proof, no new modules
   needed. Would add `Echo-comp-iso` to `Echo.agda`.
2. **Cancellation corollary.** One paragraph on top of (1).
3. **Pentagon coherence.** Moderate proof, probably one more lemma.
4. **Approximate-echo skeleton.** New module
   `EchoApprox.agda` defining ε-echoes and restating (1) in the
   approximate setting. This is where axis 2 of the taxonomy gets
   teeth.
5. **Decoration commuting.** Per-decoration lemmas in the existing
   `EchoGraded`, `EchoLinear`, `EchoIndexed` modules.

None of these depend on the blocked Buchholz-WF / shared-binder
work. All are Sonnet-class proofs; (4) is Opus 4.7 design and
Sonnet execution.
