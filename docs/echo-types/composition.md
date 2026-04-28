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

## Accumulation — Agda-backed (base case, landed)

*Lemma.* For `f : A → B` and `g : B → C`, the type
`Echo(g ∘ f) y` is canonically isomorphic to
`Σ B (λ b → Echo(f) b × (g b ≡ y))`.

*Proof.* Σ-associativity plus propositional-equality rearrangement.
In Agda terms, given
```
Echo f b       = Σ A (λ x → f x ≡ b)
Echo g y       = Σ B (λ b → g b ≡ y)
Echo (g ∘ f) y = Σ A (λ x → g (f x) ≡ y)
```
the iso is witnessed by
```
to   (x , p)              = (f x , (x , refl) , p)
from (b , (x , refl) , p) = (x , p)
```
and both round-trips reduce to `refl` definitionally once the
`refl` pattern has pinned the intermediate `b` to `f x`. Landed
in `proofs/agda/Echo.agda` as `Echo-comp-iso-to`, `Echo-comp-iso-from`,
`Echo-comp-iso-from-to`, `Echo-comp-iso-to-from` (all pinned in
`Smoke.agda`).

*Agda adjacency.* `Echo.map-over-comp` proves functoriality of the
derived action on echoes; this is the morphism side of the same
composition law. The object-side iso above and the morphism-side
composition law together give a coherent two-level story for
composition.

---

## Cancellation — partial (Agda-backed maps, iso deferred)

*Statement.* If `g : B → C` has a two-sided inverse `s : C → B`
with `s-left : ∀ b → s (g b) ≡ b` and `s-right : ∀ y → g (s y) ≡ y`,
then `Echo(g ∘ f) y` and `Echo(f) (s y)` are related by a canonical
forward and backward map.

*What is landed.* Two maps in `proofs/agda/Echo.agda`, each
requiring only the relevant half of the iso structure:
```
cancel-iso-to   : (s-left  : ∀ b → s (g b) ≡ b) → Echo (g ∘ f) y → Echo f (s y)
cancel-iso-from : (s-right : ∀ y → g (s y) ≡ y) → Echo f (s y)   → Echo (g ∘ f) y
```
Pinned in `Smoke.agda` as `cancel-iso-to`, `cancel-iso-from`.

*What is deferred.* The round-trips that would promote these two
maps to a full iso are *not* proved. Under `--without-K`, the two
round-trips require a triangle-identity coherence between `s-left`
and `s-right` (roughly `cong g (s-left b) ≡ s-right (g b)`), which
is not a consequence of the two pointwise inverse laws alone — a
bare "both-way inverse" is weaker than an equivalence in HoTT
terms. The in-file comment in `Echo.agda` flags this explicitly.
Options for the full iso: (a) an equivalence record that packages
the triangle identity as a field, or (b) stdlib's
`Function.Bundles.Inverse`.

*Correction to earlier wording.* A bare section on `g` (i.e.,
`s-right` only) is not enough to collapse the Σ-over-intermediate
in the accumulation law; the earlier version of this section
claimed otherwise. The correction is that both `s-left` and
`s-right` are needed, and even then the full iso needs triangle
coherence.

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

### Q4. Associativity — partially landed

*Question.* Does the accumulation isomorphism above satisfy the
pentagon coherence for three-fold composition? I.e., for
`f : A → B`, `g : B → C`, `h : C → D`, do the two ways of
associating `Echo((h ∘ g) ∘ f) ≃ Echo(h ∘ (g ∘ f))` yield equivalent
iso's?

*Answer (partial).* Yes for the load-bearing projections. The two
pentagon-style lemmas `Echo-comp-iso-pent-B` and
`Echo-comp-iso-pent-echo` (both `refl`) confirm that the two
natural factorings — inner-first `(f, h∘g)` versus outer-first
`(g∘f, h)` then `(f, g)` — produce the same `f x` at the B-component
and the same `(x , refl) : Echo f (f x)` at the Echo-f witness. The
full Σ-associativity iso between the two nested Σ-shapes (which
differ by whether the intermediate `c : C` with `g b ≡ c` is
carried or absorbed) is the remaining open piece of pentagon
coherence.

*Evidence this is the right shape.* Both lemmas land as `refl`
without any `trans-assoc` / `cong-trans` manipulation, because
`Echo-comp-iso-to`'s body `(x , p) ↦ (f x , (x , refl) , p)` is
structurally symmetric in the outer function — the f-component
and witness do not depend on which outer is peeled off. If the
iso had a `trans`-shaped body instead, pentagon would have
required real coherence lemmas; the `refl` outcome is evidence
the iso has the right design.

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

1. **(Landed) Base accumulation iso.**
   `Echo(g ∘ f) y ≃ Σ B (λ b → Echo(f) b × (g b ≡ y))`. Proved in
   `Echo.agda` as `Echo-comp-iso-{to, from, from-to, to-from}`.

2. **(Agda-backed) Functorial action.** `map-over` respects
   composition: `map-over (g' , c₁) ∘ map-over (f' , c₂) ≡ map-over
   ((g' ∘ f') , coherence)`. Proved in `Echo.map-over-comp`.

3. **(Partial) Cancellation.** Forward and backward maps landed as
   `cancel-iso-to` (needs `s-left`) and `cancel-iso-from` (needs
   `s-right`). Round-trips deferred pending a triangle-identity
   coherence or a stdlib `Function.Bundles.Inverse` shim.

4. **(Landed) Pentagon.** Three-fold composition associates at
   the projections (`Echo-comp-iso-pent-B`, `Echo-comp-iso-pent-echo`,
   both `refl`) and at the full Σ shape
   (`Echo-comp-pent-Σ-assoc-{to, from, from-to, to-from}`). The two
   nested-Σ shapes differ only by Σ-associativity / unification of
   the intermediate base point; both round-trips reduce
   definitionally once `g b ≡ c` is pinned, so this is a strict iso
   inside `--safe --without-K`. All four iso components pinned in
   `Smoke.agda`.

5. **(Landed) Tolerance calculus.** For approximate echoes,
   tolerances compose additively under a non-expansive outer leg.
   Realised as `EchoApprox.Approx.echo-approx-compose` over a
   parametric pseudo-metric.

6. **(Partial) Decoration commuting.** Role, grade, linearity, and
   modal decorations commute with composition under conditions to be
   identified. The grade case is **landed**: `EchoGraded.degrade-compose`
   shows that any factoring of a `g1 ≤g g3` transition through an
   intermediate `g2` collapses to the same degraded echo, proved as a
   corollary of `degrade-comp` and `≤g-prop` (the order is
   propositional). `degrade-via-join` restates this through the
   join structure `_⊔g_`, with `≤g-⊔g-left/right/univ` exhibiting
   `_⊔g_` as the categorical join. The linear case is **landed** in
   `EchoLinear.agda` as `degradeMode-comp` along the mode order
   `linear ⊑ linear ⊑ affine ⊑ affine`; corollaries
   `degradeMode-id-{linear, affine}` and
   `degradeMode-strict-is-weaken` establish the relationship to the
   existing `weaken`. Indexed / role / modal cases remain open.

---

## What to formalise next

Ranked by unblock-value. (1) and (2) landed; (3) onwards is open.

1. ~~**Base accumulation iso.**~~ Landed in `Echo.agda` as
   `Echo-comp-iso-{to, from, from-to, to-from}`.
2. ~~**Cancellation corollary.**~~ Partially landed as
   `cancel-iso-to` / `cancel-iso-from`; full iso deferred pending
   triangle-identity coherence (see §3 above).
3. ~~**Pentagon coherence.**~~ Landed: projection-level
   (`-pent-B`, `-pent-echo` as `refl`) plus the full Σ-shape iso
   (`Echo-comp-pent-Σ-assoc-{to, from, from-to, to-from}`).
4. ~~**Full cancel-iso with round-trips.**~~ Landed: `Echo.cancel-iso`
   packages the four pieces (`cancel-iso-{to, from, from-to, to-from}`)
   plus both triangle-identity coherences as a single
   `Function.Bundles._↔_` record. Companion `Echo.Echo-comp-iso`
   does the same for the unconditional accumulation iso (no
   triangles needed). Built via stdlib's `mk↔ₛ′`; both round-trips
   close on the existing pointwise lemmas.
5. ~~**Approximate-echo skeleton.**~~ Landed in
   `EchoApprox.agda` with `EchoR ε f y`, `echo-approx-intro`,
   `echo-approx-relax`, and `echo-approx-compose` (additive under
   non-expansive outer leg).
6. **Decoration commuting.** Per-decoration lemmas in the existing
   `EchoGraded`, `EchoLinear`, `EchoIndexed`, `EchoChoreo`,
   `EchoEpistemic` modules. *Grade case landed*: `EchoGraded.degrade-compose`
   (per-decoration composition law) and `degrade-via-join` (its
   join-structured restatement), resting on `≤g-prop` and `degrade-comp`.
   *Linear case landed*: `EchoLinear.degradeMode-{comp,compose,via-join}`
   along the two-mode order. *Indexed case landed*:
   `EchoIndexed.map-role-indexed-comp`. *Modal case landed*:
   `EchoEpistemic.knowledge-monotone-comp` (with `knowledge-monotone-id`
   identity-step corollary). *Role/choreo case landed*:
   `EchoChoreo.applyChoreo-{comp,compose,via-join}` along the
   choreographic-reachability order `_⊑c_` (`Client ⊑c Server`),
   resting on `⊑c-prop` and the canonical `_⊔c_` join. The
   five-decoration sweep is now closed at the per-decoration
   composition rung.

None of these depend on the blocked Buchholz-WF / shared-binder
work. All are Sonnet-class proofs; (5) is Opus 4.7 design and
Sonnet execution.
