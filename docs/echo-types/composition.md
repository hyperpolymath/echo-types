<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Echo Types — Composition

**Status:** working note mixing established results and open
conjectures. Every result backed by the current Agda development is
marked *Agda-backed*; every conjectural claim is labelled explicitly.

> **Forward-link (2026-05-27).** The composition-track narrative this
> doc maintains has been consolidated into
> [`fibration-package.adoc`](fibration-package.adoc) (`map-over` action
> + `Echo-comp-iso` accumulation + `cancel-iso` cancellation +
> pentagon coherence, threaded with reading order). The
> fibration-package consolidation is now the recommended entry point;
> this doc remains as the longer-form working-note narrative with the
> per-section conjecture-vs-proof labelling. The proofs cited herein
> are all Agda-backed and pinned in `Smoke.agda`.

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

*What is landed (round-trips + packaging).* The two round-trips
`cancel-iso-from-to` and `cancel-iso-to-from` are now proved in
`Echo.agda`, each parameterised by its respective triangle-identity
coherence:

* `cancel-iso-from-to` needs `triangle₁ : ∀ b → cong g (s-left b) ≡
  s-right (g b)`.
* `cancel-iso-to-from` needs `triangle₂ : ∀ y → cong s (s-right y) ≡
  s-left (s y)`.

One triangle implies the other in HoTT (any quasi-inverse can be
upgraded to a half-adjoint equivalence), but constructing the upgrade
requires non-trivial path algebra, so both are taken as explicit
arguments. The full iso then packages via stdlib's `mk↔ₛ′` as
`Echo.cancel-iso : (s-left ...) (s-right ...) (triangle₁ ...)
(triangle₂ ...) → Echo (g ∘ f) y ↔ Echo f (s y)`. Companion
`Echo.Echo-comp-iso` does the same for the unconditional
accumulation iso (no triangles needed). All five pinned in
`Smoke.agda`.

*Correction to earlier wording.* A bare section on `g` (i.e.,
`s-right` only) is not enough to collapse the Σ-over-intermediate
in the accumulation law; the earlier version of this section
claimed otherwise. The correction is that both `s-left` and
`s-right` are needed, and the full iso additionally needs the two
triangle identities — both are passed explicitly.

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

### Q1. 2-categorical structure — closed (rule-out)

*Verdict.* No 2-category. The five structurally plausible
organisations (echo as a lax/oplax 2-functor; slice-of-echos
with `IsMediator` cells; double category; graded bicomonad;
Grothendieck stack) each collapse to existing 1-cat +
graded-comonad + pullback content because every would-be 2-cell
appears as `refl` or is prop-forced trivial by `≤g-prop` /
`⊑-prop`. The composition laws (accumulation iso, cancel-iso,
pentagon Σ-assoc, decoration commuting) are *not* 2-coherence
laws of a hypothesised 2-category — they are the 1-categorical
composition laws of a pullback-presented type, full stop. See
`docs/echo-types/decisions/no-2-cat.adoc` for the full closure
note (verdict / evidence / implication).

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

*Status (updated).* No longer entirely speculative. The
non-expansive case (`L_g = 1`) is landed as
`EchoApprox.Approx.echo-approx-compose` in additive form
`(ε₁ + ε₂)-echo(g ∘ f)`. The compositional *shape* — whether the
forward/backward maps form a strict iso analogous to
`Echo-comp-iso` — is settled in the negative: it is a *retract*,
not an iso, because the RHS Σ admits multiple splits of the budget
and the chosen intermediate `b` is not pinned by the input. The
axis-2 design note (`/tmp/echo-types-exploration/axis2-approximate.md`
§5) gives the full discussion.

First slice of the retract landed in `EchoApprox.agda`:
`echo-approx-comp-sound` (RHS-Σ → LHS via `echo-approx-compose`),
`echo-approx-comp-retract-to` (canonical-split LHS → RHS-Σ section
at `b := f x`, `ε₁ := zero`, `ε₂ := ε`), and
`echo-approx-comp-retract-A` (A-component round-trip preserves the
witness up to `refl`).

Rung-C slice (post-PR-#74, design call resolved in favour of option
(b)): a separate `BalancedTolerance` record layered on `Tolerance`
(mirroring how `Separated` layers on `PseudoMetric`), carrying
`+-identityˡ : ∀ ε → zero + ε ≡ ε` and `+-identityʳ : ∀ ε → ε + zero
≡ ε`. The base `Tolerance` interface stays untouched; lemmas that
need the identity laws take an explicit `BalancedTolerance`
hypothesis. With it landed:
`echo-approx-comp-retract-B` (B-component pin: the canonical-split
section picks `b := f x` definitionally, `refl`),
`echo-approx-comp-retract-budget` (`(zero + ε) ≡ ε` from
`+-identityˡ`), and `echo-approx-comp-retract-from-to` (budget-aligned
A-component round-trip: `proj₁ (subst _ (+-identityˡ ε) (sound
(retract-to e))) ≡ proj₁ e`). The full transported equality `subst _
(+-identityˡ ε) (sound (retract-to e)) ≡ e` is NOT discharged — it
would require propositionality of the order `_≤_` on the inner
bound, which `Tolerance` deliberately does not assert; the
A-component statement is the strongest available without that extra
hypothesis.

Second slice landed alongside (axis-2 design note §7 obligations
7 and 8): `Separated` (separation predicate on the pseudo-metric:
`dist b₁ b₂ ≤ zero → b₁ ≡ b₂`),
`echo-approx-zero-collapses-strict` (under separation, every
zero-tolerance approximate echo IS a strict echo with the same
A-witness — the §4 "Approximate → strict, only when separated, at
ε = 0" statement made formal), and the axis-1 shadow lemmas
`echo-shadow-A`, `echo-shadow-iso-{to,from}`,
`echo-strict→approx-shadow-A`,
`echo-strict→approx-collapse-shadow-A`. The last two pin the
axis-1 / axis-2 cross-classification: the A-component (the axis-1
"shadow" of the approximate echo) is preserved on the nose by
`echo-strict→approx` and round-trips definitionally through the
zero-collapse under separation.

The Lipschitz generalisation (`L_g ≠ 1`) remains deferred — it
requires multiplication on `Tolerance`, another interface call.
The full transported LHS round-trip equality (beyond the
A-component) remains deferred too — it needs `_≤_`-propositionality,
which is structurally orthogonal to `BalancedTolerance`.

### Q4. Associativity — landed

*Question.* Does the accumulation isomorphism above satisfy the
pentagon coherence for three-fold composition? I.e., for
`f : A → B`, `g : B → C`, `h : C → D`, do the two ways of
associating `Echo((h ∘ g) ∘ f) ≃ Echo(h ∘ (g ∘ f))` yield equivalent
iso's?

*Answer.* Yes, at both levels. The two projection-pentagon lemmas
`Echo-comp-iso-pent-B` and `Echo-comp-iso-pent-echo` (both `refl`)
confirm that the two natural factorings — inner-first `(f, h∘g)`
versus outer-first `(g∘f, h)` then `(f, g)` — produce the same
`f x` at the B-component and the same `(x , refl) : Echo f (f x)`
at the Echo-f witness. The full Σ-associativity iso between the
two nested Σ-shapes (which differ by whether the intermediate
`c : C` with `g b ≡ c` is carried or absorbed) lands as
`Echo-comp-pent-Σ-assoc-{to, from, from-to, to-from}` and is
packaged as a stdlib `Function.Bundles._↔_` via
`Echo-comp-pent-Σ-assoc`. Both round-trips reduce definitionally
once `g b ≡ c` has been pinned, so this is a strict iso inside
`--safe --without-K`.

*Confirmed this is the right shape.* Both lemmas land as `refl`
without any `trans-assoc` / `cong-trans` manipulation, because
`Echo-comp-iso-to`'s body `(x , p) ↦ (f x , (x , refl) , p)` is
structurally symmetric in the outer function — the f-component
and witness do not depend on which outer is peeled off. If the
iso had a `trans`-shaped body instead, pentagon would have
required real coherence lemmas. The `refl` outcome is the
*definitive characterisation*: pentagon is identity — what would
be the bicategorical associator-2-cell — and is forced trivial
here. With the 2-cat shape ruled out (§Q1;
`decisions/no-2-cat.adoc`), this is no longer "evidence the iso
has the right design" but the 1-categorical-final reading of it.

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

*Formalisation hint (revised).* With the 2-cat shape ruled out
(§Q1; `decisions/no-2-cat.adoc`), recovery is a 1-categorical
notion: a slice morphism into `Echo f y` (the extraction step)
followed by the canonical projection, or equivalently a section
of the appropriate fibration. The earlier "expressible as a
2-cell in the hypothetical 2-category of Q1" hedge no longer
applies. Not attempted; now write-up-tractable on a 1-categorical
footing.

---

## Composition laws — a compact statement

Collecting the above:

1. **(Landed) Base accumulation iso.**
   `Echo(g ∘ f) y ≃ Σ B (λ b → Echo(f) b × (g b ≡ y))`. Proved in
   `Echo.agda` as `Echo-comp-iso-{to, from, from-to, to-from}`.

2. **(Agda-backed) Functorial action.** `map-over` respects
   composition: `map-over (g' , c₁) ∘ map-over (f' , c₂) ≡ map-over
   ((g' ∘ f') , coherence)`. Proved in `Echo.map-over-comp`.

3. **(Landed) Cancellation.** Forward, backward, both round-trips
   landed in `Echo.agda` as `cancel-iso-{to, from, from-to,
   to-from}`, plus the packaging `Echo.cancel-iso : ... ↔ ...`
   via stdlib's `mk↔ₛ′`. Round-trips parameterised by both
   triangle identities (`triangle₁`, `triangle₂`) — one implies
   the other in HoTT, but the constructive upgrade is non-trivial
   path algebra, so both are explicit.

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

6. **(Landed) Decoration commuting — sweep complete (2026-04-28).**
   All five decorations now commute with composition under the same
   recipe (decoration order → propositionality → join → factoring-
   free compose → via-join restatement):
   * Grade: `EchoGraded.degrade-{compose, via-join}` resting on
     `≤g-prop`, `degrade-comp`, and `_⊔g_` join structure
     (`≤g-⊔g-{left,right,univ}`).
   * Linear: `EchoLinear.degradeMode-{comp, compose, via-join}`
     along the two-mode order with `_⊔m_` join (affine top).
   * Indexed: `EchoIndexed.map-role-indexed-comp`.
   * Choreo (role): `EchoChoreo.applyChoreo-{comp, compose,
     via-join}` along `_⊑c_` (`Client ⊑c Server`) with `_⊔c_`
     join.
   * Modal (epistemic): `EchoEpistemic.knowledge-monotone-{comp,
     id}`.
   All headlines pinned in `Smoke.agda`.

---

## What to formalise next

Ranked by unblock-value. (1) and (2) landed; (3) onwards is open.

1. ~~**Base accumulation iso.**~~ Landed in `Echo.agda` as
   `Echo-comp-iso-{to, from, from-to, to-from}`.
2. ~~**Cancellation corollary.**~~ **Fully landed** as
   `cancel-iso-{to, from, from-to, to-from}` plus the
   `Function.Bundles._↔_` packaging `Echo.cancel-iso`,
   parameterised by `s-left`, `s-right`, and both triangle
   identities. See §3 above for the triangle structure.
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

---

## Anti-pattern — closing a degrade-map obligation within an endpoint

*Status: methodological note (2026-05-30). Not Agda-backed; the
upstream theorem it abstracts from IS Agda-backed.*

The per-decoration composition rung (§6, "Decoration commuting") proves
that for each decoration `D` the degrade map `degrade : ⊑ → Echo D₁ →
Echo D₂` commutes with composition under a recipe: order →
propositionality → join → factoring-free compose → via-join restatement.
The recipe makes the cross-decoration obligation — "two successive
weakenings agree with a single weakening along the composed proof" —
*explicitly* a property of the degrade map, not of either endpoint.
The upstream theorem is `EchoLinear.degradeMode-comp`
(`proofs/agda/EchoLinear.agda:93-101`), three `refl` clauses pinning
each reachable constructor pair.

**The anti-pattern.** When a decoration `D₁ ≤ D₂` connects two
indexed instances of a fiber, an obligation that mentions *both*
endpoints does not close inside either endpoint alone. Attempting to
discharge it by strengthening a typing rule of `D₁` (or `D₂`) with a
premise that references the other endpoint's invariant is structurally
ill-shaped: the load-bearing content lives on the degrade arrow.

**Detection heuristic.** If a proof attempt requires adding a premise
to a rule of one decoration that mentions a *different* decoration's
invariant (e.g. a region-presence premise on a modality-indexed rule),
the discipline is being violated. The corrective is to relocate the
obligation to the decoration map, not to thicken the endpoint.

**Empirical downstream test.** The `hyperpolymath/ephapax` project's
L1 region-capability layer admits an analogue cross-decoration
obligation. An empirical closure attempt (ephapax PR #170, merged
2026-05-27) strengthened the L1 variable rule
`T_Var_*_L1` with a region-well-formedness premise and verified the
resulting axiom remained false on a concrete typing-level
counterexample (`ERegion rv (EI32 5) : TBase TI32 at R = [rv]`). The
honest closure path identified in ephapax's `PRESERVATION-DESIGN.md`
§4.8.1 is cross-layer — the obligation lives at the L1→L2 boundary
where the effect-typed `TFun` of `T_Lam_Linear_L2` carries the
region-effect that L1's R-threading lacks. The pattern matches the
echo-types abstraction: visible source-level discrepancies *can* be
absorbed inside an endpoint (and PR #170 absorbed one), but the
cross-decoration obligation cannot.

The downstream test is not a proof of the upstream theorem — it is
empirical evidence that the discipline detects ill-shaped attempts at
the point the abstraction predicts. See echo-types#125 for the
issue thread that surfaced this observation.
