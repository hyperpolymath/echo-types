# Echo Types — Taxonomy

**Status:** working taxonomy. Axes below are working distinctions,
not committed definitions. Each axis carries at least one
distinguishing example that forces the distinction to be real.

---

## Axis 1 — Extensional vs intensional

*Definition.* The **extensional shadow** of `Echo(f)` is the
set-valued indicator
`Shadow(f) = { y : B | Echo f y is inhabited } = image(f)`.
The **intensional core** is the full proof-relevant family
`{ Echo f y | y : B }`, with each fiber inspected up to its
witness structure `(x , p : f x ≡ y)`.

*Distinguishing test.* Two maps with identical extensional shadow
may have different intensional cores.

*Example forcing the distinction.*
- `f : ℕ → ℕ`, `f n = 0`.
- `g : ℕ × ℕ → ℕ`, `g (m, n) = 0`.

Both have `image = {0}`, so `Shadow(f) = Shadow(g)`. But
`Echo f 0 ≃ ℕ` while `Echo g 0 ≃ ℕ × ℕ` — same extensional shadow,
distinct intensional core.

*Agda anchor.* All modules in this repo that pin proof-relevant
witnesses live in the intensional layer. `EchoCharacteristic.collapse`
and `EchoResidue.EchoR` are examples of "projecting to the shadow"
(forgetting witness structure).

*Stable axis for the rest of the document.*

---

## Axis 2 — Exact vs approximate

*Definition.* An echo is **exact** when `Echo f y` records the full
preimage with definitional equality at the witness. It is
**approximate** when the witness records only up to some coarser
relation `~` on `A` (e.g. approximate equality, bounded distance).

*Distinguishing test.* Substitute `≡` by some relation `R : A → A → Set`
and ask whether the theory still names the residue coherently.

*Example.*
- Exact: `Echo f y = Σ A (λ x → f x ≡ y)`.
- Approximate: `EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)` for a
  pseudo-metric on `B`. **Formalised** in `proofs/agda/EchoApprox.agda`,
  parametric over a `Tolerance` monoid and a `PseudoMetric`.

The approximate version appears implicitly in numerical
computation, sensor-fusion pipelines, and lossy compression.

*Conjecture (now a theorem).* Approximate echoes compose with an
additive error under a non-expansive outer leg:
`ε₁-echo(f) + ε₂-echo(g) ⊑ (ε₁ + ε₂)-echo(g ∘ f)`. Realised in
`EchoApprox.Approx.echo-approx-compose`. The non-expansiveness
hypothesis on the outer leg is the minimal extra assumption — without
it an amplifying second leg can blow ε₁ up arbitrarily on the way
through.

---

## Axis 3 — Local vs global

*Definition.* A **local** echo describes the remainder at one
specific `y : B`. A **global** echo describes a coherent family
indexed by every `y`, with some compatibility between fibers.

*Distinguishing test.* Does the theory care about how
`Echo f y₁` and `Echo f y₂` relate when `y₁` and `y₂` are in the
same equivalence class or on the same trajectory?

*Example.*
- Local: `Echo f y` alone, for a specific y.
- Global: `Echo f` as a type-level function `B → Set`, with induced
  structure such as `map-over : MapOver f f' → ∀ y → Echo f y → Echo f' y`.

*Agda anchor.* `map-over` and `map-over-comp` in `Echo.agda` are
the glue that promotes local echoes to a global, functorial object.

---

## Axis 4 — Canonical vs presentation-dependent

*Definition.* A **canonical** echo is invariant under re-presentation
of `f` and its codomain. A **presentation-dependent** echo encodes
information that survives only as long as the current representation
does.

*Distinguishing test.* Apply an isomorphism on the domain or codomain
and check whether the echo type is isomorphic.

*Example.*
- Canonical: `Echo f y` as a dependent sum is canonical under
  isomorphism of `A` and `B` up to transport.
- Presentation-dependent: parser-state echoes record the specific
  token sequence that produced a parse tree; a different (but
  isomorphic) tokenisation yields a different echo.

*Open question.* Is there a systematic way to extract the
canonical-part of a presentation-dependent echo, analogous to
quotienting by a symmetry group? This could be the "canonical-form"
operator for echoes.

---

## Axis 5 — Compositional vs non-compositional

*Definition.* **Compositional** echoes satisfy a clean law relating
`Echo(g ∘ f)` to `Echo(f)` and `Echo(g)` (see `composition.md`).
**Non-compositional** echoes do not — computing `Echo(g ∘ f)` requires
global information beyond the component echoes.

*Distinguishing test.* Factor a map through an intermediate type and
ask whether the echo factors accordingly.

*Example.*
- Compositional (expected): fiber-based echoes, since
  `Σ A (λ x → (g ∘ f) x ≡ y) ≃ Σ B (λ b → Σ A (λ x → f x ≡ b) × g b ≡ y)`
  up to a canonical isomorphism.
- Non-compositional (conjectural): approximate echoes where the
  tolerance on `g ∘ f` is not a function of the tolerances on `f`
  and `g` alone — e.g. when the two stages amplify or cancel.

*Open question.* Is there a class of echo types that is always
compositional, and another that provably is not? Strongest version:
are there functors `EchoC : A → B → Set` and `EchoN : A → B → Set`
exhibiting exactly the split?

---

## Axis 6 — Static vs dynamic

*Definition.* **Static** echoes are determined at compile time (or
proof construction) from the shape of `f`. **Dynamic** echoes are
determined only at runtime, from data produced during execution.

*Distinguishing test.* Can `Echo f y` be computed from `f` and `y`
alone, or does it require observing a specific computation trace?

*Example.*
- Static: `Echo f y` for a known pure function `f` with known `y`.
- Dynamic: the residue of a concurrent scheduler, where the same
  program can produce different echoes depending on interleaving.
  Formalised partially in `EchoChoreo.agda` via role-indexed
  observation.

---

## Axis 7 — Proof-relevant vs proof-irrelevant

*Definition.* A **proof-relevant** echo distinguishes different
proofs that `f x = y`, treating them as different inhabitants of the
residue. A **proof-irrelevant** echo collapses all such proofs to a
single witness.

*Distinguishing test.* In an intensional type theory, are there two
inhabitants of `Echo f y` that share the same `x` but differ in `p`?

*Example.*
- Proof-relevant (current Agda default under `--without-K`):
  different `p : f x ≡ y` can in principle be distinct. In practice
  all current examples in this repo use `refl` exclusively, so the
  proof-relevant-ness is latent rather than exploited.
- Proof-irrelevant: truncate `Echo f y` by a higher inductive type
  `∥ Echo f y ∥`, or work in a setoid where `p` is modulo an
  equivalence relation.

*Open question.* Which theorems in the current Agda development
actually require proof-relevance, and which collapse identically if
`Echo` is propositionally truncated? A spotcheck of
`EchoCharacteristic.echo-true≢echo-false` suggests the distinction
is load-bearing there.

---

## Axis 8 — Information-theoretic vs computational access

*Definition.* An echo is **information-theoretically accessible**
when `Echo f y` is merely *inhabited* as a type — i.e. a witness
`(x , p : f x ≡ y)` exists in the metatheory. An echo is
**computationally accessible** when a concrete procedure produces
such a witness in bounded resources given `y`. Information-theoretic
accessibility is a property of the type; computational accessibility
is a property of an accompanying algorithm.

*Distinguishing test.* Does the echo's usefulness collapse when we
restrict to witness-extraction algorithms of a fixed complexity
class?

*Example forcing the distinction.*
- `H : {0,1}* → {0,1}ⁿ`, a cryptographically strong hash function.
  `Echo H y` is information-theoretically inhabited for every `y ∈
  image(H)` (pigeonhole — there exist preimages), but computationally
  inaccessible under the standard security assumption (no
  polynomial-time algorithm produces a witness). See `examples.md` §8.
- `square⁻¹ : ℕ → ℕ` under the constructive square-root algorithm.
  Same information content as `Echo square`, but the witness is
  produced in `O(log n)` operations. Computationally accessible.

*Why it is a separate axis.* Axes 1–7 are properties of the echo
type as a mathematical object — they do not depend on any notion of
cost, algorithm, or resource. Axis 8 does. Two echoes can be
identical on every other axis (same extensional shadow, same
intensional core, same proof relevance, etc.) and differ only in
whether a witness is reachable by a feasible algorithm. The security
of every modern cryptosystem depends on this axis being real.

*Agda anchor.* `EchoDecidable.agda` formalises refinement 3 below
(decidability-respecting echo) as the first axis-8 artifact under
`--safe --without-K`. Full cost-tracking refinements (1, 2, 4) are
not yet formalised — Agda's type system does not express complexity
bounds, so asymptotic computational access cannot be named at the
type level without further machinery. Adjacent stdlib pieces:
- `Data.Nat.Logarithm.⌊log₂⌋` and arithmetic complexity conventions
  admit informal-level statements like "this function runs in `O(n
  log n)`", but without a cost monad.
- `EchoLinear.agda` and `EchoGraded.agda` restrict what one can *do*
  with witnesses via usage modes and grades. These are proxies for
  resource control, not full computational-access tracking.

*Candidate refinements of `Echo` that would capture this axis.*

1. **Cost-indexed echo.** Pair `Echo f y` with a witness-extraction
   bound: `CEcho f y cost = Σ (Echo f y) (λ _ → Extractor f y cost)`.
   Requires a resource monad or a cost-passing semantics.

2. **Graded access modality.** `Echo^c f y` at grade `c` means
   "witness is reachable with `≤ c` steps". A graded semiring on the
   cost indexes gives composition. `EchoGraded.agda` is the natural
   host; the grade would need a complexity-class interpretation
   (e.g. polynomial vs super-polynomial).

3. **Decidability-respecting echo.** `EchoDec f y = Dec (Echo f y)`
   pairs the echo with a *constructive decision procedure*. Weaker
   than full cost-tracking but enough to distinguish "feasibly
   decidable" from "mathematically inhabited". **Formalised** in
   `proofs/agda/EchoDecidable.agda` as the first axis-8 artifact.

*Refinement choice (chosen first formalisation target).*
Refinement 3 is the right starting point under `--safe --without-K`.
It is the only one of the four candidates that lives entirely inside
the existing type theory: no resource monad, no graded semiring with
a complexity-class interpretation, no abstract machine. `Dec` is
already in the standard library, and the gap between `Echo f y`
(inhabited) and `Dec (Echo f y)` (constructively decided) is
exactly the gap axis 8 names. Formalising 3 first lets the heavier
refinements (1, 2, 4) be added later as orthogonal layers, each
projecting to the decidability-respecting echo by forgetting cost
information. Realised in `EchoDecidable.agda` with headline lemmas
`echo-dec-intro`, `echo-dec-pull-yes`, `echo-dec-respect-≡`,
`echo-dec-fin`, `echo-dec-compose-with-search`.

4. **Witness-search abstract machine.** Model the extractor as a
   term in a bounded-step abstract machine and pair it with the
   echo. Heavier; more faithful to actual cryptographic modelling.

*Open question.* Is there a single refinement that subsumes all four?
My guess is no: (1) and (4) track asymptotic cost, (2) and (3)
track discrete feasibility classes. They probably live on a small
lattice of access-tracking theories. Concretely, refinement 3 (now
formalised) gives the bottom of the lattice: every other refinement
projects down to it by erasing cost data.

*Composition conjecture.* Computational accessibility composes
**multiplicatively** along `g ∘ f` in the canonical case — the
cost of extracting a `g ∘ f` witness is bounded by the product of
component costs. This is the standard complexity composition and
should carry over; would need to be stated carefully since the
accumulation iso of `composition.md` §1 introduces an intermediate
`b : B` whose extraction cost is implicit.

*Worked example motivating the axis.* Hash chains in a blockchain.
Each block's header is a pre-image echo over the previous block's
hash. Information-theoretically, the entire chain's residue structure
is determined by any final hash value. Computationally, reconstructing
earlier blocks from the final hash alone is infeasible — precisely
the property that makes the chain tamper-evident. The current Echo
Types framework cannot name this distinction as a type-level fact.

---

## Cross-classification table

A first cut at placing existing modules on the axes. Entries marked
`?` are not yet pinned down. Entries marked `·` are not applicable.
The access column uses `Info` for information-theoretic only (typical
for a theorem-prover module with no resource semantics) and is the
uniform default at this stage — no module currently models
computational access as a first-class property.

| Module | Ext/Int | Exact/Approx | Local/Global | Canonical | Compositional | Static/Dynamic | Proof-rel | Access |
|---|---|---|---|---|---|---|---|---|
| `Echo` | Int | Exact | Global | Canon | Expected | Static | Yes | Info |
| `EchoCharacteristic` | Both | Exact | Local | Canon | ? | Static | Yes | Info |
| `EchoResidue` | Int→Shadow map | Exact | Global | Canon | ? | Static | Yes | Info |
| `EchoIndexed` | Int | Exact | Global | Pres-dep by role | ? | Static | Yes | Info |
| `EchoChoreo` | Int | Exact | Local | Pres-dep | ? | Dynamic | Yes | Info |
| `EchoEpistemic` | Int | Exact | Global | Pres-dep by agent | ? | ? | Yes | Info |
| `EchoLinear` | Int | Exact | Global | Canon | ? | Static | Yes | Info (proxy) |
| `EchoGraded` | Int | Exact | Global | Canon | Expected | Static | Yes | Info (proxy) |
| `EchoTropical` | Int | Approx-ish | Local | Pres-dep | ? | Static | Yes | Info |
| `EchoOrdinal` | Int | Exact | Local | Canon | ? | Static | Yes | Info |

Multiple `?` entries are open research: the compositional behaviour
of the choreographic, epistemic, and tropical echoes has not been
systematically checked and may turn out to differ from the clean
composition law for the base `Echo`. The `Info (proxy)` marks on
`EchoLinear` and `EchoGraded` indicate modules whose usage modes and
grade semirings *approximate* cost-tracking at the access axis but
do not commit to an algorithmic-cost interpretation.

---

## Open: new axes worth considering

Axes listed here have distinguishing examples but have not been
developed far enough to promote to a numbered axis.

- **Reversibility axis.** Does `f` admit a section? Partial section?
  No section? The shape of `Echo(f)` changes sharply across these.
  Evidence: `no-section-collapse` in `EchoCharacteristic.agda`.
- **Topological axis.** When `A` and `B` carry topologies, is
  `Echo(f)` a sheaf, a cosheaf, neither? Could subsume the
  local/global distinction more sharply.
- **Category-of-loss axis.** The intended morphisms between echo
  types may themselves form a category with interesting properties
  (e.g. all morphisms factor through a residue). Currently indirect
  in `EchoCategorical.agda`; worth an explicit axis once developed.

*History note.* Axis 8 (information-theoretic vs computational
access) was promoted from this list on the same commit that added
it as a numbered axis. The cryptographic-hash example in
`examples.md` §8 was the case that forced the promotion: no other
axis could distinguish "preimage exists" from "preimage is findable".
