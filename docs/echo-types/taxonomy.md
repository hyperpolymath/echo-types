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
- Approximate (new, not yet in Agda):
  `EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)` for some metric on `B`.

The approximate version appears implicitly in numerical
computation, sensor-fusion pipelines, and lossy compression. It is
**not yet formalised** in this repo. Open question: what is the
right universal formulation of an "ε-echo" and what do its
composition laws look like?

*Conjecture.* Approximate echoes compose with an additive error:
`ε₁-echo(f) + ε₂-echo(g) ⊑ (ε₁ + ε₂)-echo(g ∘ f)` — roughly, tolerances
accumulate along composition. Requires careful statement.

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

## Cross-classification table

A first cut at placing existing modules on the axes. Entries marked
`?` are not yet pinned down. Entries marked `·` are not applicable.

| Module | Ext/Int | Exact/Approx | Local/Global | Canonical | Compositional | Static/Dynamic | Proof-rel |
|---|---|---|---|---|---|---|---|
| `Echo` | Int | Exact | Global | Canon | Expected | Static | Yes |
| `EchoCharacteristic` | Both | Exact | Local | Canon | ? | Static | Yes |
| `EchoResidue` | Int→Shadow map | Exact | Global | Canon | ? | Static | Yes |
| `EchoIndexed` | Int | Exact | Global | Pres-dep by role | ? | Static | Yes |
| `EchoChoreo` | Int | Exact | Local | Pres-dep | ? | Dynamic | Yes |
| `EchoEpistemic` | Int | Exact | Global | Pres-dep by agent | ? | ? | Yes |
| `EchoLinear` | Int | Exact | Global | Canon | ? | Static | Yes |
| `EchoGraded` | Int | Exact | Global | Canon | Expected | Static | Yes |
| `EchoTropical` | Int | Approx-ish | Local | Pres-dep | ? | Static | Yes |
| `EchoOrdinal` | Int | Exact | Local | Canon | ? | Static | Yes |

Multiple `?` entries are open research: the compositional behaviour
of the choreographic, epistemic, and tropical echoes has not been
systematically checked and may turn out to differ from the clean
composition law for the base `Echo`.

---

## Open: new axes worth considering

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
