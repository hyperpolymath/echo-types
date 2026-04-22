# Echo Types — Canonical Examples

**Status:** working example library. Entries marked *Agda-backed*
have a corresponding compiled theorem in this repo. Entries marked
*informal* are described at the theory level only; they may be
formalisable later but are not proved here.

Template used for every entry:

- **Source map** — the `f : A → B` under discussion.
- **What is lost** — information that `y ∈ B` alone does not determine.
- **What remains** — structured residue of `f` given `y`.
- **Echo** — the concrete shape of `Echo f y` for this case.
- **Extensional / intensional** — where the distinguishing content sits.
- **Reference** — Agda module if applicable.

---

## 1. Sign loss under squaring

- **Source map.** `square : ℤ → ℕ`, `square n = n * n`.
- **What is lost.** The sign of `n` — `square(+3) = square(-3) = 9`.
- **What remains.** The magnitude, witnessed together with a specific
  signed preimage.
- **Echo.** `Echo square 9 = Σ ℤ (λ n → square n ≡ 9)` is inhabited
  by both `(+3 , refl)` and `(-3 , refl)`; these are distinct
  inhabitants of the echo even though they collapse to the same `9`.
- **Extensional / intensional.** Intensional — the shadow is
  `{0, 1, 4, 9, 16, …}`; the intensional core distinguishes signed
  preimages.
- **Reference.** `proofs/agda/EchoExamples.square9`.

---

## 2. Boolean component forgetting

- **Source map.** `fst : Bool × Bool → Bool`, `fst (a, b) = a`.
- **What is lost.** The second component `b`.
- **What remains.** A concrete pair whose first component is the
  observed boolean.
- **Echo.** `Echo fst a = Σ (Bool × Bool) (λ p → fst p ≡ a)`, with
  exactly two distinct inhabitants for each `a : Bool`
  (corresponding to the two choices of `b`).
- **Extensional / intensional.** Both. Shadow is `Bool` in full; the
  intensional core distinguishes `(true, true)` from `(true, false)`.
- **Reference.** `proofs/agda/EchoCharacteristic.visible`;
  `no-section-visible` shows the loss is genuine.

---

## 3. Quotient by equivalence

- **Source map.** `[_] : A → A/∼`, the quotient map modulo an
  equivalence relation `∼`.
- **What is lost.** Which specific representative of an equivalence
  class was taken.
- **What remains.** A specific representative, together with proof
  it lies in the given class.
- **Echo.** `Echo [_] c = Σ A (λ x → [x] ≡ c)` — inhabited by every
  representative, up to the quotient's induced proof structure.
- **Extensional / intensional.** Intensional is load-bearing: the
  shadow is the entire quotient, but the echo records the specific
  representative.
- **Reference.** `proofs/agda/EchoExamples.quot`;
  `collapse-residue-identifies` shows residue-level identification.

---

## 4. Cantor normal form as a canonical echo

- **Source map.** `normalize : OrdinalBelowε₀ → CNF`, mapping an
  arbitrary expression tree of ordinals below ε₀ to its unique
  Cantor normal form.
- **What is lost.** The specific expression tree (associativity,
  redundant zero-summands, non-descending summand orders).
- **What remains.** A canonical representative whose shape strictly
  determines the ordinal value.
- **Echo.** `Echo normalize cnf = Σ (tree : OrdinalBelowε₀) (normalize tree ≡ cnf)`.
- **Extensional / intensional.** Both. The shadow is "the canonical
  form exists"; the intensional core records *which tree* produced
  it, giving provenance across normalisation.
- **Reference.** `proofs/agda/Ordinal/CNF.agda`; trichotomy
  (`cnf-trichotomy`, `<ᶜ-trans`, `<ᶜ-irrefl`) gives the order
  structure that makes this a well-behaved canonicalisation.

---

## 5. Database GROUP BY

- **Source map.** `group_by_key : List Row → Map Key Row-Summary`.
  Each row contributes to a group keyed by some attribute; the
  summary (count, sum, max, …) aggregates the group.
- **What is lost.** Individual row identities within each group.
- **What remains.** Enough aggregate information to answer the
  summary query, plus (in a residue layer) references to the rows
  that contributed.
- **Echo.** For a given key `k` and summary `s`, the echo is the set
  of input row lists that would produce `s` under the aggregation.
  In an actual database with provenance annotations (K-provenance,
  `Bag`-semiring), the echo specialises to the semiring element.
- **Extensional / intensional.** Both. Shadow = set of (key,
  summary) pairs. Intensional = which rows contributed, with
  semiring-level provenance.
- **Informal.** Not yet formalised in Agda. The adjacency note
  `docs/adjacency/provenance-semirings.adoc` is the neighbour.

---

## 6. Lossy numerical truncation

- **Source map.** `truncate : ℝ → ℤ`, `truncate x = ⌊x⌋`.
- **What is lost.** The fractional part `x − ⌊x⌋ ∈ [0, 1)`.
- **What remains.** The integer value, plus — in an ε-echo refinement
  — a bound on how far from the truncation value the original `x`
  could have been.
- **Echo.** Exact: `Echo truncate n = Σ ℝ (λ x → ⌊x⌋ ≡ n)`.
  Approximate: `EchoR (ε = ½) ⌊·⌋ n ≈ Σ ℝ (λ x → |⌊x⌋ − n| ≤ ½)`.
- **Extensional / intensional.** Both. The approximate version
  brings in the "Exact vs approximate" axis (see taxonomy).
- **Informal.** Approximate-echo formalisation is open (see
  `taxonomy.md`, axis 2).

---

## 7. Ordinal collapse

- **Source map.** `collapse : BT → OmegaIndex`, collapsing a
  Buchholz term to its leading Ω-marker, as in
  `EchoOrdinal.ordinal-collapse`.
- **What is lost.** The full inner structure of the term (subterms,
  plus-decomposition, nested ψ-applications).
- **What remains.** The Ω-index marker — enough to place the term in
  a rough cardinal tier but nowhere near enough to reconstruct it.
- **Echo.** `Echo collapse ν = Σ BT (λ t → collapse t ≡ ν)`. Many
  distinct BT terms collapse to the same ν.
- **Extensional / intensional.** Intensional is crucial:
  `ordinal-collapse-non-injective` and
  `ordinal-echo-left≢ordinal-echo-right` distinguish two terms that
  share a collapse target.
- **Reference.** `proofs/agda/EchoOrdinal.agda`.

---

## 8. Cryptographic hash (mathematical preimage)

- **Source map.** `H : {0,1}* → {0,1}ⁿ`, a cryptographic hash.
- **What is lost.** Essentially everything — in the security model,
  preimages should be computationally inaccessible from the hash.
- **What remains.** Mathematically (not computationally), the full
  set of strings that hash to the observed output.
- **Echo.** `Echo H y = Σ {0,1}* (λ s → H s ≡ y)` — a mathematically
  enormous but enumerable (in principle) set.
- **Extensional / intensional.** Intensional at the set-theoretic
  level (every preimage exists), but the security claim is about
  *computational* access to the echo, not its existence. This
  distinction is not captured by the current `Echo f y` definition
  and is a genuine open question: what refinement of Echo Types
  encodes computational vs information-theoretic residue?
- **Informal.** Not in repo. Serves as the worked example for the
  **computational-access axis** that the current taxonomy does not
  yet include.

---

## 9. Parser error recovery

- **Source map.** `parse : List Token → Maybe SyntaxTree`. On malformed
  input the parser returns a best-effort tree with error markers.
- **What is lost.** Which specific token stream produced the (possibly
  error-bearing) tree; the erased parts of malformed input.
- **What remains.** The tree, plus error markers recording where the
  parser made recovery choices — this is an *explicit* residue in
  the return type, not merely implicit.
- **Echo.** `Echo parse tree = Σ (List Token) (λ ts → parse ts ≡ tree)`,
  but a more faithful version carries the recovery trace as part of
  the tree itself, making the echo split into a
  "canonical-tree" part and an "error-annotation" part.
- **Extensional / intensional.** Both. Shadow = set of reachable
  trees. Intensional = which token stream + what recovery choices.
- **Informal.** Not formalised. This is the example that forces the
  **presentation-dependent** axis (taxonomy, axis 4): the same tree
  can be reached from different token streams, and the echo
  distinguishes them.

---

## 10. Abstract interpretation (widening)

- **Source map.** `α : Values → AbstractValues`, a Galois-connection
  abstraction (e.g. `Int → Sign = {⊥, neg, zero, pos, ⊤}`).
- **What is lost.** The precise value — `α(5) = α(7) = pos`.
- **What remains.** The abstract class, plus (in any reasonable
  analyser) enough trace information to refine the abstraction in a
  re-analysis.
- **Echo.** `Echo α a = Σ Values (λ v → α v ≡ a)` is the concrete
  class over the abstract element `a`. Dually, the analyser's
  *widening* step introduces *approximate* echoes whose tolerance
  grows with analysis depth — tying example 6 and example 10
  together through axis 2 (exact vs approximate).
- **Extensional / intensional.** Both. The shadow is the abstract
  lattice; the intensional core is the concrete class structure.
- **Informal.** Not formalised; adjacent to `docs/adjacency/refinement-types.adoc`.

---

## Cross-cutting observations

1. **Shadow collapse is the same across cases.** Every example's
   "extensional shadow" is just `image(f)`. The shadow provides no
   structural discrimination between examples; all the discrimination
   lives in the intensional core.
2. **Presentation-dependent echoes cluster.** Examples 5, 9, 10
   share presentation-dependence. This suggests a sub-theory of
   "implementation-detail residue" distinct from the canonical
   fiber-based cases (examples 1–4).
3. **The computational-access question is live.** Example 8
   (cryptographic hash) cannot be captured by the fiber definition
   alone. It motivates adding a computational-access axis to the
   taxonomy.
4. **Approximate echoes appear twice.** Examples 6 and 10 both
   involve tolerance; both are open for formalisation. A single
   approximate-echo definition that serves both is a next theory
   step.
