<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Tropical Correspondence (echo-types ↔ tropical-resource-typing)

Last updated: 2026-05-20

This appendix records the citation-level correspondence between
`proofs/agda/EchoTropical.agda` in this repo and the adjacent
`hyperpolymath/tropical-resource-typing` repo (Isabelle + Lean4). The
alignment is **statement-level only**: there is no FFI surface between
Agda and Isabelle/Lean, no shared definition module, and no cross-prover
extraction pipeline. Each side carries its own independent proof of the
named theorems; this document is a cross-reference that lets a reader
verify "the same fact is established in all three systems," but does
not constitute a unified verification artefact. It closes the
"Adjacent repo not recently audited" blocker noted in
`cross-repo-bridge-status.md`.

## Source files

- **Agda (this repo).** `proofs/agda/EchoTropical.agda` — the
  Tropical-Echo bridge (E10): max-plus semiring on `ℕ` plus the
  echo-retention bridge theorems.
- **Isabelle.**
  `tropical-resource-typing/Tropical.thy` — max-plus tropical semiring
  over the lifted carrier `ℕ ∪ {-∞}`, wired into Isabelle's
  `comm_semiring_1` typeclass hierarchy, with idempotence proved
  separately (the structure is a dioid, not a ring).
- **Lean4.**
  `tropical-resource-typing/TropicalSessionTypes.lean` — max-plus
  tropical semiring on the lifted carrier `Nat ∪ {bot}`, used to grade
  session types so that speculative parallel cost is the bottleneck
  (`max`) rather than the sequential sum.
- **Canonical adjacent remote.** `hyperpolymath/tropical-resource-typing`
  (active; primary language Isabelle; the `.thy` files were last
  touched in the `Tropical_Semirings` close sweep, with subsequent CI
  hardening commits on top).
- **Local clone for this audit.**
  `/home/hyperpolymath/dev/repos/repos-monorepo/verification-ecosystem/tropical-resource-typing`.

## Name-by-name correspondence

| Agda (`EchoTropical.agda`) | Isabelle (`Tropical.thy`) | Lean4 (`TropicalSessionTypes.lean`) | Notes |
|---|---|---|---|
| `_⊕_` (max-plus add on `ℕ`, line 23) | `trop_add` (function, line 41) | `tAdd` (function, line 96) | Same operation (max with identity element absorbed at the left). DIVERGES (carrier): Agda's `_⊕_` operates on raw `ℕ` with `zero` acting as the additive identity by the recursion shape; Isabelle's `trop_add` and Lean's `tAdd` both operate on a *lifted* carrier (`tropical = Fin nat \| NegInf` / `Tropical = .val Nat \| .bot`) where the additive identity is the bottom element `−∞`, not `0`. The `ℕ` quotient on the Agda side is intentional (the bridge only needs scores in `ℕ`) but means Agda's `_⊕_` is the restriction of the Isabelle/Lean operation to the finite sub-semiring; the algebraic laws below match on that restriction. |
| `⊕-idem` (line 30) | `trop_add_idem [simp]` (lemma, line 73) | — | Match (Agda ↔ Isabelle): Agda `⊕-idem : ∀ m → m ⊕ m ≡ m` ↔ Isabelle `trop_add_idem : trop_add a a = a`. The Isabelle file also restates this at typeclass level as `tropical_add_idem` (theorem, line 266: `(a :: tropical) + a = a`); the bare-function lemma is the closer match. Lean side has NO named idempotence theorem — the file ships 13 CommSemiring laws (commut/assoc/identity/distrib) but not `tAdd a a = a`. The Lean docstring explicitly flags this gap: `tropical_grade_le_sequentialTotal` is offered as the "Lean analogue of Isabelle `tropical_add_idem`" because `max a b ≤ a + b` is what `add_idem` buys in a dioid. So the Lean cell is `—` for the bare law and `tropical_grade_le_sequentialTotal` for the downstream consumer. |
| `score-⊕-idem` (line 82) | — | — | Unilateral (Agda-only). The Agda side specialises `⊕-idem` to scores of the 3-candidate set; the adjacent repo has no `Candidate` type and no `score` function, so the specialisation has no analog. |
| `tropical-non-injective` (line 55) | — | — | Unilateral (Agda-only). Headline of the echo-retention bridge: there exist distinct candidates with the same tropical score. The adjacent repo does not type candidates (its tropical semiring is generic), so there is nothing to be non-injective about. |
| `tropical-collapse-visible` (line 121) | — | — | Unilateral (Agda-only). `score a ≡ score b` for the concrete 3-candidate choice; no analog. |
| `Echo` / `echo-intro` / `TropEcho` / `IsArgmin` (lines 59–73) | — | — | Unilateral (Agda-only). The echo type itself (`Echo f y := Σ A (λ x → f x ≡ y)`) is an echo-types invention; the adjacent repo has no fibre type and no echo bridge. |
| `echo0-to-tropical` (line 113) | — | — | Unilateral (Agda-only). Bridge map echo → tropical residue; no analog (no echo on the other side). |
| `distinct-candidates-same-visible-distinct-echo` (line 130) | — | — | Unilateral (Agda-only). The main bridge theorem: collapse on the visible (tropical) side, retention on the echo side. No analog. |
| `tropical-echo-retention-simple` (line 135) | — | — | Unilateral (Agda-only). Simplified restatement of the headline bridge. |
| (no Agda analog) | `trop_mul` (function, line 46) | `tMul` (function, line 103) | DIVERGES: the adjacent repo carries a full semiring (add + mul), the Agda side does not. The Agda bridge needs only the additive (max) structure of the dioid; multiplicative tropical structure is out of scope for the echo bridge as it currently stands. |
| (no Agda analog) | `trop_add_comm` (line 65) | `add_comm_trop` (line 114) | Adjacent-side commutativity. Match between Isabelle and Lean. No Agda analog by design — `_⊕_` on `ℕ` is commutative but the lemma is not stated because the bridge headlines do not consume it. |
| (no Agda analog) | `trop_add_assoc` (line 69) | `add_assoc_trop` (line 117) | Adjacent-side associativity. Match between Isabelle and Lean. No Agda analog by design (same reason as commutativity). |
| (no Agda analog) | `trop_distrib_{left,right}` (lines 122/126); semiring instance | `left_distrib_trop` / `right_distrib_trop` (lines 167/173); `CommSemiring Tropical` instance (line 208) | Adjacent-side distributivity + semiring typeclass wiring. Match between Isabelle and Lean. Out of scope for the echo bridge. |

## Alignment caveats

- **No Agda↔Isabelle/Lean import surface.** Agda cannot `import` a
  `.thy` or a `.lean`; Isabelle and Lean4 cannot `import` an `.agda`.
  Any "alignment" between these files is therefore citation-level only
  — a reader verifies the names and statements line up, but each
  prover runs its own independent proof. None of the three is a
  trusted oracle for either of the others.
- **Independent proofs, identical claims.** The first alignable
  theorem pair is `⊕-idem` (Agda) ↔ `trop_add_idem` (Isabelle). Both
  are proved (clean, no axioms, no `sorry`); the Agda side under
  `--safe --without-K`, the Isabelle side as a `simp` lemma against
  the algebraic kernel of `Tropical.thy`. The Lean side does not name
  this fact directly but consumes it inside the QTT refinement
  theorem `tropical_grade_le_sequentialTotal` (`max a b ≤ a + b` is
  the dioid consequence of additive idempotence).
- **Carrier mismatch is intentional, not a defect.** Agda's `_⊕_`
  lives on `ℕ` (the score type); Isabelle/Lean live on the lifted
  carrier with an explicit `−∞` bottom. The Agda side never needs
  `−∞` because every candidate has a finite score; the bridge is
  consciously narrower than the full max-plus semiring.
- **Echo-side machinery is Agda-exclusive.** The `Echo`/`TropEcho`
  fibre type, `IsArgmin`, the candidate datatype, and all bridge
  headlines (`tropical-non-injective`, `echo0-to-tropical`,
  `distinct-candidates-same-visible-distinct-echo`) have no analog
  on the Isabelle or Lean sides. The adjacent repo's tropical
  semiring stands on its own and is consumed by *session-type
  grading* (`grade : Session → Tropical` in Lean), which is the
  symmetric Agda-exclusive direction.
- **Long-game alignment target.** When the echo-types ordinal track
  reaches Bachmann–Howard (ψ₀(Ω_ω); see `roadmap.adoc` §Lane 3 and
  `docs/buchholz-plan.adoc`), the adjacent repo's
  `Tropical_Ordinal_Bridge.thy` becomes the natural cross-repo
  alignment target (Agda Buchholz BT ↔ Isabelle `tropO` carrier).
  This target is **firewalled** until the ordinal track lands the
  milestone — do not pull it forward.

## Revision history

- 2026-05-20: created (initial citation-level correspondence).
