<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Cross-Repo Bridge Status

Last updated: 2026-06-02.

This file is the single status ledger for echo-type bridge work that
touches other repositories.

## Tracks

| Track | echo-types side | Adjacent side | Current status | Main blocker |
|---|---|---|---|---|
| CNO bridge (Agda) | `proofs/agda/EchoCNOBridge.agda` | `absolute-zero/proofs/agda/CNO.agda` (direct import) | **Content-bridge done.** Bridge imports `IsCNO`, `empty-is-cno`, `halt-is-cno`, `cno-composition`, `absolute-zero-is-cno`, `seq-comp` from absolute-zero's `CNO.agda` and exhibits `cno-program-echo : (p : Program) → IsCNO p → ProgramEcho p` plus three concrete instances. `CNO.agda` builds clean under `--safe --without-K`, no postulates. | — (closed at content-bridge level; cross-prover theorem-statement alignment is the next row.) |
| CNO core theorem alignment | `EchoCNOBridge` theorem family | `absolute-zero/proofs/coq/common/CNO.v`, `absolute-zero/proofs/lean4/CNO.lean` | Name-by-name correspondence table drafted (see §"CNO Agda↔Coq↔Lean4 correspondence" below). | (1) Coq's `eval` is relational; Agda+Lean are functional. (2) Coq has no `absolute_zero` alias. (3) Coq's single-instruction CNO is `nop_is_cno`; Agda+Lean use `halt_is_cno`. (4) Coq carries 3 axioms (`eval_deterministic`, `eval_respects_state_eq_{left,right}`) that echo-types' `--safe --without-K` policy forbids — porting must re-route through a functional formulation, where they hold by `refl`. (5) `ProgramEcho`/`Echo` itself is currently unilateral (Agda-only). |
| JanusKey bridge | `proofs/agda/EchoJanusBridge.agda` | `januskey/src/abi/Types.idr` (`OpKind`, `IsFileOp`, `IsKeyOp`); `januskey/PROOF-NEEDS.md` | Name-bridge only — Agda side has a *local* 4-variant `JanusOp = Create \| Delete \| Modify \| Move`; canonical Idris2 ABI defines 8-variant `OpKind = Copy \| Move \| Delete \| Modify \| Obliterate \| KeyGen \| KeyRotate \| KeyRevoke` plus `IsFileOp`/`IsKeyOp` predicates. Already drifted (Create vs Copy; missing Obliterate + 3 key ops). | Decision recorded: structural-mirror the Agda enum to januskey's Idris2 `OpKind`; content-bridge deferred until januskey's `PROOF-NEEDS.md` lands content-bearing semantics. Agda↔Idris2 has no FFI, so any content-bridge must run via shared schema or trusted extraction. |
| Tropical alignment | `proofs/agda/EchoTropical.agda` | `tropical-resource-typing/Tropical.thy`, `tropical-resource-typing/TropicalSessionTypes.lean` (and 8 other `.thy` files) | Adjacent repo audit complete (2026-05-20). Repo present at `repos-monorepo/verification-ecosystem/tropical-resource-typing`; remote `hyperpolymath/tropical-resource-typing` active (last push 2026-05-18, language=Isabelle). First alignable theorem pair identified: Agda `⊕-idem` ↔ Isabelle `trop_add_idem` ↔ Lean `add_comm_trop`+`add_assoc_trop`. | Agda cannot import `.thy` or `.lean` directly; alignment is citation-level (statement correspondence with build-side independent proof per language), not import-level. Long-game target: `Tropical_Ordinal_Bridge.thy` ↔ echo-types ordinal track. |
| EchoTypes.jl executable mirror | Tier-1+Tier-2 spine + unconditional F5 OFS fragment (modules: `Echo`, `EchoResidue`, `EchoFiberCount`, `EchoThermodynamics`, plus 2026-05-27 v0.2.0 additions: `EchoTotalCompletion`, `EchoOrthogonalFactorizationSystem`, `EchoImageFactorization`, `EchoNoSectionGeneric`, `EchoLossTaxonomy`, `EchoEntropy`, `EchoObservationalEquivalence`) | [`hyperpolymath/EchoTypes.jl`](https://github.com/hyperpolymath/EchoTypes.jl) v0.2.0 (pinned to `e7dded6`); registered in `julia-professional-registry` | **Executable companion shipped.** Mirrors run the finite-domain shadow of the upstream theorems on concrete data and falsify-by-counterexample; the companion makes no proof claims, the Agda here remains the source of truth. R-2026-05-18 retraction surface NOT mirrored; F5 funext-qualified clauses (uniqueness up to iso, diagonal lifting) NOT mirrored — Julia has no funext, the claims would be vacuous. UIP- and truncation-strength upgrades likewise honestly not mirrored. | — (shipped; honest scope holds verbatim from upstream). Future advances on the Tier-1+Tier-2 spine are candidates for new shadows in subsequent EchoTypes.jl releases, but no in-repo CI dependency exists in either direction. |
| Ephapax L3 bridge (Agda↔Coq) | `proofs/agda/EchoEphapaxBridge.agda` | `ephapax/formal/Echo.v` (Coq, 584 lines, 24 `Qed`, zero `Admitted` / zero `Axiom`) — explicit port of `EchoLinear.agda` + `EchoResidue.agda` under a K-free / zero-axiom discipline equivalent to `--safe --without-K` | **Navigability bridge done; content bridge NARROW** (2026-05-30). Two definitional `refl`-renames: `ephapax-L3-weaken = EchoLinear.weaken` and `ephapax-L3-no-section-collapse = EchoResidue.no-section-collapse-to-residue`. Coq headlines `mode_le_prop`, `weaken_collapses_distinction`, `affine_canonical`, `degrade_mode_comp`, `no_section_collapse_to_residue` (line 502-517) each match an Agda counterpart pinned in `Smoke.agda`. Scope: **L3 only** — ephapax-affine has Rust checkers only; L1 has 5 `Axiom` + 11 `Admitted`; L4 has no mechanised theorems yet (cf. ephapax `formal/PRESERVATION-DESIGN.md`, `docs/echo-types/paper.adoc` §"Threats to validity"). | Per-bridge docs `docs/bridges/ECHO-EPHAPAX-BRIDGE.adoc` (CNO-equivalent) not yet authored; tracked as follow-up issue. Full content bridge (round-trip CI between Agda + Coq) would require an Agda mirror of ephapax `formal/Echo.v` and is **not foreclosed** by the NARROW stub. |
| Valence Shell / Ochránce accountable-shell bridge (exploratory, downstream) | Structured-loss vocabulary only — `EchoResidue` / `EchoResidueTaxonomy` / `EchoLossTaxonomy` / `EchoObservationalEquivalence` / `EchoNoSectionGeneric` cited at the reading-aid level. **No bridge module**; nothing added to `All.agda`, `Smoke.agda`, or `EchoCanonicalIdentitySuite.agda`. | Valence Shell (`hyperpolymath/valence-shell`) — shell state transitions, undo/redo, checkpoints, diff/replay. Ochránce (`hyperpolymath/ochrance`) — A2ML manifests, Merkle state commitments, repair/attestation surfaces. | **Exploratory — candidate downstream consumer. Core Affect: NO.** Echo Types' structured-loss semantics may *classify* shell state transitions by residue / loss form (recoverable / constrained / residue-bearing / observationally equivalent / genuinely lost); Ochránce may supply concrete receipt evidence. Downstream application evidence only — not a new foundation. No mechanised cross-repo theorem currently exists. Companion: `docs/bridge-status.md` §7 and `docs/echo-types/explorations/accountable-shell/README.adoc`. | No shared schema and no Agda↔Idris2 / Agda↔Rust import path; the relationship is citation-level only. Echo Types makes **no** claim about Valence Shell / Ochránce implementation correctness, and **no** claim about POSIX, Rust, the Lean→Rust correspondence, secure deletion, GDPR, cryptographic integrity, or attestation. Valence Shell's RMR/RMO vocabulary, if referenced, is downstream application vocabulary and is not adopted into the Echo Types core. |

## Immediate next actions

1. **JanusKey** — rewrite `EchoJanusBridge.JanusOp` from the 4-variant local enum to mirror the 8-variant Idris2 `OpKind` (Copy/Move/Delete/Modify/Obliterate/KeyGen/KeyRotate/KeyRevoke); add `IsFileOp`/`IsKeyOp` predicate analogues. Keep bridge theorems trivial (each `JanusEcho op` continues to inhabit `Echo janus-to-unit tt`). Re-pin in `Smoke.agda`.
2. **Tropical** — extend this status doc with a name-by-name correspondence appendix (Agda `⊕-idem`, `score-⊕-idem`, `tropical-non-injective`, `echo0-to-tropical`, `distinct-candidates-same-visible-distinct-echo` ↔ counterpart names in `Tropical.thy` / `TropicalSessionTypes.lean`).
3. **CNO theorem alignment** — promote the correspondence table below into a separate cross-prover alignment doc once a Coq-side or Lean-side `Echo` analog is introduced (currently Agda-unilateral).
4. **JanusKey content-bridge** — gated on the adjacent repo's `PROOF-NEEDS.md` closing. No echo-types action until then.

## CNO Agda↔Coq↔Lean4 correspondence

The table maps the Agda surface consumed by `EchoCNOBridge.agda` plus
the bridge's own headlines onto the sibling Coq and Lean4 statements.
Where there is no analog the cell is `—`; where the analog exists but
the statement diverges, the cell is `DIVERGES: <reason>`.

| Agda (`CNO.agda` / `EchoCNOBridge.agda`) | Coq (`proofs/coq/common/CNO.v`) | Lean4 (`proofs/lean4/CNO.lean`) | Notes |
|---|---|---|---|
| `Program` (CNO.agda L100–101) | `Program` (L84) | `Program` (L90, `abbrev`) | Match. All three = `List Instruction`. |
| `Instruction` (L91–97) | `Instruction` (L74–80) | `Instruction` (L78–85) | Match. Same 6 constructors; only constructor ordering differs (`Halt` last in Coq/Lean, second in Agda). |
| `IsCNO` (record, L214–219) | `is_CNO` (Definition, L204–208) | `isCNO` (`def`, L195–199) | Match in intent (4-clause conjunction). DIVERGES (mild): Agda = `record` with named fields; Coq/Lean = nested `∧`. Identity clause also DIVERGES (mild): Agda `eval p s ≡ s` up to `state-eq`; Coq quantifies over `s'` with `eval p s s'` (relational `eval`); Lean `eval p s = s` up to `ProgramState.eq` (functional `eval`). |
| `empty-is-cno` (L226–232) | `empty_is_cno` (L383–407) | `empty_is_cno` (L204–217) | Match. Proof shapes diverge per `eval` style. |
| `halt-is-cno` (L247–253) | — (only `nop_is_cno`, L412–440) | `halt_is_cno` (L235–251) | DIVERGES: Coq ships `nop_is_cno` instead. Agda picks Halt because Nop bumps PC (so isn't identity-on-state in the Agda model). |
| `cno-composition` (L312–330) | `cno_composition` (L338–378) | `cno_composition` (L329–356) | Match. `IsCNO p1 → IsCNO p2 → IsCNO (seq_comp p1 p2)`. |
| `seq-comp` (L280–281) | `seq_comp` (L247) | `seqComp` (`abbrev`, L282) | Match. All three = `p1 ++ p2`. |
| `absolute-zero` (L359–360) | — | `absoluteZero` (`def`, L530) | DIVERGES: Coq has no `absolute_zero` alias; one must use `[]` directly. Agda+Lean both alias `[]`. |
| `absolute-zero-is-cno` (L363–364) | — (expressed as `empty_is_cno`) | `absoluteZero_is_cno` (L533) | Lean matches Agda (`= empty_is_cno`); Coq has no analog. |
| `cno-program-echo` (bridge, L76–77) | — | — | Bridge-only headline. No Coq/Lean analog (no `Echo` type, no `ProgramEcho` fibre, no `echo-intro`). |
| `empty-cno-echo` / `halt-cno-echo` / `absolute-zero-echo` / `cno-compose-echo` (bridge) | — | — | Bridge instances; no analog. |
| `ProgramEcho` / `program-to-unit` (bridge) | — | — | Bridge type + collapse map; defined only Agda-side. |
| `cno-preserves-state` / `cno-terminates-thm` / `cno-pure-thm` / `cno-thermo-rev` (L260–273) | `cno_terminates`, `cno_preserves_state`, `cno_pure`, `cno_reversible` (L213–242) | `cno_terminates`, `cno_preserves_state`, `cno_pure`, `cno_reversible` (L256–273) | Match (not consumed by bridge; included for completeness). |
| — | `eval_deterministic`, `cno_equiv*`, `eval_respects_state_eq_{left,right}` (Axioms + theorems, L444–626) | — | DIVERGES: Coq introduces equivalence theory + 3 axioms not present in Agda or Lean. `--safe --without-K` forbids axioms — a Coq→Agda port must either re-prove these (impossible without altering the model) or re-route through the functional `eval` formulation, where they hold by `refl`. |

### Structural alignment blocker

The deepest cross-prover blocker is the **`eval` model mismatch**:

- Agda — total function `Program → ProgramState → ProgramState`; `IsCNO` quantifies as `state-eq (eval p s) s`.
- Lean4 — total function (same shape; `ProgramState.eq (eval p s) s` ports cleanly from Agda).
- Coq — `Prop`-valued inductive relation `eval : Program → ProgramState → ProgramState → Prop`; `is_CNO` quantifies as `forall s s', eval p s s' -> s =st= s'`.

Bridging the relational/functional split needs either (a) a
`Functional.eval` reformulation on the Coq side plus a soundness lemma
against the inductive `eval`, or (b) re-stating `cno-program-echo` in
Coq as `forall p (H : is_CNO p) s s', eval p s s' -> ProgramEcho p`,
which changes the headline's logical shape. The 3 Coq axioms exist
precisely to paper over this in the relational model.

## Revision history

- 2026-06-02: Added the Valence Shell / Ochránce accountable-shell
  bridge row as an exploratory downstream-consumer entry (Core Affect:
  NO; citation-level only, no bridge module, nothing wired into
  `All.agda` / `Smoke.agda` / `EchoCanonicalIdentitySuite.agda`).
  Mirrored in `docs/bridge-status.md` §7 and the exploratory note
  `docs/echo-types/explorations/accountable-shell/README.adoc`.
- 2026-05-20: Closed CNO content-bridge row; baked Agda↔Coq↔Lean4
  correspondence table in; updated JanusKey row with the
  structural-mirror decision and the 4-vs-8 enum drift; closed the
  Tropical "not recently audited" blocker after locating the active
  adjacent repo. Removed references to the superseded
  `EchoBridgeScaffold.agda` adapter slot.
- 2026-04-23: Initial ledger.
