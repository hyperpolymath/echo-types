<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# Fidelity — open postulates (trust boundaries)

Companion to `proofs/agda/Ordinal/Buchholz/Fidelity.agda`. Open problem
**`D-2026-06-14`** (`docs/echo-types/decisions/ordinal-bh-order-type-fidelity-open.adoc`).

## Plain-language summary

**What is now mechanised.** Only the *shape* of the order-type
fidelity claim, plus one genuinely-proved structural fact:

- The **theorem shape** is typed and auditable: `Fidelity.agda` states
  "the sound carrier `_<ᵇ²_` (on well-formed terms `WfBT`) has order
  type ψ₀(Ω_ω)" as a cofinal order-embedding into a Bachmann–Howard
  structure (`OrderTypeBH`, assembled in `fidelity`). The statement is
  quantified over the **sound carrier only** — never native `_<ᵇ_`.
- The **lower-bound half** (`fidelity-lower`) is a real term *given the
  postulated denotation*: the BH height is attained by the well-formed
  carrier term `BH = ψ₀(Ω_ω)` itself (it plumbs `BH`, `BH-wf`, and the
  denotation's `pins-BH` field — no postulate of its own).
- The **grammar-level upper shadow** (`marker-≤ω`, `markers-≤ω`) is
  proved **for real, postulate-free**: every Ω-marker in any Buchholz
  term is `≤Ω ω` (the carrier lives in the ν ≤ ω fragment; the notation
  never names a marker above Ω_ω). This is the structural precondition
  of the upper bound, *not* the upper bound itself.

**What remains genuinely open.** The two pieces of real content — the
**order-reflecting, height-preserving denotation** `⟦·⟧` and its
**cofinality** — are postulated, together with the existence of a
checked Bachmann–Howard target structure. These are the missing
*objects*, not missing *plumbing*.

**Explicit non-claim.** *Nothing in this module asserts that order type
ψ₀(Ω_ω) is proven.* `fidelity` is only as strong as the three
postulates below; with them open, it asserts the **shape** of fidelity,
not fidelity. `rank2` (the height-collapsing termination measure) is
**not** reused, extended, or tightened toward this claim — fidelity
needs the separate, height-preserving `⟦·⟧`. The status surfaces
(appendix, decision log, roadmap) continue to read **"written at WF
milestone; order-type fidelity OPEN"** and were *not* edited by this
commit.

## The postulates (complete list — `grep postulate Fidelity.agda`)

| # | Name | Statement (in words) | What closes it | Owner |
|---|------|----------------------|----------------|-------|
| 1 | `bh-notation : BHNotation` | A checked well-founded strict order `(𝒪, _<𝒪_)` with a distinguished element `bh-height` whose initial segment is the Bachmann–Howard ordinal ψ₀(Ω_ω). | Construct (or import) a verified Bachmann–Howard ordinal structure in Agda — e.g. a checked ordinal-notation library, or a Cantor/Veblen normal-form development carried to ψ₀(Ω_ω). | **External mathematics** (owner / external) |
| 2 | `denotation : DenotesBH bh-notation` | A denotation `⟦·⟧ : BT → 𝒪` that is **order-preserving** (`s <ᵇ² t → ⟦s⟧ <𝒪 ⟦t⟧`), **order-reflecting** (`⟦s⟧ <𝒪 ⟦t⟧ → s <ᵇ² t`), **cofinal** (image unbounded in `𝒪`), and **pins BH** (`⟦BH⟧ ≡ bh-height`). The height-preserving embedding `rank2` is *not*. | Define `⟦·⟧` mapping each ψ_ν / Ω_ν / + to its genuine ordinal height (not the collapsed ω-power blocks of `rank2`) and prove the four fields. This is the core order-type-correctness work (a denotational semantics for the notation faithful to `_<ᵇ²_`). | **External mathematics** (owner / external); the design route is option (a) in `D-2026-06-14`. |
| 3 | `ordinal-upper-bound : ∀ {t} → WfBT t → ¬ (bh-height <𝒪 ⟦ t ⟧)` | No well-formed carrier term denotes strictly above the BH height (the ⟦·⟧-level upper half of the sandwich). | Cheap *given* postulate #2: combine the real `markers-≤ω` (every marker `≤Ω ω`) with a height calculation through the real `⟦·⟧` (markers `≤ ω` ⇒ denotation `≤ ψ₀(Ω_ω)`). It is postulated only because it quantifies over the not-yet-real `⟦·⟧`; it is **not** independent external mathematics beyond #2. | Discharged alongside / just after #2 (in-repo, once `⟦·⟧` is real). |

## Discharge order

`bh-notation` (#1) and `denotation` (#2) are the genuine external
content and are independent of each other only up to #2 referencing
#1's `𝒪`. `ordinal-upper-bound` (#3) is downstream of #2 and in-repo
once #2 lands. When all three are real, `fidelity : OrderTypeBH`
becomes an unconditional theorem and a **human** may then update the
appendix / decision-log / roadmap from "OPEN" to discharged — per the
hard rule, this commit does not pre-empt that sign-off.
