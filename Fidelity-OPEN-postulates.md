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
- The **target structure** `(𝒪, _<𝒪_, wf-<𝒪)` is now **real,
  postulate-free** (2026-06-15): `Ordinal.Buchholz.BHTarget` constructs
  it from the Brouwer order (`Ord` / `_<′_` / `wf-<′`) via
  `bh-notation-from`, inside the `--safe` kernel (wired into `All.agda`,
  pinned in `Ordinal/Buchholz/Smoke.agda`). Only the candidate BH
  *height* remains a free input — an explicit `Fidelity.AtHeight`
  module parameter.

**What remains genuinely open.** The two pieces of real content — the
**order-reflecting, height-preserving denotation** `⟦·⟧` and its
**cofinality** — are postulated. (The checked Bachmann–Howard target
*structure* is no longer assumed — see the last bullet above.) These are
the missing *objects*, not missing *plumbing*.

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

As of 2026-06-15 there are **two** (reduced from three). The former
`bh-notation` postulate is **discharged**: the target structure is now
constructed for real in the `--safe` module `Ordinal.Buchholz.BHTarget`
(`bh-notation-from` over the Brouwer order `Ord` / `_<′_` / `wf-<′`), and
the candidate BH height is an explicit `Fidelity.AtHeight` module
parameter rather than an axiom.

| # | Name | Statement (in words) | What closes it | Owner |
|---|------|----------------------|----------------|-------|
| 1 | `denotation : DenotesBH bh-notation` | A denotation `⟦·⟧ : BT → 𝒪` (with `𝒪 = Ord`, `_<𝒪_ = _<′_`) that is **order-preserving** (`s <ᵇ² t → ⟦s⟧ <′ ⟦t⟧`), **order-reflecting** (`⟦s⟧ <′ ⟦t⟧ → s <ᵇ² t`), **cofinal** (image unbounded in `Ord`), and **pins BH** (`⟦BH⟧ ≡ bh-height`). The height-preserving embedding `rank2` is *not*. | Define `⟦·⟧` mapping each ψ_ν / Ω_ν / + to its genuine ordinal height (not the collapsed ω-power blocks of `rank2`) and prove the four fields. This is the core order-type-correctness work (a denotational semantics for the notation faithful to `_<ᵇ²_`). | **External mathematics** (owner / external); the design route is option (a) in `D-2026-06-14`. |
| 2 | `ordinal-upper-bound : ∀ {t} → WfBT t → ¬ (bh-height <𝒪 ⟦ t ⟧)` | No well-formed carrier term denotes strictly above the BH height (the ⟦·⟧-level upper half of the sandwich). | Cheap *given* postulate #1: combine the real `markers-≤ω` (every marker `≤Ω ω`) with a height calculation through the real `⟦·⟧` (markers `≤ ω` ⇒ denotation `≤ ψ₀(Ω_ω)`). It is postulated only because it quantifies over the not-yet-real `⟦·⟧`; it is **not** independent external mathematics beyond #1. | Discharged alongside / just after #1 (in-repo, once `⟦·⟧` is real). |

## Discharge order

`denotation` (#1) is the genuine external content — the faithful
height-preserving embedding into the now-real Brouwer target.
`ordinal-upper-bound` (#2) is downstream of #1 and in-repo once #1
lands. When both are real, `fidelity : OrderTypeBH` becomes an
unconditional theorem (for the supplied `AtHeight` height) and a
**human** may then update the appendix / decision-log / roadmap from
"OPEN" to discharged — per the hard rule, this commit does not pre-empt
that sign-off.
