;;; ============================================================
;;; META.scm — echo-types architecture decisions from EI-2
;;; ============================================================
;;;
;;; Format: meta-a2ml (S-expression, SRFI-30 conventions)
;;; Schema reference:
;;;   github.com/hyperpolymath/standards/blob/main/meta-a2ml/spec/abnf/meta.abnf
;;;
;;; SPDX-License-Identifier: PMPL-1.0-or-later
;;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

(define-module (echo-types meta)
  #:export (architecture-decisions
            development-practices
            design-rationale))

;;; ============================================================
;;; Architecture Decision Records
;;; ============================================================

(define architecture-decisions
  '((adr-001
     (title . "Distinctness load rests on truncation + 2-cell arguments")
     (status . accepted)
     (date . "2026-04-29")
     (context . "EI-2 investigation across seven data points found the integration recipe does not carry substantive simultaneous cross-axis content. The non-loss-only criterion is necessary but not sufficient; even Choreo × Choreo (the only available NLO self-pairing) degenerates to coordinate-product commutation.")
     (decision . "Gate-1's distinctness claim narrows: the recipe is organising vocabulary; the load-bearing distinctness arguments are (1) truncation (echo-not-prop family) and (2) 2-cell (Σ-over-preimages-shaped natural 2-cells in neighbour frameworks).")
     (consequences . "Five-document cascade: gate-1, gate-2-handoff, roadmap-gates, adjacency README, top-level README. Recipe extension parked for v0.2+.")
     (supersedes . none))

    (adr-002
     (title . "Drop READING 2 as the EI-2 closure framing")
     (status . accepted)
     (date . "2026-04-29")
     (context . "Two candidate readings for EI-2 closure were drafted (READING 1: weaken gate-1; READING 2: NLO-as-recipe-precondition). The prior session's RoleRole.agda finding established that NLO is necessary but not sufficient, refuting READING 2 as drafted.")
     (decision . "Adopt the stronger-negative reading: distinctness rerouted to truncation + 2-cell, recipe explicitly removed from distinctness load. Both originally-drafted reading patches are kept as historical record with SUPERSEDED banners.")
     (consequences . "EI-2 terminates negatively via PATH B (partial formalisation accepted as sufficient). Three legacy doc files are SUPERSEDED-banner'd, not deleted.")
     (supersedes . none))

    (adr-003
     (title . "Accept partial formalisation (PATH B) for EI-2 closure")
     (status . accepted)
     (date . "2026-04-29")
     (context . "The full 2D iff theorem (recipe-non-triviality ↔ NLO criterion) is not formalisable in safe Agda without postulates: decidable equality on decoration types, F-collapses axioms, extensionality on cell actions.")
     (decision . "Accept the per-axis halves (proved in RecipeTheorem.agda) plus the concrete construction halves (proved in RecipeNonTriviality.agda) plus the seven empirical data points as sufficient evidence for termination. Document the formal generic theorem as future work, not as a blocker for EI-2 closure.")
     (consequences . "EI-2 closes; the recipe-non-triviality theorem in its full generic form is parked. Gate-1's distinctness narrowing does not depend on the parked theorem since the negative finding removes the recipe from the distinctness load entirely.")
     (supersedes . none))

    (adr-004
     (title . "Recipe extension scope: v0.2+, not v0.1.x")
     (status . accepted)
     (date . "2026-04-29")
     (context . "The positive-termination route from EI-2 — extending the recipe to allow coupled state across axes or multiple live positions per axis — is conceptually distinct from the EI-2 question (does the existing recipe with the existing five axes carry substantive content?).")
     (decision . "Park recipe extension as a separate v0.2+ work item. Do not file it as an EI-2 reopening or as unfinished EI-2 business. When v0.2 work begins, file as a new question (e.g., EI-3).")
     (consequences . "EI-2 stays terminated. Future investigators cannot reopen it under the framing 'EI-2 wasn't really finished, the recipe just needs extending'.")
     (supersedes . none))

    (adr-005
     (title . "Forge workflow: GitHub canonical, mirror outward")
     (status . accepted)
     (date . "2026-04-28")
     (context . "User has a static stylistic preference for GitLab > GitHub but the actual git workflow has GitHub as canonical with hub-and-spoke mirroring outward. The static preference does not apply to git operations specifically.")
     (decision . "echo-types canonical at github.com/hyperpolymath/echo-types; mirror to GitLab and Codeberg via .github/workflows/mirror.yml. Tokens configured per MIRROR_SETUP.adoc; missing-token cases silently skip rather than fail.")
     (consequences . "Hub-and-spoke pattern; PRs and Issues live on GitHub; mirrors are read-only.")
     (supersedes . none))

    (adr-006
     (title . "Cross-platform builds: Linux primary, Windows secondary")
     (status . accepted)
     (date . "2026-04-28")
     (context . "User works across two machines: Fedora Kinoite (primary, Nushell) and a Windows machine for travel.")
     (decision . "Build instructions are path-agnostic; line endings normalised via .gitattributes (LF for Agda/AsciiDoc/YAML, .agdai marked binary). Cross-platform considerations apply throughout.")
     (consequences . "Path-agnostic build instructions are required, not optional, for any new tooling.")
     (supersedes . none))))

;;; ============================================================
;;; Development practices (relevant subset)
;;; ============================================================

(define development-practices
  '((code-style
     (agda . "--safe --without-K mandatory; no postulates")
     (asciidoc . "narrow-true claims preferred over broader-easy; honest qualification visible in source")
     (commit-messages . "structured per INTEGRATION_COMMITS.adoc; include rationale in body, not just title"))

    (versioning
     (scheme . "SemVer 2.0.0")
     (current-target . "0.1.1")
     (recipe-extension-target . "0.2.0+"))

    (review
     (gate-pattern . "three identity gates with explicit retraction conditions per gate")
     (lane-discipline . "gate-1, gate-2, gate-3 work in parallel lanes; integration via cross-lane audit")
     (falsifier-format . "explicit FALSIFIER callouts in AsciiDoc + comment block above corresponding Agda definition"))

    (documentation
     (cascade-discipline . "narrowings to gate-1's claim must propagate to all five canonical doc locations: gate-1-distinct-phenomenon, gate-2-handoff, roadmap-gates, adjacency README, top README")
     (do-not-redo . "STATE.scm tracks terminated questions and forbidden rebrandings; consult before starting any investigation framed as a follow-up to a closed question"))

    (versioning-of-decisions
     (status-values . "proposed / accepted / deprecated / superseded / rejected")
     (supersedes-pattern . "when an ADR replaces another, mark the old one with status=superseded and (superseded-by . <new-id>); never delete"))))

;;; ============================================================
;;; Design rationale
;;; ============================================================

(define design-rationale
  '((why-narrower-true
     "Gate-1's original framing (five axes simultaneously) was overstrong. The honest narrower-true claim — distinctness rests on truncation + 2-cell — is provably correct, formally certified, and removes the integration recipe from a load it cannot bear. Narrowing claims toward what the formalisation actually shows, rather than maintaining ambition the formalisation does not support, is the project's standing epistemic posture.")

    (why-path-b
     "Full formalisation of the recipe-non-triviality theorem requires postulates that --safe Agda forbids. PATH B (partial formalisation accepted as sufficient given empirical + structural evidence) is the honest closure: per-axis halves are proved, concrete construction halves are proved, the generic 2D iff is documented as out of safe-Agda scope. The negative gate-1 finding does not depend on the generic theorem.")

    (why-keep-superseded-readings
     "The two reading-decision documents (READING 1 and READING 2) plus their comparison are kept with SUPERSEDED banners rather than deleted. They record the alternatives that were considered, which prevents future investigators from re-deriving them from scratch under different names. This is the canonical anti-duplicate-work pattern for this codebase.")

    (why-recipe-stays-as-vocabulary
     "Even though the recipe doesn't carry distinctness, it still organises the per-axis lemma family (composition, join, propositionality of order) and provides a uniform shape for stating per-axis transport actions. Removing it from the codebase would lose useful organisation. Keeping it as 'organising vocabulary, not locus of distinctness' is the right framing.")

    (why-state-not-ad-hoc-handover
     "Earlier sessions used ad-hoc handover documents (text files, conversation summaries). This session captures the termination in state-a2ml STATE.scm form so it is machine-readable, schema-validated against standards/state-a2ml/spec/abnf/state.abnf, and joins the ecosystem of *-a2ml documents the user maintains. Future Claude sessions can parse and consult it programmatically.")))

;;; ============================================================
;;; END OF META
;;; ============================================================
