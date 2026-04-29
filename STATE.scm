;;; ============================================================
;;; STATE.scm — echo-types EI-2 termination capture
;;; ============================================================
;;;
;;; Format: state-a2ml (S-expression, SRFI-30 conventions)
;;; Schema reference:
;;;   github.com/hyperpolymath/standards/blob/main/state-a2ml/spec/abnf/state.abnf
;;; Sibling reference (cached pattern):
;;;   github.com/hyperpolymath/standards/blob/main/meta-a2ml/spec/abnf/meta.abnf
;;;
;;; Purpose: prevent EI-2 from being re-investigated. The investigation
;;; concluded; the verdict is negative; the documentation cascade has been
;;; applied; the recipe is no longer a candidate locus of distinctness.
;;;
;;; SPDX-License-Identifier: PMPL-1.0-or-later
;;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

(define-module (echo-types ei-2 state)
  #:export (project
            session
            terminated-questions
            standing-decisions
            artefacts
            cascade-applied
            do-not-redo
            next-actions
            forbidden-rebrandings))

;;; ============================================================
;;; Project identity
;;; ============================================================

(define project
  '((name           . "echo-types")
    (repository     . "github.com/hyperpolymath/echo-types")
    (canonical-host . github)                ; per current forge workflow
    (mirrors        . (gitlab codeberg))
    (version-target . "0.1.1")
    (license        . "PMPL-1.0-or-later")))

;;; ============================================================
;;; Session header
;;; ============================================================

(define session
  '((investigation-id   . "EI-2")
    (investigation-name . "Robustness of the integration recipe under richer 2D combinations")
    (opened             . "2026-04-28")
    (closed             . "2026-04-29")
    (verdict            . negative)
    (route              . path-b)
    (closing-rationale  . "Empirical evidence (7 data points) and structural argument (RoleRole.agda) overwhelming; full 2D iff theorem documented as not formalisable in safe Agda without postulates; per-axis halves and concrete construction halves proved.")))

;;; ============================================================
;;; Terminated questions (do not reopen)
;;; ============================================================

(define terminated-questions
  '(((id      . "EI-2")
     (status  . closed-negatively)
     (verdict . "Integration recipe with the existing five named axes does NOT carry substantive simultaneous cross-axis content.")
     (data-points
      ((RoleGraded         . (cells . 18) (non-trivial . 1) (axis-pair . "Role x Grade"))
       (RoleMode           . (cells . 9)  (non-trivial . 1) (axis-pair . "Role x Mode"))
       (ModeGraded         . (cells . 18) (non-trivial . 0) (axis-pair . "Mode x Grade"))
       (RoleModeGrade-RM   . (cells . 27) (non-trivial . 1) (axis-pair . "Role x Mode @ 3D pairwise"))
       (RoleModeGrade-RG   . (cells . 36) (non-trivial . 1) (axis-pair . "Role x Grade @ 3D pairwise"))
       (RoleModeGrade-MG   . (cells . 36) (non-trivial . 0) (axis-pair . "Mode x Grade @ 3D pairwise"))
       (RoleModeGrade-trip . (cells . 54) (non-trivial . 1) (axis-pair . "Role x Mode x Grade @ triple"))
       (RoleRole-pair      . (cells . 9)  (non-trivial . 0) (axis-pair . "Role x Role independent product; trivial by categorical product"))
       (RoleRole-shared    . (cells . n/a) (non-trivial . n/a) (axis-pair . "Role x Role shared state; recipe does not apply"))))
     (load-bearing-content . "Every non-trivial cell carries one-axis-at-a-time content; the load-bearing transport is always Choreo's client-to-server at the c⊑s strict step.")
     (criterion-status     . "Non-loss-only criterion is necessary but NOT sufficient for substantive simultaneous interaction.")
     (forbidden-reopen-framings
      . ("non-loss-only as recipe precondition (READING 2)"
         "weakened gate-1 with NLO precondition (READING 2)"
         "richer family choice for ModeGrade (would not change the structural finding)"
         "alternative axis pair within the existing five named axes"))
     (authoritative-record-files
      . ("docs/EI2_REPORT.adoc"                ; top Status section
         "docs/next-questions.adoc"             ; closed section
         "proofs/agda/characteristic/RecipeNonTriviality.agda"))
     (date . "2026-04-29"))))

;;; ============================================================
;;; Standing decisions (treat as load-bearing; do not relitigate)
;;; ============================================================

(define standing-decisions
  '(((id . sd-001)
     (title  . "Distinctness load is carried by truncation + 2-cell arguments")
     (status . accepted)
     (date   . "2026-04-29")
     (rationale . "Across all attempted axis pairings (including the only NLO self-pairing), the integration recipe produces only one-axis-at-a-time content. Truncation (echo-not-prop family) and 2-cell (Sophisticated submodules) carry the gate-1 distinctness load independently of the recipe.")
     (artefacts . ("proofs/agda/examples/{TropicalArgmin,EpistemicUpdate,LinearErasure}.agda"
                   "proofs/agda/EchoVsQuotient.Sophisticated"
                   "proofs/agda/EchoVsGalois.Sophisticated"))
     (consequences . "Gate-1's claim has been narrowed across 5 doc locations. The recipe remains useful as organising vocabulary."))

    ((id . sd-002)
     (title  . "Recipe is organising vocabulary, NOT locus of distinctness")
     (status . accepted)
     (date   . "2026-04-29")
     (rationale . "EI-2 termination established that recipe-level commutation theorems are vacuous when no axis is non-loss-only, and degenerate to coordinate-product or undefined transport when both are. The recipe still organises the per-axis lemma family (composition, join, propositionality) but does not produce substantive simultaneous integration content.")
     (forbidden-claims . ("recipe carries cross-axis distinctness"
                          "five axes simultaneously as a distinctness claim"
                          "non-loss-only is sufficient for substantive integration content"))
     (authoritative-text . "gate-2-handoff.adoc § Observation G"))

    ((id . sd-003)
     (title  . "Forge workflow: GitHub canonical, hub-and-spoke mirror outward")
     (status . accepted)
     (date   . "2026-04-28")
     (rationale . "User's standing forge workflow (overrides the static gitlab>github preference for git operations specifically). Mirror to GitLab and Codeberg via Actions workflow with token-based auth.")
     (artefacts . (".github/workflows/mirror.yml" "MIRROR_SETUP.adoc")))

    ((id . sd-004)
     (title  . "Cross-platform compatibility: Linux primary, Windows secondary")
     (status . accepted)
     (date   . "2026-04-28")
     (rationale . "User works across two machines (Fedora Kinoite primary, Windows for travel). Build instructions must be path-agnostic; line endings normalised via .gitattributes.")
     (artefacts . (".gitattributes")))

    ((id . sd-005)
     (title  . "Recipe extension parked for v0.2+, NOT v0.1.x scope")
     (status . accepted)
     (date   . "2026-04-29")
     (rationale . "The positive-termination route — extending the recipe to allow coupled state across axes or multiple live positions per axis — is genuinely separate work, not unfinished EI-2 business. It would require new modules, not a rerun of EI-2.")
     (when-active . "When v0.2 work begins, file as a new question (e.g., EI-3) rather than reopening EI-2."))

    ((id . sd-006)
     (title  . "Two-document-family doc surface: Reading 1 and Reading 2 patches superseded")
     (status . accepted)
     (date   . "2026-04-29")
     (rationale . "Both candidate readings drafted during EI-2 investigation (READING 1: weaken gate-1 with NLO precondition; READING 2: refine recipe with NLO precondition) were superseded by the stronger-negative trajectory found via RoleRole.agda. Files kept as historical record only; SUPERSEDED banners applied.")
     (superseded-files . ("docs/EI2_READING1_PATCHES.adoc"
                          "docs/EI2_READING2_PATCHES.adoc"
                          "docs/EI2_READINGS_COMPARISON.adoc")))))

;;; ============================================================
;;; Artefacts produced during EI-2 (canonical file list)
;;; ============================================================

(define artefacts
  '((agda-characteristic-lane
     . ("proofs/agda/characteristic/RoleGraded.agda"          ; original EI-1 closure
        "proofs/agda/characteristic/RoleMode.agda"            ; phase 3 sibling
        "proofs/agda/characteristic/ModeGraded.agda"          ; phase 2 sibling (note trailing 'd')
        "proofs/agda/characteristic/RoleModeGrade.agda"       ; 3D obligation 4
        "proofs/agda/characteristic/RoleRole.agda"            ; phase 5 critical test
        "proofs/agda/characteristic/InteractionTest.agda"     ; phase 4 simultaneity obstacle
        "proofs/agda/characteristic/RecipeSpec.agda"          ; phase 5 recipe-as-record
        "proofs/agda/characteristic/RecipeTheorem.agda"       ; partial generic, per-axis halves
        "proofs/agda/characteristic/RecipeNonTriviality.agda" ; concrete construction halves (PATH B)
        "proofs/agda/characteristic/ChoreoInjective.agda"     ; NLO certificate for Choreo
        "proofs/agda/characteristic/IntegrationAudit.agda"    ; EI-1 falsifier exhibit
        "proofs/agda/characteristic/VisibleConstraintAudit.agda"))
    (docs
     . ("docs/EI2_REPORT.adoc"             ; authoritative report (top Status section)
        "docs/EI2_READING1_PATCHES.adoc"   ; superseded
        "docs/EI2_READING2_PATCHES.adoc"   ; superseded
        "docs/EI2_READINGS_COMPARISON.adoc" ; superseded
        "docs/next-questions.adoc"))         ; EI-2 closed section
    (modified
     . ("docs/gate-1-distinct-phenomenon.adoc"  ; § The Gate #1 claim narrowed
        "docs/gate-2-handoff.adoc"              ; § Observation G updated
        "docs/adjacency/README.adoc"            ; EI-2 cascade note
        "roadmap-gates.adoc"                    ; § Gate 1 Claim narrowed
        "README.md"))                            ; integration-bridge bullet updated
    (integration-tracking
     . ("INTEGRATION_COMMITS.adoc"))             ; 7 commits, EI-2 termination = commit 7
    (staging-area
     . "/mnt/user-data/outputs/audit-output/")))

;;; ============================================================
;;; Documentation cascade applied (where the narrowed claim lives)
;;; ============================================================

(define cascade-applied
  '(((file . "docs/gate-1-distinct-phenomenon.adoc")
     (section . "§ The Gate #1 claim")
     (change . "Distinctness rerouted to truncation + 2-cell arguments; integration explicitly removed from distinctness load."))
    ((file . "docs/gate-2-handoff.adoc")
     (section . "§ Observation G")
     (change . "Recipe characterised as organising vocabulary; EI-2 finding recorded in NOTE block; NLO-vs-loss-only column added to instances table."))
    ((file . "roadmap-gates.adoc")
     (section . "§ Gate 1 Claim")
     (change . "Same narrowing as gate-1-distinct-phenomenon.adoc."))
    ((file . "docs/adjacency/README.adoc")
     (section . "Where the wins live (NOTE after table)")
     (change . "EI-2 cascade note added explaining recipe-vs-2-cell-level distinction."))
    ((file . "README.md")
     (section . "integration-bridge bullet in feature list")
     (change . "Updated to reflect recipe as organising vocabulary, with link to EI2_REPORT."))
    ((file . "docs/next-questions.adoc")
     (section . "§ Closed questions")
     (change . "Full EI-2 entry with seven-data-point evidence table, file list, and termination rationale."))))

;;; ============================================================
;;; Do-not-redo register (anti-duplicate-work checklist)
;;; ============================================================

(define do-not-redo
  '(("Build a fourth 2D sibling construction with NLO criterion to test recipe-non-triviality"
     . "Done in spirit: RoleRole.agda showed even Choreo×Choreo doesn't help. Adding a fourth pair would not change the structural finding.")
    ("Draft READING 1 (weaken gate-1) or READING 2 (refine recipe) doc patches"
     . "Both drafted and superseded. SUPERSEDED banners on EI2_READING{1,2}_PATCHES.adoc.")
    ("Attempt to formalise the full recipe-non-triviality 2D iff theorem in safe Agda"
     . "Documented as not formalisable without postulates (decidable equality, F-collapses axioms, extensionality). PATH B accepted partial formalisation.")
    ("Re-run RoleGraded with a different family choice F : Role × Grade → Set"
     . "Three structural choices were evaluated; the negative finding is family-independent.")
    ("Re-investigate whether Choreo's transport is genuinely non-loss-only"
     . "Formal certificate exists: client-to-server-injective-on-proj₁ in ChoreoInjective.agda. Do not redo.")
    ("Open a new EI-2 entry to track the recipe extension"
     . "Recipe extension is genuinely separate work; track as a new question (e.g., EI-3) when v0.2 work begins, not as EI-2 reopening.")
    ("Add ModeGrade.agda (without trailing 'd')"
     . "ModeGraded.agda (with trailing 'd') is canonical. The duplicate without trailing 'd' was created in error during this session and removed.")))

;;; ============================================================
;;; Forbidden rebrandings (to prevent recurrence under new names)
;;; ============================================================

(define forbidden-rebrandings
  '("the integration argument carries gate-1's distinctness load"
    "the recipe is uniformly applicable across all 2D axis pairs"
    "non-loss-only is sufficient for substantive simultaneous interaction"
    "five axes simultaneously as a distinctness claim"
    "Mode × Grade is a falsifier in some weaker sense"
    "Role × Role would have produced substantive content with a better family choice"))

;;; ============================================================
;;; Next actions (post-termination, gate-1/gate-2/gate-3 work that
;;; remains open and is NOT EI-2 follow-up)
;;; ============================================================

(define next-actions
  '(((id . t-3)
     (title . "Gate-1 falsification test 3 (informativeness collapse)")
     (status . unstubbed)
     (relevance . "Now better-targeted post-EI-2: with RoleGraded in place, ask whether the role-or-grade axis is derivable from the other plus a forgetful functor.")
     (priority . medium))

    ((id . q2-4)
     (title . "Falsifier attempts for surviving gate-2 nominees")
     (status . open)
     (relevance . "Each surviving nominee has an unattempted falsifier. Worth attempting at least one to harden the gate-2 case beyond 'no successful reduction has been attempted'.")
     (priority . medium))

    ((id . q2-1)
     (title . "Generalisation of echo-not-prop")
     (status . open)
     (relevance . "n=2 special case proofs generalise to: for non-injective f with at least two distinct preimages of y, is-prop (Echo f y) → ⊥. Closing this also discharges the truncation-argument gap for refinement, IFC, and provenance adjacency notes.")
     (priority . high)
     (rationale . "Truncation argument is one of the two load-bearing distinctness arguments post-EI-2; strengthening it has high leverage."))

    ((id . q2-3)
     (title . "Adopt RoleGraded.choreo-grade-commute as nominee N5")
     (status . open)
     (relevance . "Gate-2's audit flagged it as candidate fifth nominee but did not adopt. Adoption pushes the audit count to 5-of-5 across four constructions.")
     (priority . low)
     (note . "Mostly bookkeeping post-EI-2 since the recipe is no longer the distinctness locus."))

    ((id . integration)
     (title . "Apply the seven-commit integration sequence")
     (status . ready)
     (relevance . "INTEGRATION_COMMITS.adoc has the full sequence. Commit 7 is the EI-2 termination. All artefacts are staged at /mnt/user-data/outputs/audit-output/.")
     (priority . high))

    ((id . v0-2-recipe-extension)
     (title . "Recipe extension exploration (parked)")
     (status . parked-v0.2)
     (relevance . "Coupled state across axes; multiple live positions per axis. New module work, not a re-investigation of EI-2.")
     (priority . deferred))))

;;; ============================================================
;;; END OF STATE
;;; ============================================================
