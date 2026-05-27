{-# OPTIONS --safe --without-K #-}

-- EchoCanonicalIdentitySuite — the curated entry point for
-- "why Echo deserves a name". One file, organised in tiers,
-- pulling the load-bearing headlines from every Tier-1 / Tier-2 /
-- Tier-3 module into a single readable demonstration of the
-- identity claim's scope.
--
-- Reading this file top-to-bottom gives the structural arc:
--
--   1. CORE IDENTITY (Tier 1, the canonical-identity layer)
--      What "Echo" IS, named at the right level of abstraction:
--      the canonical fibre completion + one leg of the
--      (equivalence, projection) orthogonal factorisation system
--      on Type.
--
--   2. CLASSIFICATION GRID (Tier 2)
--      Function-side / residue-side / decoration-recipe /
--      observational-equivalence axes, organised as named
--      abstractions instead of comments.
--
--   3. QUALIFIED UNIVERSAL PROPERTY (Tier 3, Pillar F Gate F5)
--      The full OFS clauses earned back at the qualified level
--      (funext as explicit module parameter, never a postulate).
--
--   4. CEMENTING MATCHED-NEGATIVES
--      Two shadow encodings that have been claimed in the wild as
--      "enough" to capture Echo, provably aren't.
--
--   5. AUDIENCE FACES (Tier 3 audience moves)
--      Four parametric records exposing the structural content
--      under the names different domains speak in.
--
-- Each pinned name is the LOAD-BEARING headline from its source
-- module. The full module-by-module content + companion remarks
-- live in the source modules; this file is the curated index.
--
-- Build invariant. Every name pinned below is verified under
-- `--safe --without-K`, zero postulates, no funext in the
-- trusted base. Funext appears only as an explicit module
-- hypothesis for the qualified universal-property clauses (F5
-- slices), per the F4 template.
--
-- This is the load-bearing artefact for citing "Echo at full
-- structure". External readers should start here; the source
-- modules provide the proofs + the honest-scope guardrails.

module EchoCanonicalIdentitySuite where

----------------------------------------------------------------------
-- Tier 1 — CORE IDENTITY (the canonical-identity layer)
--
-- The named-theorem load-bearing artefacts that promote Echo from
-- a useful construction to a named structural object.
----------------------------------------------------------------------

-- The slogan-unlock: every irreversible map's domain is canonically
-- equivalent to the total space of its echoes.
open import EchoTotalCompletion public using
  ( encode                          -- A → Σ B (Echo f), the equivalence's forward leg
  ; decode                          -- Σ B (Echo f) → A, the backward leg
  ; A↔ΣEcho                          -- THE HEADLINE: A ≃ Σ B (Echo f), packaged as _↔_
  ; f-factors-via-projection         -- f factors definitionally as proj₁ ∘ encode
  )

-- The architectural keystone: every f : A → B factors as
-- A ≃ Σ B (Echo f) → B with left leg an equivalence + right leg
-- a projection.
open import EchoOrthogonalFactorizationSystem public using
  ( echo-factorisation               -- the triangle commutes (pointwise)
  ; left-leg-equivalence             -- = A↔ΣEcho, re-exported under OFS name
  ; projection-fibre-iso             -- the right leg's fibre at y is Echo f y
  ; ofs-witness                       -- the 4-tuple OFS witness at K-free level
  )

-- The image factorisation in Echo language.
open import EchoImageFactorization public using
  ( Image                            -- := Σ B (Echo f), the proof-relevant image
  ; image-factor-left                -- A → Image f (= encode)
  ; image-factor-right               -- Image f → B (= proj₁)
  ; image-factor-commutes            -- the triangle commutes definitionally
  ; Surjective                       -- := (b : B) → Echo f b
  ; Injective                        -- := {x y} → f x ≡ f y → x ≡ y
  ; injective-fibres-proj-unique     -- inj ⇒ K-free projection uniqueness
  )

-- The structural no-section theorem.
open import EchoNoSectionGeneric public using
  ( no-section-of-collapsing-map     -- THE HEADLINE: any collapsing map admits no section
  ; no-section-when-non-injective-at-y
                                      -- Echo-specific corollary: non-injective ⇒ no recovery
  )

----------------------------------------------------------------------
-- Tier 2 — CLASSIFICATION GRID
--
-- Function-side / residue-side / decoration-recipe / observational
-- axes organised as named abstractions. The audit's
-- "kinds-of-loss × shapes-of-residue × observation-equality" grid.
----------------------------------------------------------------------

-- Function-side: four-axis classification of f : A → B by echo shape.
open import EchoLossTaxonomy public using
  ( HasInverse                       -- the EQUIV case: quasi-inverse data
  ; equiv-fibre-center               -- EQUIV ⇒ canonical centre per fibre
  ; equiv-implies-injective          -- EQUIV ⇒ Injective
  ; equiv-fibre-proj-unique          -- EQUIV ⇒ K-free projection uniqueness
  ; inj-fibre-proj-unique            -- INJ ⇒ projection uniqueness (re-export)
  ; surj-fibre-inhabited             -- SURJ ⇒ every fibre inhabited (re-export)
  ; const-fun                        -- the canonical constant map
  ; const-fibre-section              -- CONST ⇒ section from full domain
  )

-- Residue-side: shared residue carrier + lowering.
open import EchoResidueTaxonomy public using
  ( ResidueForm                      -- THE RECORD: per-output carrier + lowering
  ; trivial-residue                  -- ⊤ residue (maximum collapse)
  ; identity-residue                 -- Echo f itself (no collapse)
  ; echoR-residue                    -- generic Σ-cert residue
  ; linear-affine-residue            -- worked non-trivial instance
  )

-- Decoration recipe: order + propositionality + join + UMP,
-- shared across the decoration zoo.
open import EchoDecorationStructure public using
  ( DecorationStructure              -- THE RECORD: seven-field decoration recipe
  ; graded-decoration-structure      -- EchoGraded instance
  ; linear-decoration-structure      -- EchoLinear instance
  ; access-decoration-structure      -- EchoAccess instance
  )

-- Observational equality: mode-indexed equality on LEcho.
open import EchoObservationalEquivalence public using
  ( _≡m_                              -- mode-indexed equality
  ; ≡m-refl                           -- reflexivity (per-mode)
  ; ≡m-sym                            -- symmetry (per-mode)
  ; linear-distinguishes-true-false   -- linear is witness-aware
  ; affine-collapses                  -- affine is witness-blind
  ; mode-equality-strictly-finer-at-linear
                                      -- THE HEADLINE: linear ⊃ affine equality
  )

----------------------------------------------------------------------
-- Tier 3 — QUALIFIED UNIVERSAL PROPERTY (Pillar F, Gate F5)
--
-- The full (equivalence, projection) OFS earned back at the
-- qualified level: funext as an explicit module hypothesis, never
-- a postulate. Unconditional pointwise corollaries kept funext-free.
----------------------------------------------------------------------

-- F5-1: strict factorisation triangle.
open import EchoOFSUnivF5 public using
  ( FunExt₀                          -- the funext hypothesis (same shape as F4)
  ; echo-factorisation-strict        -- f ≡ proj₁ ∘ encode f, GIVEN funext
  ; echo-factorisation-pointwise     -- the funext-free corollary
  )

-- F5-2: diagonal lifting property. Re-exported as the `F5Diag`
-- alias to avoid module-name clash with F5-3 (both have
-- `module Pointwise` + `module Strict` at top level). Consumers
-- access as `EchoCanonicalIdentitySuite.F5Diag.Pointwise (...)`
-- or import `EchoOFSUnivF5Diag` directly.
import EchoOFSUnivF5Diag as F5Diag

-- F5-3: factorisation uniqueness up to iso. Same `F5Iso` aliasing
-- convention.
import EchoOFSUnivF5Iso as F5Iso

----------------------------------------------------------------------
-- CEMENTING MATCHED-NEGATIVES
--
-- Two shadow encodings provably are NOT adequate substitutes for
-- Echo. Each pairs a positive claim about the shadow (it has a
-- section / it agrees on what it should) with a matched negative
-- against the witness side (Echo provably distinguishes / has no
-- section).
----------------------------------------------------------------------

-- Shannon-entropy shadow: the fibre-count shadow agrees on
-- echo-true vs echo-false (matched-negative against
-- EchoAbstractionBarrier.sigma-distinguishes).
open import EchoEntropy public using
  ( entropy-shadow                   -- ℕ-valued shadow on the collapse fibre
  ; shannon-shadow                   -- ⌊log₂⌋ of it
  ; entropy-shadow-blind             -- THE HEADLINE: entropy can't distinguish
  ; witness-distinguishes-where-entropy-cannot
                                      -- matched-negative: Σ side does distinguish
  )

-- LL `!A := 1` shallow encoding: admits a section that Echo
-- provably does not.
open import EchoLLEncoding public using
  ( LLShallowEncoding                -- the LL-encoding interface
  ; trivial-encoding                 -- the canonical X m := ⊤ shadow
  ; trivial-encoding-has-section     -- positive: the shadow's wX has a section
  ; source-no-section                -- matched-negative: Echo's weaken has none
  ; gap-paired                       -- THE HEADLINE: the gap as a single Σ
  )

----------------------------------------------------------------------
-- AUDIENCE FACES (Tier 3 audience moves)
--
-- Four parametric records exposing the structural content under
-- the names different domains speak in. The mathematical shape is
-- one Σ-with-tag pattern; the audience-side framings differ.
----------------------------------------------------------------------

-- Provenance — database / lineage / K-provenance audience.
open import EchoProvenance public using
  ( Provenance                       -- the abstract setup
  ; bool-over-nat-provenance         -- worked Bool-over-ℕ instance
  )

-- Security — region-exit / capability-flow audience.
-- (Imports `Security`, `TwoRegion`, `region-exit-audit-instance`;
-- the `SecurityTheorems` parametric module is also re-exported.)
open import EchoSecurity public using
  ( Security                         -- the abstract setup
  ; region-exit-audit-instance       -- worked 2-region LEcho instance
  )

-- ProbabilisticSupport — sampling / draw-id audience.
open import EchoProbabilisticSupport public using
  ( Sampling                         -- the abstract setup
  ; bool-indexed-nat-sampling        -- worked Bool-indexed-ℕ instance
  )

-- Differential — sensitivity / perturbation-tracking audience.
open import EchoDifferential public using
  ( Sensitivity                      -- the abstract setup
  ; bool-perturbed-nat-sensitivity   -- worked Bool-perturbed-ℕ instance
  )

----------------------------------------------------------------------
-- Closing companion remark.
--
-- This suite is the curated index, not the documentation. The
-- source modules contain the full companion remarks + honest-
-- scope guardrails + matched-negative `NotProved-*` blocks. A
-- reader citing any name pinned above should also read the
-- source module's companion-remark to understand the honest
-- scope of the claim being cited.
--
-- What this suite establishes, end-to-end:
--
--   * Echo is the canonical fibre completion: A ≃ Σ B (Echo f).
--   * Echo is one leg of the (equivalence, projection) OFS on
--     Type: the OFS witness lands at the K-free level
--     unconditionally, and the full universal-property clauses
--     land conditionally on funext (Gate F5, fully passed at
--     the qualified level).
--   * The function-side / residue-side / decoration-recipe /
--     observational-equality axes are all named abstractions
--     instead of comments — the Tier-2 classification grid is
--     mechanised.
--   * Shadow encodings (Shannon entropy, LL `!A := 1`)
--     provably aren't adequate substitutes — the cementing
--     matched-negatives close the "but couldn't you just use
--     entropy / LL?" line of attack.
--   * Four audience-facing records (Provenance, Security,
--     Sampling, Sensitivity) expose the structural content
--     under the names different domains speak in.
--
-- What this suite does NOT establish (honest scope):
--
--   * The (epi, mono) image factorisation — requires
--     propositional truncation, not available under `--safe
--     --without-K` without HITs. See `EchoImageFactorization`'s
--     companion-remark.
--   * Full contractible-fibre / propositional-fibre upgrades
--     of the Tier-2 EQUIV / INJ cases — require UIP. See
--     `EchoLossTaxonomy`'s companion-remark.
--   * Decoration-zoo wiring of the remaining six decoration
--     modules (Choreo, Cost, Search, Indexed, Epistemic) into
--     ResidueForm / DecorationStructure instances. Mechanical
--     follow-on; see the companion remarks of
--     `EchoResidueTaxonomy` / `EchoDecorationStructure`.
--   * Real-valued Shannon entropy / mutual information / DP
--     ε-budgets / measure-theoretic probability / cryptographic
--     security claims. Each audience-face module's matched-
--     negative `NotProved-*` block pins the relevant scope.
--   * The decoration-bridge exploration (parallel-session work
--     under `Exploratory/` or similar) — not part of this suite.
--
-- The suite stands as a single-file entry point for "Echo at
-- full structure" demonstrations. External-reader workflow:
-- read this file's pinned names + the source-module companion
-- remarks for the headlines that interest you.
----------------------------------------------------------------------
