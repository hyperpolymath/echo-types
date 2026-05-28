{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- ============================================================
-- EchoDecorationBridge.agda  (EXPLORATORY)
-- ============================================================
--
-- Status.  Exploratory bridge module.  Not load-bearing for the
-- identity claim, not part of Gate theory, not imported by
-- All.agda, subject to abandonment without notice.  See:
--
--   docs/echo-types/explorations/decoration-bridge/README.adoc
--   roadmap.adoc § Deferred research track § R5
--
-- The bridge frames adjacent-domain constructions (CRDT merges,
-- gossip partial views, local-first causal histories) as
-- candidate analogies for the EchoIntegration shape, NOT as
-- evidence that the integration recipe generalises.  Scope is
-- strictly the Choreo × Graded axis pair that EchoIntegration
-- already integrates.  External candidates that need to vary the
-- axis pair are out of scope.
--
-- Imports (the *only* upstream surfaces this module touches).
--   * EchoIntegration:
--       knowledge-and-controlled-degradation
--       knowledge-preserved-under-choreo
--       merged-at-residue
--       distinct-at-keep
--   * EchoChoreo:
--       Role, Client
--       Global
--       client-stability
--       scramble-server
--   * EchoGraded:
--       keep≤residue
--       degrade
--   * EchoCharacteristic (transitive surface mentioned in
--     EchoIntegration's return type):
--       echo-true, echo-false
--   * EchoEpistemic (transitive surface mentioned in
--     EchoIntegration's input type):
--       Knows
--
-- Signature-change policy.  If any listed upstream lemma changes
-- signature, this module is re-checked.  If patching it to track
-- the new signature would impose *any* constraint on upstream
-- code — even a benign-looking one — this module is retired, not
-- patched.  Exploratory code does not get to vote on what
-- upstream code is allowed to look like; that is the whole point
-- of the isolation discipline.
--
-- Reverse-import discipline.  No non-bridge module imports this
-- one.  Adding such an import re-attaches the exploration to
-- load-bearing code, defeats the cleanly-abandonable property,
-- and is a violation.  If a downstream use case appears, the
-- correct response is to promote the relevant content to a
-- proper core module via the normal rung-consolidation policy,
-- not to import EchoDecorationBridge.
--
-- Retraction-watch (docs/retractions.adoc R-2026-05-18).  Do not
-- describe the records or functions below as:
--   * a categorical characterisation of decoration-residue
--     (Pillar B is funext-relative pointwise, not full UP);
--   * a graded comonad structure (EchoGraded is a thin-poset
--     reindexing modality, not a graded comonad);
--   * a model-independent decoration semantics (EchoRelModel is
--     carrier-parametricity over a fixed grade poset, not
--     model-independence).
-- If the bridge ever produces content that looks like any of the
-- above, retraction-watch trips and the bridge closes pending
-- review.
--
-- Forbidden-rebrandings discipline.
-- (.machine_readable/6a2/STATE.a2ml § forbidden-rebrandings)
-- The framing is scoped to the *one* Choreo × Graded axis pair
-- that EchoIntegration uses.  External candidate instances are
-- analogies that may or may not fit, never evidence that the
-- integration recipe is uniformly applicable across 2D axis
-- pairs.  See README §"Forbidden-rebrandings check" for the
-- auditable cite-by-name verdict.

module EchoDecorationBridge where

----------------------------------------------------------------------
-- Imports.  Tight and audited (see header).
----------------------------------------------------------------------

open import EchoChoreo using
  ( Role; Client
  ; Global
  ; client-stability
  ; scramble-server
  )
open import EchoGraded using
  ( keep≤residue
  ; degrade
  )
open import EchoIntegration using
  ( knowledge-and-controlled-degradation
  ; knowledge-preserved-under-choreo
  ; merged-at-residue
  ; distinct-at-keep
  )

-- Transitive surfaces (mentioned in EchoIntegration's input /
-- return types; the bridge re-issues those types verbatim).
open import EchoCharacteristic using (echo-true; echo-false)
open import EchoEpistemic using (Knows)

open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

----------------------------------------------------------------------
-- Section 1.  The fit shape.
--
-- An external candidate instance fits the EchoIntegration shape
-- precisely when it can supply the inputs that
-- `knowledge-and-controlled-degradation` consumes:
--
--   (a) a predicate on Global naming the candidate's invariant;
--   (b) a proof that the invariant is preserved under
--       `scramble-server`, the specific hidden-state update
--       EchoChoreo names (NB: not a general invariance claim —
--       only this one update);
--   (c) a Client-side knowledge witness at a fixed Bool target.
--
-- This record names that fit shape.  It does NOT generalise over
-- the role pair, the grade lattice, the choreographic update, or
-- the visible-codomain shape.  Any candidate that would need to
-- vary one of those is out of scope for this scaffold and fails
-- the fit by construction.
--
-- TODO(bridge): the record currently mirrors EchoIntegration's
-- inputs one-to-one.  That is intentional for the scaffold —
-- making the fit shape strictly narrower than the integration
-- claim it triggers means external candidates have somewhere
-- precise to land or honestly fail to land.
----------------------------------------------------------------------

record DecorationFit (y : Bool) : Set₁ where
  field
    Pred        : Global → Set
    Pred-stable : ∀ g → Pred g → Pred (scramble-server g)
    knowledge   : Knows Client Pred y

----------------------------------------------------------------------
-- Section 2.  Plug-in: a fitting candidate inherits the
-- EchoIntegration conclusion verbatim.
--
-- This is the bridge's *only* current substantive content — a
-- type-level demonstration that the integration shape is what
-- candidates must produce, not a new theorem.  The body is
-- literally the integration lemma applied to the record's
-- fields; the value of the wrapper is that an external candidate
-- can see, in one place, exactly what it owes the bridge.
--
-- TODO(bridge): there is no second-order content here.  If a
-- real candidate ever lands and forces a genuinely new lemma
-- (rather than a re-package), that lemma is the moment to
-- re-audit the bridge scope against the forbidden-rebrandings
-- register, because "novel cross-axis content" is structurally
-- adjacent to several entries.
----------------------------------------------------------------------

decoration-claim :
  ∀ {y : Bool} (fit : DecorationFit y) →
  (∀ e → DecorationFit.Pred fit (proj₁ (client-stability e)))
  × (degrade keep≤residue echo-true ≡ degrade keep≤residue echo-false)
decoration-claim fit =
  knowledge-and-controlled-degradation
    (DecorationFit.Pred-stable fit)
    (DecorationFit.knowledge fit)

----------------------------------------------------------------------
-- Section 3.  What is intentionally absent (and why).
--
-- The following are NOT in this module, and adding them would
-- exceed the bridge scope:
--
--   * A second axis pair.  Mode × Grade, Role × Role, and 3D
--     combinations are all foreclosed by EI-2.  The bridge does
--     not re-attempt them under a new framing.
--   * A "general candidate" record polymorphic over decoration
--     pairs.  That structure is precisely what the EI-2
--     termination shows does not carry substantive simultaneous
--     content; framing it as a bridge-side interface would be a
--     forbidden-rebranding under STATE.forbidden-rebrandings
--     entry "the recipe is uniformly applicable across all 2D
--     axis pairs".
--   * Composition of `decoration-claim` with itself across
--     different `y` values.  The EchoIntegration claim is at one
--     y; composing two such claims is meaningful only inside the
--     core development, where `client-stability`'s functorial
--     law lives.  The bridge does not lift that machinery.
--   * Universal-property language for `DecorationFit`.  It is a
--     record, not a limit; describing it as terminal among
--     candidates would trip retraction-watch.
--
-- TODO(bridge): if any of these become tempting during a future
-- session, stop and read this section first.
----------------------------------------------------------------------
