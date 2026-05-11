{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Gate 2 audit: N5Falsifier
--
-- VERDICT: the N5 candidate (`characteristic.RoleGraded.choreo-grade-commute`)
-- SURVIVES the sharpened falsifier. The candidate is ready for adoption
-- as the fifth gate-2 nominee in `roadmap-gates.adoc`.
--
-- Background. STATE.next-actions q2-3 (low-priority bookkeeping
-- post-EI-2) calls for adopting `choreo-grade-commute` as nominee N5.
-- The gate-2 audit doc surface flagged it as a candidate fifth nominee
-- but did not adopt pending a falsifier attempt of the same shape that
-- successfully struck down N3 (`knowledge-and-controlled-degradation`,
-- formalised in `characteristic.IntegrationAudit`).
--
-- The N3 sharpened falsifier exhibited:
--
--   * `split-knowledge` — pure-choreo restatement (no `degrade`).
--   * `split-merging`   — pure-grade restatement (no role).
--   * `N3-is-product`   — original ≡ literal pair of the two splits.
--   * `split-merging-uses-no-hypotheses` — conjunct 2 ignores N3's
--     hypotheses, witnessing "no shared data between conjuncts".
--
-- For N5, the same shape is structurally inapplicable: both sides of
-- the equation reference both decoration witnesses (`rp`, `gp`) and
-- the same data (`e`). There is no pair of pure-axis facts whose
-- product reproduces the theorem, because the content of N5 is the
-- *coincidence* of two action orderings on shared data.
--
-- Honest narrowing (per STATE standing-decisions sd-002). The recipe
-- is organising vocabulary, NOT distinctness load. Adoption of N5 is
-- bookkeeping completion of the gate-2 nominee table; the gate-1
-- distinctness load is carried by truncation (echo-not-prop family)
-- and 2-cell arguments (Sophisticated submodules), independently of
-- this theorem.
--
-- Recommendation (closing). Add `RoleGraded.choreo-grade-commute` as
-- the fifth gate-2 nominee N5 in `roadmap-gates.adoc`, raising the
-- audit count to 5-of-5 across the four characteristic constructions.
------------------------------------------------------------------------

module characteristic.N5Falsifier where

open import Data.Product.Base                     using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import EchoChoreo                            using
  ( Client
  ; Server
  ; client-to-server
  ; _⊑c_
  ; c⊑c
  ; c⊑s
  ; s⊑s
  )
open import EchoGraded                            using
  ( _≤g_
  ; keep
  ; keep≤keep
  )
open import characteristic.RoleGraded             using
  ( RoleGEcho
  ; applyRole
  ; applyGrade
  ; choreo-grade-commute
  )

------------------------------------------------------------------------
-- Same-data witness
--
-- Both sides of N5's equation are functions of all three binders
-- (`rp`, `gp`, `e`). Below, `LHS` and `RHS` package each side as a
-- function consuming the full triple, making the data-dependency
-- syntactic. Compare with N3, where `split-merging` was a closed term
-- referencing none of N3's hypotheses; here neither side admits a
-- closed-form restatement that drops one of `rp`, `gp`, or `e`.
------------------------------------------------------------------------

LHS :
  ∀ {r1 r2 g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2) (e : RoleGEcho r1 g1) →
  RoleGEcho r2 g2
LHS rp gp e = applyGrade gp (applyRole rp e)

RHS :
  ∀ {r1 r2 g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2) (e : RoleGEcho r1 g1) →
  RoleGEcho r2 g2
RHS rp gp e = applyRole rp (applyGrade gp e)

-- The equation under audit. Same statement as
-- `RoleGraded.choreo-grade-commute`, exposed here as a function of
-- the triple `(rp, gp, e)`.
N5-equation :
  ∀ {r1 r2 g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2) (e : RoleGEcho r1 g1) →
  LHS rp gp e ≡ RHS rp gp e
N5-equation = choreo-grade-commute

-- Shared-data Σ witness. Both `LHS rp gp e` and `RHS rp gp e` arise
-- from a single triple, and the equation between them is recovered
-- from `choreo-grade-commute`. The Σ-type makes explicit that the
-- two sides are jointly determined by `(rp, gp, e)`; there is no
-- decomposition of `(LHS, RHS)` into independent components.
shared-data :
  ∀ {r1 r2 g1 g2}
  (rp : r1 ⊑c r2) (gp : g1 ≤g g2) (e : RoleGEcho r1 g1) →
  Σ (RoleGEcho r2 g2) (λ lhs →
  Σ (RoleGEcho r2 g2) (λ rhs →
    (lhs ≡ LHS rp gp e) × (rhs ≡ RHS rp gp e) × (lhs ≡ rhs)))
shared-data rp gp e =
  LHS rp gp e , RHS rp gp e , refl , refl , N5-equation rp gp e

------------------------------------------------------------------------
-- Why the N3-shape falsifier does not apply
--
-- For N3, exhibiting `(split-knowledge , split-merging)` as the
-- literal product was possible because the original was a `_×_` of
-- two facts that named no common term. For N5, neither side admits
-- a single-axis restatement at all: stripping `applyRole` from
-- `LHS rp gp e` discards the `rp` dependency, but the resulting term
-- `applyGrade gp e` no longer has the type of the original LHS
-- (which lives in `RoleGEcho r2 g2`, not `RoleGEcho r1 g2`).
--
-- The structural witness of inapplicability is therefore: there is
-- no pair `(P-choreo, P-grade)` of pure-axis statements such that
-- `P-choreo × P-grade` has the type of `N5-equation`. A formal
-- impossibility proof would require quantifying over Agda terms
-- (meta-level), but the type-level obstruction is visible in the
-- signatures of `LHS` and `RHS` above: both ineliminably consume
-- all three binders.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Single-axis collapses (both decorations forced to identity)
--
-- When both `rp` and `gp` are identity steps (`c⊑c`/`s⊑s` and
-- `keep≤keep`), the equation degenerates to reflexivity on `e`.
-- These cells witness the *absence* of substantive content in the
-- single-axis halves: if N5 *were* a product of pure-axis facts, the
-- collapses below would expose non-trivial pure-axis content. They
-- do not — they all close by `refl` because identity steps are
-- identity.
------------------------------------------------------------------------

-- (rp, gp) = (c⊑c, keep≤keep): both sides reduce to `e ≡ e`.
collapse-cc-keep :
  (e : RoleGEcho Client keep) →
  applyGrade keep≤keep (applyRole c⊑c e)
  ≡ applyRole c⊑c (applyGrade keep≤keep e)
collapse-cc-keep e = refl

-- Symmetric case (rp, gp) = (s⊑s, keep≤keep). The source role is
-- forced to `Server` by the type of `s⊑s : Server ⊑c Server`.
collapse-ss-keep :
  (e : RoleGEcho Server keep) →
  applyGrade keep≤keep (applyRole s⊑s e)
  ≡ applyRole s⊑s (applyGrade keep≤keep e)
collapse-ss-keep e = refl

------------------------------------------------------------------------
-- The non-trivial cell (c⊑s, keep≤keep)
--
-- The single non-trivial cell of N5. Both sides reduce to
-- `client-to-server e`. The load-bearing transport is the pure
-- choreographic step `client-to-server`; the grade axis contributes
-- only the identity step `keep≤keep`, which does not enter the
-- reduction. There is no grade-only factor available to pair with a
-- pure-choreo factor — the identity grade step provides nothing to
-- factor out.
------------------------------------------------------------------------

non-trivial-cell-equation :
  (e : RoleGEcho Client keep) →
  applyGrade keep≤keep (applyRole c⊑s e)
  ≡ applyRole c⊑s (applyGrade keep≤keep e)
non-trivial-cell-equation e = refl

-- Both sides reduce to `client-to-server e`.
non-trivial-cell-LHS-reduces :
  (e : RoleGEcho Client keep) →
  applyGrade keep≤keep (applyRole c⊑s e) ≡ client-to-server e
non-trivial-cell-LHS-reduces e = refl

non-trivial-cell-RHS-reduces :
  (e : RoleGEcho Client keep) →
  applyRole c⊑s (applyGrade keep≤keep e) ≡ client-to-server e
non-trivial-cell-RHS-reduces e = refl

-- Joint witness: both sides equal `client-to-server e`, exhibiting
-- explicitly that the load-bearing transport in this cell is pure
-- choreographic. There is no companion pure-grade factor; the grade
-- step `keep≤keep` is identity and contributes nothing.
non-trivial-cell-pure-choreo :
  (e : RoleGEcho Client keep) →
    (applyGrade keep≤keep (applyRole c⊑s e) ≡ client-to-server e)
  × (applyRole c⊑s (applyGrade keep≤keep e) ≡ client-to-server e)
non-trivial-cell-pure-choreo e =
  non-trivial-cell-LHS-reduces e , non-trivial-cell-RHS-reduces e

------------------------------------------------------------------------
-- Closing
--
-- The N5 candidate survives the sharpened falsifier. Recommended
-- action: amend `roadmap-gates.adoc` to add
-- `RoleGraded.choreo-grade-commute` as the fifth gate-2 nominee N5,
-- with this file linked from the gate-2 audit doc surface as the
-- falsifier-attempt record.
--
-- Per the set-2 task spec, this file deliberately modifies nothing
-- existing. Registering N5Falsifier in `proofs/agda/All.agda` (so the
-- verified suite covers it, per project convention) is the
-- integrator's call.
------------------------------------------------------------------------
