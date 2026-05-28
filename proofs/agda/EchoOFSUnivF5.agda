{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Gate F5 first slice (docs/echo-types/earn-back-plan.adoc §"Gate F5
-- — Full OFS, honestly qualified" — to be added).
--
-- The R-2026-05-18 discipline narrowed Echo's "full OFS" claim to
-- (factorisation existence + fibre identification at the K-free
-- level); the COMPLETE (equivalence, projection) factorisation
-- system would need uniqueness up to isomorphism + the diagonal
-- lifting property, both of which require funext to STATE
-- (function-level equations rather than pointwise).
--
-- F5's earn-back is, exactly as F4: not "retracted → unconditional"
-- but "retracted → *true, conditional*". Parameterise the strict
-- function-level theorem by an EXPLICIT funext hypothesis (a module
-- parameter — never a postulate), exactly as `EchoPullbackUnivF4`
-- does for the pullback's strict terminality. The unconditional
-- pointwise content stays as the funext-free corollary; the
-- function-level form is true given funext, stated as such.
--
-- This module ships the FIRST F5 slice: the strict-function form of
-- the OFS factorisation triangle `f ≡ proj₁ ∘ encode f`. The
-- pointwise form `(x : A) → f x ≡ proj₁ (encode f x)` is already
-- in `EchoOrthogonalFactorizationSystem.echo-factorisation`
-- (definitional, K-free). The strict form lifts it via funext in
-- one line.
--
-- Subsequent F5 slices (deferred, separate modules):
--
--   * F5-2 — Diagonal lifting property (squares with left
--     equivalence + right projection have unique lifters). Needs
--     `HasInverse`-coherence + funext on both the lifter equation
--     and the uniqueness clause.
--
--   * F5-3 — Uniqueness up to iso (any other (eq, proj)
--     factorisation `f = m' ∘ e'` admits a canonical iso onto the
--     Echo factorisation). Needs both funext and a coherent-
--     equivalence upgrade of `EchoLossTaxonomy.HasInverse`.
--
-- The first slice (this module) closes the simplest, most directly
-- analogous earn-back: lifting the EXISTING K-free pointwise
-- triangle to its strict function form under funext. The pattern
-- (three lines: pointwise lemma + funext application + the strict
-- form) is identical to F4's `echo-pullback-univ-strict`. The
-- harder slices (F5-2, F5-3) await follow-on sessions.
--
-- Not wired into `All.agda` / `Smoke.agda` until Gate F5 is
-- recorded as passed in the earn-back ledger; pinned here so the
-- gate has its artefact ready when the ledger updates.
--
-- Headlines (will be pinned in Smoke.agda once gate passes):
--
--   * FunExt₀                          -- the funext hypothesis (same shape as F4)
--   * echo-factorisation-strict        -- f ≡ proj₁ ∘ encode f (given funext)
--   * echo-factorisation-pointwise     -- the funext-free corollary

module EchoOFSUnivF5 where

open import Echo                              using (Echo)
open import EchoTotalCompletion               using (encode; f-factors-via-projection)
open import EchoOrthogonalFactorizationSystem using (echo-factorisation)

open import Data.Product.Base                 using (Σ; _,_; proj₁; proj₂)
open import Function.Base                     using (_∘_)
open import Relation.Binary.PropositionalEquality
                                              using (_≡_)

----------------------------------------------------------------------
-- The funext hypothesis (same shape as `EchoPullbackUnivF4.FunExt₀`).
--
-- `Set₁` because it quantifies over `Set`. NOT a postulate; the
-- caller supplies it as a parameter to the module below, exactly
-- as F4 does.
----------------------------------------------------------------------

FunExt₀ : Set₁
FunExt₀ =
  {A : Set} {B : A → Set} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

----------------------------------------------------------------------
-- Strict factorisation triangle, parameterised by funext.
--
-- The pointwise form `(x : A) → f x ≡ proj₁ (encode f x)` is
-- `EchoOrthogonalFactorizationSystem.echo-factorisation` (= the
-- re-export of `EchoTotalCompletion.f-factors-via-projection`),
-- and is `refl` at every point (the factorisation triangle
-- commutes definitionally). Funext upgrades this to the
-- function-level equation `f ≡ proj₁ ∘ encode f` in one line.
----------------------------------------------------------------------

module _ (funext : FunExt₀) where

  echo-factorisation-strict :
    {A B : Set} (f : A → B) →
    f ≡ proj₁ ∘ encode f
  echo-factorisation-strict f = funext (echo-factorisation f)

----------------------------------------------------------------------
-- The funext-free corollary, kept verbatim from the OFS module.
-- Reading:
--
--   * unconditional, zero hypotheses : pointwise factorisation
--       (`echo-factorisation-pointwise` — `∀ x → f x ≡ proj₁
--         (encode f x)`);
--   * conditional on `funext`        : strict factorisation
--       (`echo-factorisation-strict`  — `f ≡ proj₁ ∘ encode f`).
--
-- No claim is upgraded beyond what its hypothesis licenses: the
-- strict form is *true given funext*, stated as such; the
-- pointwise form remains the unconditional K-free artefact.
----------------------------------------------------------------------

echo-factorisation-pointwise :
  {A B : Set} (f : A → B) (x : A) →
  f x ≡ proj₁ (encode f x)
echo-factorisation-pointwise f = echo-factorisation f

----------------------------------------------------------------------
-- Companion remark.
--
-- This is the FIRST F5 slice — the simplest, most directly
-- analogous earn-back to F4's `echo-pullback-univ-strict`. The
-- complete F5 gate also requires:
--
--   * F5-2: the diagonal lifting property. Given a commutative
--     square `e : A → A'` (equiv) + `p : Σ B (Echo f) → B`
--     (projection = `proj₁`) + `h : A → Σ B (Echo f)` +
--     `k : A' → B` with `proj₁ ∘ h ≡ k ∘ e` pointwise, there is
--     a unique `lift : A' → Σ B (Echo f)` with `lift ∘ e ≡ h`
--     and `proj₁ ∘ lift ≡ k`. Construction: `lift x = h (e⁻¹ x)`;
--     pointwise commutativity is K-free; strict form needs funext.
--     Uniqueness: any `lift'` satisfying both pointwise equations
--     is pointwise equal to `lift`; strict uniqueness needs funext.
--
--   * F5-3: factorisation uniqueness up to iso. Given any other
--     `g : A → X` equivalence + `p : X → B` with `p ∘ g ≡ f`
--     pointwise, construct a canonical `φ : X ↔ Σ B (Echo f)`
--     with `proj₁ ∘ φ.to ≡ p` (strict, given funext) and
--     `φ.to ∘ g ≡ encode f` (strict, given funext). Construction:
--     `φ.to x = (p x, g⁻¹ x, ?)` using `g`'s inverse from
--     `HasInverse`; the path-algebra obligations need funext.
--
-- Both follow-on slices land in separate modules once the gate's
-- ledger entry confirms F5-1 (this module) and authorises the
-- larger slices. The earn-back-plan ledger entry for F5 should
-- be added in the same commit that wires F5-1 into `Smoke.agda` /
-- `All.agda` (i.e. only after the user explicitly opts F5 into
-- the gate ledger).
----------------------------------------------------------------------
