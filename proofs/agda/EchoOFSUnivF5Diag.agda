{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Gate F5 second slice (docs/echo-types/earn-back-plan.adoc §"Gate
-- F5 — Full OFS, honestly qualified").
--
-- The diagonal lifting property for the (equivalence, projection)
-- factorisation system on Type. Same F4 template as F5-1: pointwise
-- (K-free) form lands unconditionally; strict (function-level) form
-- lifts via an explicit funext parameter.
--
-- The diagonal lifting square:
--
--     A ───h──→ Σ B (Echo f)
--     │            │
--     e            proj₁
--     ↓            ↓
--     A' ──k───→ B
--
-- with `e : A → A'` an equivalence (data: `HasInverse e`),
-- `proj₁ : Σ B (Echo f) → B` the canonical projection,
-- `h : A → Σ B (Echo f)`, `k : A' → B`, and a pointwise
-- commutativity witness `square : ∀ a → proj₁ (h a) ≡ k (e a)`.
--
-- The diagonal lift `A' → Σ B (Echo f)` exists and is unique up to
-- pointwise equality. Construction: `λ x → h (e⁻¹ x)`. The two
-- triangles (lift ∘ e ≡ h, proj₁ ∘ lift ≡ k) commute pointwise
-- K-free; the strict form is funext-conditional.
--
-- Uniqueness: any other lift `lift'` satisfying the top triangle
-- (lift' ∘ e ≡ h, pointwise) is pointwise equal to the canonical
-- lift. The pointwise uniqueness is K-free; the strict
-- (function-equality) uniqueness is funext-conditional.
--
-- Companion to F5-1 (`EchoOFSUnivF5.echo-factorisation-strict`).
-- Together, F5-1 + F5-2 cover the first two of the three OFS
-- clauses; F5-3 (factorisation uniqueness up to iso) closes the
-- gate.
--
-- Not wired into `All.agda` / `Smoke.agda` until Gate F5 is
-- recorded as fully passed (F5-1 alone is the partial-pass per the
-- ledger). The module compiles standalone under `--safe --without-K`,
-- zero postulates.
--
-- Headlines (will be pinned when gate fully passes):
--
--   * diagonal-lift                          -- canonical lift, pointwise
--   * diagonal-lift-respects-e               -- top triangle, pointwise
--   * diagonal-lift-projects-to-k            -- bottom triangle, pointwise
--   * diagonal-lift-pointwise-uniq           -- pointwise uniqueness
--   * diagonal-lift-respects-e-strict        -- top triangle, given funext
--   * diagonal-lift-projects-to-k-strict     -- bottom triangle, given funext
--   * diagonal-lift-strict-uniq              -- function-level uniqueness, given funext

module EchoOFSUnivF5Diag where

open import Echo                              using (Echo)
open import EchoLossTaxonomy                  using (HasInverse)
open import EchoOFSUnivF5                     using (FunExt₀)

open import Data.Product.Base                 using (Σ; _,_; proj₁; proj₂)
open import Function.Base                     using (_∘_)
open import Relation.Binary.PropositionalEquality
                                              using (_≡_; refl; sym; trans; cong)

----------------------------------------------------------------------
-- Pointwise (K-free) content.
--
-- All four pointwise theorems live in this module, parameterised by
-- the diagonal-square data. Construction: `lift x = h (e⁻¹ x)`,
-- using the inverse from `HasInverse e`.
----------------------------------------------------------------------

module Pointwise
  {A A' B : Set}
  (f : A → B)
  (e : A → A')
  (e-inv : HasInverse e)
  (h : A → Σ B (Echo f))
  (k : A' → B)
  (square : ∀ a → proj₁ (h a) ≡ k (e a))
  where

  open HasInverse e-inv renaming (inv to e⁻¹; f-inv to e-f-inv; inv-f to e-inv-f)

  ----------------------------------------------------------------------
  -- The canonical diagonal lift.
  ----------------------------------------------------------------------

  diagonal-lift : A' → Σ B (Echo f)
  diagonal-lift x = h (e⁻¹ x)

  ----------------------------------------------------------------------
  -- Top triangle: lift ∘ e ≡ h, pointwise.
  --
  -- `lift (e a) = h (e⁻¹ (e a)) = h a` using `e-inv-f a : e⁻¹ (e a) ≡ a`
  -- and `cong h`.
  ----------------------------------------------------------------------

  diagonal-lift-respects-e : ∀ a → diagonal-lift (e a) ≡ h a
  diagonal-lift-respects-e a = cong h (e-inv-f a)

  ----------------------------------------------------------------------
  -- Bottom triangle: proj₁ ∘ lift ≡ k, pointwise.
  --
  -- `proj₁ (lift x) = proj₁ (h (e⁻¹ x))`. The `square` at `e⁻¹ x`
  -- gives `proj₁ (h (e⁻¹ x)) ≡ k (e (e⁻¹ x))`. Then `e-f-inv x : e
  -- (e⁻¹ x) ≡ x` and `cong k`.
  ----------------------------------------------------------------------

  diagonal-lift-projects-to-k : ∀ x → proj₁ (diagonal-lift x) ≡ k x
  diagonal-lift-projects-to-k x =
    trans (square (e⁻¹ x)) (cong k (e-f-inv x))

  ----------------------------------------------------------------------
  -- Pointwise uniqueness.
  --
  -- Any `lift' : A' → Σ B (Echo f)` satisfying the top triangle
  -- pointwise (`lift'-respects-e : ∀ a → lift' (e a) ≡ h a`) is
  -- pointwise equal to `diagonal-lift`.
  --
  -- Proof: `lift' x ≡ lift' (e (e⁻¹ x))` by `cong lift' (sym (e-f-inv x))`,
  -- then `lift'-respects-e (e⁻¹ x) : lift' (e (e⁻¹ x)) ≡ h (e⁻¹ x)
  -- = diagonal-lift x`.
  ----------------------------------------------------------------------

  diagonal-lift-pointwise-uniq :
    (lift' : A' → Σ B (Echo f)) →
    (lift'-respects-e : ∀ a → lift' (e a) ≡ h a) →
    ∀ x → lift' x ≡ diagonal-lift x
  diagonal-lift-pointwise-uniq lift' lift'-respects-e x =
    trans (cong lift' (sym (e-f-inv x))) (lift'-respects-e (e⁻¹ x))

----------------------------------------------------------------------
-- Strict (function-level) content, parameterised by funext.
--
-- The three pointwise theorems above lift to function equations via
-- the supplied `funext`. Three one-liners, same as F4 / F5-1.
----------------------------------------------------------------------

module Strict (funext : FunExt₀) where

  open Pointwise

  diagonal-lift-respects-e-strict :
    {A A' B : Set}
    (f : A → B)
    (e : A → A')
    (e-inv : HasInverse e)
    (h : A → Σ B (Echo f))
    (k : A' → B)
    (square : ∀ a → proj₁ (h a) ≡ k (e a)) →
    diagonal-lift f e e-inv h k square ∘ e ≡ h
  diagonal-lift-respects-e-strict f e e-inv h k square =
    funext (diagonal-lift-respects-e f e e-inv h k square)

  diagonal-lift-projects-to-k-strict :
    {A A' B : Set}
    (f : A → B)
    (e : A → A')
    (e-inv : HasInverse e)
    (h : A → Σ B (Echo f))
    (k : A' → B)
    (square : ∀ a → proj₁ (h a) ≡ k (e a)) →
    proj₁ ∘ diagonal-lift f e e-inv h k square ≡ k
  diagonal-lift-projects-to-k-strict f e e-inv h k square =
    funext (diagonal-lift-projects-to-k f e e-inv h k square)

  diagonal-lift-strict-uniq :
    {A A' B : Set}
    (f : A → B)
    (e : A → A')
    (e-inv : HasInverse e)
    (h : A → Σ B (Echo f))
    (k : A' → B)
    (square : ∀ a → proj₁ (h a) ≡ k (e a))
    (lift' : A' → Σ B (Echo f))
    (lift'-respects-e : ∀ a → lift' (e a) ≡ h a) →
    lift' ≡ diagonal-lift f e e-inv h k square
  diagonal-lift-strict-uniq f e e-inv h k square lift' lift'-respects-e =
    funext (diagonal-lift-pointwise-uniq f e e-inv h k square lift' lift'-respects-e)

----------------------------------------------------------------------
-- Companion remark.
--
-- This module proves the diagonal lifting property at the K-free
-- pointwise level + the funext-qualified strict level. The
-- diagonal-square data is parametric in `f, e, h, k, square` so
-- consumers can instantiate at any concrete diagonal square.
--
-- The HasInverse data on `e` is the QUASI-INVERSE shape from
-- `EchoLossTaxonomy.HasInverse` — strictly weaker than a coherent
-- equivalence in HoTT terms, but sufficient for the K-free /
-- funext-strict pair here. A coherent-equivalence upgrade
-- (half-adjoint with a triangle identity) would let some of the
-- path-algebra in F5-3 (factorisation uniqueness up to iso) close
-- without funext on the coherence side; this slice does not require
-- it.
--
-- Honest scope. Pointwise existence + pointwise uniqueness +
-- strict-given-funext for both. The diagonal lifting property as
-- categorically stated (in a 2-category enriched over groupoids,
-- with the diagonal's iso to the canonical lift) requires more
-- structure than is named here; this slice ships the function-level
-- form that the F4 template authorises.
----------------------------------------------------------------------
