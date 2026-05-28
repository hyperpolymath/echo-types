{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Gate F5 third slice (docs/echo-types/earn-back-plan.adoc §"Gate
-- F5 — Full OFS, honestly qualified").
--
-- Factorisation uniqueness up to isomorphism. Same F4 template as
-- F5-1 / F5-2: pointwise (K-free) form lands unconditionally;
-- strict (function-level) form lifts via an explicit funext
-- parameter.
--
-- *Setup.* Given any second (equivalence, projection) factorisation
-- `f = p ∘ g` with `g : A → X` an equivalence (via `HasInverse`)
-- and `p : X → B`, exhibit a canonical iso `φ : X ↔ Σ B (Echo f)`
-- such that the two factorisations commute (after funext lifting):
--
--   * `φ.to ∘ g ≡ encode f`  (top equation, strict given funext)
--   * `proj₁ ∘ φ.to ≡ p`    (bottom equation, strict given funext)
--
-- *Design note.* The natural first attempt — defining
-- `φ.to x = (p x, inv x, witness x)` with `witness` packaging the
-- commute data — surfaces a half-adjoint triangle-identity
-- obligation in the round-trip `φ.to ∘ φ.from`, requiring `cong g
-- (inv-f a) ≡ f-inv (g a)` to close.  The cleaner construction
-- factors through the existing totality completion:
--
--     φ.to    = encode f ∘ inv
--     φ.from  = g ∘ decode f
--
-- Round-trips reduce via existing K-free lemmas:
--
--     φ.from ∘ φ.to    = g ∘ (decode f ∘ encode f) ∘ inv
--                      ≡ g ∘ inv              (by `decode-encode`)
--                      ≡ id                   (by `f-inv`)
--
--     φ.to ∘ φ.from    = encode f ∘ (inv ∘ g) ∘ decode f
--                      ≡ encode f ∘ decode f  (by `inv-f` + cong)
--                      ≡ id                   (by `encode-decode`)
--
-- The decomposition into `encode-decode` and `decode-encode`
-- eliminates the Σ-equality path-algebra entirely — only
-- `EchoLossTaxonomy.HasInverse` (quasi-inverse), the existing
-- `EchoTotalCompletion` round-trips, and `cong`/`trans` are needed.
--
-- The two commute equations (`φ.to ∘ g ≡ encode f` and
-- `proj₁ ∘ φ.to ≡ p`) similarly reduce pointwise via `inv-f` +
-- `cong (encode f)` on the first, and via `commute` + `f-inv` +
-- `cong p` on the second. Funext lifts both to strict form.
--
-- *Trade-off.* The composed iso has `proj₁ ∘ φ.to ≡ f ∘ inv`
-- definitionally, equal to `p` only via the `commute` coherence
-- (pointwise; strict under funext). The original direct
-- formulation would have `proj₁ ∘ φ.to ≡ p` definitionally but
-- require the triangle identity to close the round-trip. Under
-- the F4 template (funext as explicit parameter), the composed
-- version is strictly cleaner — no extra hypothesis beyond what
-- F4 / F5-1 / F5-2 already use.
--
-- Companion to F5-1 + F5-2; together, the three slices close the
-- full F5 gate at the qualified earn-back level.
--
-- Headlines (will be pinned when full F5 passes):
--
--   * φ-to                                   -- the iso's forward leg
--   * φ-from                                 -- the iso's backward leg
--   * φ-from-to                              -- φ.from ∘ φ.to ≡ id pointwise
--   * φ-to-from                              -- φ.to ∘ φ.from ≡ id pointwise
--   * φ-iso                                  -- packaged as _↔_
--   * φ-respects-g                           -- φ.to ∘ g ≡ encode f pointwise
--   * φ-projects-to-p                        -- proj₁ ∘ φ.to ≡ p pointwise
--   * φ-respects-g-strict                    -- φ.to ∘ g ≡ encode f given funext
--   * φ-projects-to-p-strict                 -- proj₁ ∘ φ.to ≡ p given funext

module EchoOFSUnivF5Iso where

open import Echo                              using (Echo)
open import EchoTotalCompletion               using (encode; decode; decode-encode; encode-decode)
open import EchoLossTaxonomy                  using (HasInverse)
open import EchoOFSUnivF5                     using (FunExt₀)

open import Data.Product.Base                 using (Σ; _,_; proj₁; proj₂)
open import Function.Base                     using (_∘_)
open import Function.Bundles                  using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality
                                              using (_≡_; refl; sym; trans; cong)

----------------------------------------------------------------------
-- Pointwise (K-free) content.
--
-- Parameterised by the second factorisation data: `g : A → X` with
-- `HasInverse g`, `p : X → B`, and `commute : ∀ a → p (g a) ≡ f a`.
-- Construction via composition with `EchoTotalCompletion.A↔ΣEcho`.
----------------------------------------------------------------------

module Pointwise
  {A X B : Set}
  (f : A → B)
  (g : A → X)
  (g-inv : HasInverse g)
  (p : X → B)
  (commute : ∀ a → p (g a) ≡ f a)
  where

  open HasInverse g-inv renaming (inv to g⁻¹; f-inv to g-f-inv; inv-f to g-inv-f)

  ----------------------------------------------------------------------
  -- The canonical iso, constructed by composition.
  --
  --   φ.to    = encode f ∘ g⁻¹
  --   φ.from  = g ∘ decode f
  --
  -- The composed form avoids the half-adjoint coherence obligation
  -- the direct formulation `φ.to x = (p x, g⁻¹ x, witness)` would
  -- incur, by routing through the existing K-free
  -- `encode-decode` / `decode-encode` round-trips.
  ----------------------------------------------------------------------

  φ-to : X → Σ B (Echo f)
  φ-to x = encode f (g⁻¹ x)

  φ-from : Σ B (Echo f) → X
  φ-from z = g (decode f z)

  ----------------------------------------------------------------------
  -- Round-trips. Both close in two lines via the existing
  -- `EchoTotalCompletion` round-trips + `HasInverse`'s inverse data.
  --
  -- `φ-from ∘ φ-to`: `g (decode f (encode f (g⁻¹ x))) ≡ g (g⁻¹ x)`
  -- because `decode-encode f (g⁻¹ x) = refl` definitionally
  -- (decode ∘ encode is the identity on the nose). Then `g (g⁻¹ x)
  -- ≡ x` by `g-f-inv x`.
  ----------------------------------------------------------------------

  φ-from-to : (x : X) → φ-from (φ-to x) ≡ x
  φ-from-to x = g-f-inv x

  ----------------------------------------------------------------------
  -- `φ-to ∘ φ-from`: `encode f (g⁻¹ (g (decode f z))) ≡ encode f
  -- (decode f z)` via `cong (encode f) (g-inv-f (decode f z))`.
  -- Then `encode f (decode f z) ≡ z` by `encode-decode f z`.
  ----------------------------------------------------------------------

  φ-to-from : (z : Σ B (Echo f)) → φ-to (φ-from z) ≡ z
  φ-to-from z =
    trans (cong (encode f) (g-inv-f (decode f z))) (encode-decode f z)

  ----------------------------------------------------------------------
  -- Iso package (stdlib `_↔_`).
  ----------------------------------------------------------------------

  φ-iso : X ↔ Σ B (Echo f)
  φ-iso = mk↔ₛ′ φ-to φ-from φ-to-from φ-from-to

  ----------------------------------------------------------------------
  -- Commute equations (pointwise).
  --
  -- `φ-to ∘ g ≡ encode f`: `φ-to (g a) = encode f (g⁻¹ (g a)) ≡
  -- encode f a` via `cong (encode f) (g-inv-f a)`.
  ----------------------------------------------------------------------

  φ-respects-g : (a : A) → φ-to (g a) ≡ encode f a
  φ-respects-g a = cong (encode f) (g-inv-f a)

  ----------------------------------------------------------------------
  -- `proj₁ ∘ φ-to ≡ p`: `proj₁ (φ-to x) = proj₁ (encode f (g⁻¹ x))
  -- = f (g⁻¹ x)`. Then `f (g⁻¹ x) ≡ p (g (g⁻¹ x)) ≡ p x` via
  -- `sym (commute (g⁻¹ x))` + `cong p (g-f-inv x)`.
  ----------------------------------------------------------------------

  φ-projects-to-p : (x : X) → proj₁ (φ-to x) ≡ p x
  φ-projects-to-p x =
    trans (sym (commute (g⁻¹ x))) (cong p (g-f-inv x))

----------------------------------------------------------------------
-- Strict (function-level) content, parameterised by funext.
--
-- The two commute equations lift via funext, in the F4 / F5-1 /
-- F5-2 one-liner style. The iso itself is already a record
-- (function-level via `mk↔ₛ′`), so its strict form doesn't need
-- funext at all — the pointwise round-trips are the iso's record
-- fields directly.
----------------------------------------------------------------------

module Strict (funext : FunExt₀) where

  open Pointwise

  φ-respects-g-strict :
    {A X B : Set}
    (f : A → B)
    (g : A → X)
    (g-inv : HasInverse g)
    (p : X → B)
    (commute : ∀ a → p (g a) ≡ f a) →
    φ-to f g g-inv p commute ∘ g ≡ encode f
  φ-respects-g-strict f g g-inv p commute =
    funext (φ-respects-g f g g-inv p commute)

  φ-projects-to-p-strict :
    {A X B : Set}
    (f : A → B)
    (g : A → X)
    (g-inv : HasInverse g)
    (p : X → B)
    (commute : ∀ a → p (g a) ≡ f a) →
    proj₁ ∘ φ-to f g g-inv p commute ≡ p
  φ-projects-to-p-strict f g g-inv p commute =
    funext (φ-projects-to-p f g g-inv p commute)

----------------------------------------------------------------------
-- Companion remark.
--
-- F5-3 closes the F5 gate at full pass. The three slices together
-- (F5-1 strict triangle, F5-2 diagonal lifting, F5-3 factorisation
-- uniqueness up to iso) earn back the qualified (equivalence,
-- projection) orthogonal factorisation system on Type, with funext
-- as an explicit parameter throughout (never a postulate).
--
-- The composition design (`φ.to = encode f ∘ g⁻¹`) is strictly
-- cleaner than the direct `(p x, g⁻¹ x, witness)` form because it
-- routes path-algebra through the already-proved K-free
-- `encode-decode` / `decode-encode` round-trips. The cost is that
-- `proj₁ ∘ φ.to ≡ p` is no longer definitional — only pointwise
-- via `commute`. Under the F4 template (funext as parameter), this
-- is the right trade.
--
-- Honest scope. `HasInverse` is a quasi-inverse (not a coherent
-- equivalence in HoTT terms). The composition design lets this
-- slice work with the quasi-inverse data alone; no triangle
-- identity required. A coherent-equivalence upgrade
-- (`HasCoherentInverse` with the triangle identity) would let some
-- of these path-equations become definitional rather than
-- pointwise, but is not load-bearing for F5-3's earn-back. The
-- triangle-identity-strengthened form is a deferred refinement,
-- not a missing piece.
--
-- F5 ledger status after this slice lands: all three slices pass;
-- gate fully closed at the qualified level. `paper.adoc` /
-- `conservativity.adoc` / `types-abstract.adoc` updates +
-- retraction follow-up F-2026-05-27a should land in the same
-- consolidation that wires this module into Smoke/All.
----------------------------------------------------------------------
