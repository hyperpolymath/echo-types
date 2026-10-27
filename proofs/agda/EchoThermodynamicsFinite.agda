{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoThermodynamicsFinite: the Landauer/Bennett bounds, lifted
-- off `Fin n` to *any Bishop-finite carrier*.
--
-- Motivation.
--
-- `EchoThermodynamics` proves the bound *shape* only for
-- `f : Fin n → B`, because the cost functional is routed through
-- `EchoFiberCount.FiberSize-fin`, whose totality is structural
-- recursion on the index bound `n` of `Fin n`. The honest question
-- the C+ rating poses is: *how far past `Fin n → B` does this go?*
--
-- Answer, made precise here:
--
--   * It generalises, with no new axioms, to **every Bishop-finite
--     carrier** `A` — i.e. any `A` equipped with a bijection
--     `A ≃ Fin n`. The bridge is pure transport: precompose with
--     the bijection's `from : Fin n → A`, and the finite-domain
--     results apply verbatim. This module discharges that case.
--
--   * It does **not** generalise to an arbitrary infinite carrier
--     (e.g. `ProgramState = ℕ → ℕ`). That residue is a *stated,
--     falsifiable* obligation — O-THERMO-∞ in
--     `docs/ECHO-CNO-BRIDGE.adoc` §"Thermodynamic Bridge" — not a
--     softened "future work" line. It is recorded there, not
--     postulated here: this module introduces zero postulates and
--     no escape pragmas, exactly like the rest of the suite.
--
-- Headlines (pinned in Smoke.agda):
--
--   * FiniteDomain                     -- Bishop-finite carrier record
--   * fiber-erasure-bound-fin          -- cost for a finite carrier
--   * bennett-reversible-finite        -- injective f on finite A, a hit ⇒ 0
--   * landauer-collapse-finite         -- f collapses onto y ⇒ k·T·⌊log₂ n⌋

module EchoThermodynamicsFinite where

open import Function.Base                         using (_∘_)
import      Data.Nat.Base                         as ℕ
open        ℕ                                     using (ℕ; _*_)
open import Data.Fin.Base                         using (Fin)
open import Data.Nat.Logarithm                    using (⌊log₂_⌋)
open import Relation.Nullary.Decidable.Core       using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import EchoThermodynamics                    using
  ( Temperature
  ; Energy
  ; k
  ; landauer-bound
  ; fiber-erasure-bound
  ; bennett-reversible-injective
  ; landauer-collapse
  )

----------------------------------------------------------------------
-- Bishop-finite carrier
--
-- `A` is Bishop-finite when it is in explicit bijection with some
-- `Fin n`. We carry both round-trips: `from∘to` transports a
-- domain witness onto `Fin n`, and `to∘from` gives injectivity of
-- `from`. No `--without-K`-unsafe content: these are bare
-- propositional equalities.
----------------------------------------------------------------------

record FiniteDomain (A : Set) : Set where
  field
    card   : ℕ
    to     : A → Fin card
    from   : Fin card → A
    from∘to : ∀ a → from (to a) ≡ a
    to∘from : ∀ i → to (from i) ≡ i

open FiniteDomain public

----------------------------------------------------------------------
-- Cost functional for a finite carrier.
--
-- Defined by precomposition with the bijection's `from`, so it is
-- *definitionally* the `Fin card` cost of `f ∘ from`. That
-- definitional identity is what lets the finite-domain proofs apply
-- verbatim, with no transport lemma on the bound itself.
----------------------------------------------------------------------

fiber-erasure-bound-fin :
  ∀ {b} {A : Set} {B : Set b}
  (fd : FiniteDomain A) (f : A → B) (y : B) →
  ((y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  Temperature → Energy
fiber-erasure-bound-fin fd f y _≟_ T =
  fiber-erasure-bound (f ∘ from fd) y _≟_ T

----------------------------------------------------------------------
-- bennett-reversible-finite
--
-- Bennett, off `Fin n`: an injective `f : A → B` on a Bishop-finite
-- carrier `A` that hits `y` at some `a₀` has erasure bound zero at
-- `y`. The two obligations of `bennett-reversible-injective` for
-- `f ∘ from` are discharged by the bijection laws:
--
--   * injectivity of `f ∘ from` = injectivity of `f` ∘ injectivity
--     of `from`, and `from` is injective because `to ∘ from ≡ id`;
--   * the witness index is `to a₀`, with `from∘to` carrying the
--     hit `f a₀ ≡ y` back along the round-trip.
----------------------------------------------------------------------

bennett-reversible-finite :
  ∀ {b} {A : Set} {B : Set b}
  (fd : FiniteDomain A) (f : A → B) (y : B)
  (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂))
  (inj : ∀ {a a′ : A} → f a ≡ f a′ → a ≡ a′)
  (a₀ : A) → f a₀ ≡ y →
  (T : Temperature) →
  fiber-erasure-bound-fin fd f y _≟_ T ≡ 0
bennett-reversible-finite fd f y _≟_ inj a₀ hit T =
  bennett-reversible-injective (f ∘ from fd) y _≟_ g-inj (to fd a₀) g-hit T
  where
    -- `from` is injective: it has a left inverse `to`.
    from-inj : ∀ {i j} → from fd i ≡ from fd j → i ≡ j
    from-inj {i} {j} e =
      trans (sym (to∘from fd i)) (trans (cong (to fd) e) (to∘from fd j))

    g-inj : ∀ {i j} → (f ∘ from fd) i ≡ (f ∘ from fd) j → i ≡ j
    g-inj e = from-inj (inj e)

    g-hit : (f ∘ from fd) (to fd a₀) ≡ y
    g-hit = trans (cong f (from∘to fd a₀)) hit

----------------------------------------------------------------------
-- landauer-collapse-finite
--
-- Worst case off `Fin n`: if `f` collapses the whole Bishop-finite
-- carrier onto `y`, the erasure bound is the full Landauer cost
-- `k · T · ⌊log₂ card⌋`. (`card` is the carrier's bijective size;
-- the bijection makes "how many alternatives were erased" a sharp
-- finite number.)
----------------------------------------------------------------------

landauer-collapse-finite :
  ∀ {b} {A : Set} {B : Set b}
  (fd : FiniteDomain A) (f : A → B) (y : B)
  (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  (∀ a → f a ≡ y) →
  (T : Temperature) →
  fiber-erasure-bound-fin fd f y _≟_ T ≡ k * T * ⌊log₂ card fd ⌋
landauer-collapse-finite fd f y _≟_ h T =
  landauer-collapse (f ∘ from fd) y _≟_ T (λ i → h (from fd i))
