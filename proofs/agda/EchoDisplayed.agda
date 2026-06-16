{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoDisplayed — the displayed-type / fibration packaging of the
-- categorical base, a faithful Agda mirror of typed-wasm's Idris
-- `TypedWasm.ABI.Echo` Displayed / DispHom / idDispHom / fromHomOver.
--
-- This module packages the SAME categorical base that `Echo.agda`
-- already provides (`Echo`, `MapOver`, `map-over`, `map-over-id`,
-- `map-over-comp`) in the fibrational view that the Idris file carries
-- but `Echo.agda` does not yet name:
--
--   * `Displayed B`   — a displayed type over B (a type family /
--     fibration `B → Set`). Mirrors Idris `Displayed b = b -> Type`.
--   * `DispHom p q v` — a morphism of displayed types over a base map
--     `v : B → B'`: a fibrewise family `p b → q (v b)`. Mirrors the
--     Idris `record DispHom`.
--   * `idDispHom p`   — the identity displayed morphism over the
--     identity base. Mirrors Idris `idDispHom`.
--   * `fromHomOver`   — the bridge turning a slice `MapOver` into a
--     `DispHom` between the two fibre displayed-types over the identity
--     base. Mirrors Idris `fromHomOver`, which is built from `echoMap`
--     (= Agda `map-over`).
--
-- HONESTY SCOPE (owner directive). This is PURELY the displayed-type /
-- fibration packaging of the categorical base. It asserts NOTHING about
-- variance, and does NOT reintroduce any graded-comonad /
-- universal-property / model-independence claim — those were RETRACTED;
-- see docs/retractions.adoc R-2026-05-18. The laws proved here are only:
-- the identity displayed morphism acts as the identity; `fromHomOver` is
-- well-defined (its action is exactly `map-over` by construction); and
-- `fromHomOver` is compatible with the existing `map-over` laws
-- (identity and composition), all over the identity base.

module EchoDisplayed where

open import Level using (Level; _⊔_; suc)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Echo
  using (Echo; MapOver; map-over; map-over-id; map-over-comp)

----------------------------------------------------------------------
-- Displayed types (fibrations / type families)
--
-- Mirrors Idris `Displayed : Type -> Type ; Displayed b = b -> Type`.
-- We carry an explicit fibre-level `ℓ'` so the fibres may live at any
-- universe (the Idris version is implicitly large-universe-polymorphic).

Displayed : ∀ {b} (B : Set b) (ℓ' : Level) → Set (b ⊔ suc ℓ')
Displayed B ℓ' = B → Set ℓ'

----------------------------------------------------------------------
-- Morphisms of displayed types over a base map
--
-- Mirrors the Idris
--   record DispHom (p : Displayed B) (q : Displayed B') (v : B -> B') where
--     constructor MkDispHom
--     dispMap : {0 b : B} -> p b -> q (v b)

record DispHom
  {b b' ℓp ℓq} {B : Set b} {B' : Set b'}
  (p : Displayed B ℓp) (q : Displayed B' ℓq)
  (v : B → B') : Set (b ⊔ ℓp ⊔ ℓq) where
  constructor MkDispHom
  field
    dispMap : {x : B} → p x → q (v x)

open DispHom public

----------------------------------------------------------------------
-- Identity displayed morphism over the identity base
--
-- Mirrors Idris `idDispHom p = MkDispHom (\x => x)`.

idDispHom :
  ∀ {b ℓp} {B : Set b} (p : Displayed B ℓp) → DispHom p p id
idDispHom _ = MkDispHom (λ x → x)

----------------------------------------------------------------------
-- The fibre of a map, packaged as a displayed type
--
-- Mirrors Idris `EchoOf f = Echo f : Displayed B`.

EchoOf :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Displayed B (a ⊔ b)
EchoOf f = Echo f

----------------------------------------------------------------------
-- The bridge: a slice MapOver induces a DispHom over the identity base
--
-- Mirrors Idris `fromHomOver h = MkDispHom (\e => echoMap h e)`, where
-- the Idris `echoMap` is exactly the Agda `map-over` (both transport a
-- fibre element along a slice morphism over the fixed base).

fromHomOver :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  MapOver f f' → DispHom (EchoOf f) (EchoOf f') id
fromHomOver m = MkDispHom (λ e → map-over m e)

----------------------------------------------------------------------
-- LAWS
----------------------------------------------------------------------

-- Law 1. The identity displayed morphism acts as the identity on every
-- fibre element. (Holds definitionally; pinned as a named theorem.)
idDispHom-acts-id :
  ∀ {b ℓp} {B : Set b} (p : Displayed B ℓp)
  {x : B} (px : p x) →
  dispMap (idDispHom p) px ≡ px
idDispHom-acts-id _ _ = refl

-- Law 2. `fromHomOver` is well-defined: its fibrewise action is exactly
-- the existing `map-over`. This is the compatibility statement that
-- pins the bridge to the already-verified slice action — there is no
-- second, divergent definition. (Holds by construction; pinned.)
fromHomOver-action :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B}
  (m : MapOver f f') {y : B} (e : Echo f y) →
  dispMap (fromHomOver {f = f} {f' = f'} m) e ≡ map-over {f = f} {f' = f'} m e
fromHomOver-action _ _ = refl

-- Law 3. Compatibility of `fromHomOver` with the identity `map-over`
-- law: the displayed morphism induced by the identity slice morphism
-- agrees, on every fibre element, with the identity displayed morphism
-- on the fibre displayed-type. This is `map-over-id` transported across
-- the bridge.
fromHomOver-id :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B} (e : Echo f y) →
  dispMap (fromHomOver {f = f} {f' = f} (id , (λ x → refl))) e
    ≡ dispMap (idDispHom (EchoOf f)) e
fromHomOver-id e = map-over-id e

-- Law 4. Compatibility of `fromHomOver` with the composition
-- `map-over` law. The Idris `DispHom` over the identity base is closed
-- under fibrewise composition; the bridge sends the composite slice
-- morphism to the composite of the two induced displayed morphisms,
-- pointwise on each fibre. This is `map-over-comp` transported across
-- the bridge (stated on the underlying MapOver Σ-data, matching the way
-- `map-over-comp` is phrased in `Echo.agda`).
fromHomOver-comp :
  ∀ {a a' a'' b}
  {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
  {f : A → B} {f' : A' → B} {f'' : A'' → B}
  (u1 : A → A') (c1 : ∀ x → f' (u1 x) ≡ f x)
  (u2 : A' → A'') (c2 : ∀ x → f'' (u2 x) ≡ f' x)
  {y : B} (e : Echo f y) →
  dispMap (fromHomOver {f = f} {f' = f''}
            (u2 ∘ u1 , (λ x → trans (c2 (u1 x)) (c1 x)))) e
  ≡ dispMap (fromHomOver {f = f'} {f' = f''} (u2 , c2))
      (dispMap (fromHomOver {f = f} {f' = f'} (u1 , c1)) e)
fromHomOver-comp u1 c1 u2 c2 e = map-over-comp u1 c1 u2 c2 e
