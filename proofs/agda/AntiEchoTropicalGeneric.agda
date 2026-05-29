{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- AntiEchoTropicalGeneric — generic-codomain lift of
-- `AntiEchoTropical.agda`'s tropical decomposition.
--
-- The concrete module `AntiEchoTropical.agda` works on the specific
-- candidate scoring `score : Candidate → ℕ`. This module lifts the
-- same decomposition to *any* ordered codomain interface — a carrier
-- `B`, an order `_≤_`, a strict order `_<_`, the bound-against-strict
-- conversion `≤⇒¬<` (always available), and the not-strict-below
-- conversion `¬<⇒≤` (the decidability content; concretely
-- `Data.Nat.Properties.¬<⇒≥`-shape, but ANY witness suffices).
--
-- Three theorems land over the interface:
--   * `antiecho-tropical-decompose-gen` — Σ-reshape iso; structural,
--     `refl` round-trips, does *not* need the order at all.
--   * `optimality-iso-gen` — `(∀ z → y ≤ s z)` ↔ `(∀ z → s z < y → ⊥)`,
--     using `≤⇒¬<` / `¬<⇒≤` from the interface.
--   * `tropdecomp-antiecho-to-gen` / `-from-gen` — the composite
--     `TropEcho-like ↔ Echo × Π-of-AntiEcho-flavoured-misses`.
--
-- Scope. The Σ-shapes for `IsArgmin-like` and `TropEcho-like` are
-- replayed locally over the interface (`IsArgminG` and `TropEchoG`)
-- because the concrete `IsArgmin` / `TropEcho` in `EchoTropical.agda`
-- are pinned to `Candidate → ℕ`. The concrete module is *unchanged*
-- and remains the canonical landing for the ℕ-scored case; this
-- module is the abstract sibling, not a replacement.
--
-- The original concrete module discharged the obligation comment
-- "a generic-codomain version is deferred (would need a `≤`-bearing
-- ordered codomain)" — that obligation is now landed here.

module AntiEchoTropicalGeneric where

open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo using (Echo)

----------------------------------------------------------------------
-- Ordered codomain interface.
--
-- The minimum structure needed to land the tropical decomposition at
-- a generic codomain. `B` is the codomain carrier; `_≤_` is the bound
-- relation used on the optimality side; `_<_` is the strict order
-- used in the AntiEcho-flavoured restatement; `≤⇒¬<` and `¬<⇒≤` are
-- the two order conversions. Note that `¬<⇒≤` is the entire content
-- of the "decidable order" hypothesis in the concrete ℕ case —
-- factored out here as a field rather than baked into the codomain.

record OrderedCodomain : Set₁ where
  field
    B    : Set
    _≤_  : B → B → Set
    _<_  : B → B → Set
    ≤⇒¬< : ∀ {y n : B} → y ≤ n → n < y → ⊥
    ¬<⇒≤ : ∀ {y n : B} → (n < y → ⊥) → y ≤ n

----------------------------------------------------------------------
-- The generic decomposition, parameterised by `OrderedCodomain` and
-- an abstract scoring function `s : C → B` from any candidate set to
-- the ordered codomain.

module Generic (OC : OrderedCodomain) where
  open OrderedCodomain OC

  -- Re-introduce the Σ-shapes locally over the abstract codomain.
  -- These mirror `EchoTropical.IsArgmin` / `TropEcho` exactly, with
  -- `Candidate → ℕ` replaced by an arbitrary `s : C → B`.

  IsArgminG : ∀ {C : Set} (s : C → B) → C → B → Set
  IsArgminG s x y = s x ≡ y × (∀ z → y ≤ s z)

  TropEchoG : ∀ {C : Set} (s : C → B) → B → Set
  TropEchoG {C = C} s y = Σ C (λ x → IsArgminG s x y)

  ------------------------------------------------------------------
  -- The structural decomposition.  Pure Σ-reshape; the order is not
  -- used.  Both round-trips `refl`.

  antiecho-tropical-decompose-gen-to :
    ∀ {C : Set} {s : C → B} {y : B} →
    TropEchoG s y → Echo s y × (∀ z → y ≤ s z)
  antiecho-tropical-decompose-gen-to (x , p , bnd) = (x , p) , bnd

  antiecho-tropical-decompose-gen-from :
    ∀ {C : Set} {s : C → B} {y : B} →
    Echo s y × (∀ z → y ≤ s z) → TropEchoG s y
  antiecho-tropical-decompose-gen-from ((x , p) , bnd) = x , p , bnd

  antiecho-tropical-decompose-gen-to-from :
    ∀ {C : Set} {s : C → B} {y : B}
    (r : Echo s y × (∀ z → y ≤ s z)) →
    antiecho-tropical-decompose-gen-to
      (antiecho-tropical-decompose-gen-from r) ≡ r
  antiecho-tropical-decompose-gen-to-from ((x , p) , bnd) = refl

  antiecho-tropical-decompose-gen-from-to :
    ∀ {C : Set} {s : C → B} {y : B}
    (t : TropEchoG s y) →
    antiecho-tropical-decompose-gen-from
      (antiecho-tropical-decompose-gen-to t) ≡ t
  antiecho-tropical-decompose-gen-from-to (x , p , bnd) = refl

  antiecho-tropical-decompose-gen :
    ∀ {C : Set} (s : C → B) (y : B) →
    TropEchoG s y ↔ (Echo s y × (∀ z → y ≤ s z))
  antiecho-tropical-decompose-gen s y =
    mk↔ₛ′
      (λ t → antiecho-tropical-decompose-gen-to   {s = s} {y = y} t)
      (λ r → antiecho-tropical-decompose-gen-from {s = s} {y = y} r)
      (λ r → antiecho-tropical-decompose-gen-to-from {s = s} {y = y} r)
      (λ t → antiecho-tropical-decompose-gen-from-to {s = s} {y = y} t)

  ------------------------------------------------------------------
  -- AntiEcho-flavoured restatement of the optimality factor.  The
  -- forward direction uses `≤⇒¬<` (always available); the backward
  -- uses `¬<⇒≤` (the decidability content of the interface).

  optimality-as-antiecho-flavour-gen-to :
    ∀ {C : Set} {s : C → B} {y : B} →
    (∀ z → y ≤ s z) → (∀ z → s z < y → ⊥)
  optimality-as-antiecho-flavour-gen-to bnd z lt = ≤⇒¬< (bnd z) lt

  optimality-as-antiecho-flavour-gen-from :
    ∀ {C : Set} {s : C → B} {y : B} →
    (∀ z → s z < y → ⊥) → (∀ z → y ≤ s z)
  optimality-as-antiecho-flavour-gen-from no-miss z = ¬<⇒≤ (no-miss z)

  ------------------------------------------------------------------
  -- Composite: TropEchoG ↔ Echo × (Π-of-AntiEcho-flavoured-misses).
  -- Forward + backward only, no extensionality on the Π factor (the
  -- two Π-shaped sides are not propositionally equal in general
  -- without funext; we keep them as a section/retraction pair, which
  -- is what the concrete module already does).

  tropdecomp-antiecho-gen-to :
    ∀ {C : Set} {s : C → B} {y : B} →
    TropEchoG s y → Echo s y × (∀ z → s z < y → ⊥)
  tropdecomp-antiecho-gen-to t
    with antiecho-tropical-decompose-gen-to t
  ... | (e , bnd) = e , optimality-as-antiecho-flavour-gen-to bnd

  tropdecomp-antiecho-gen-from :
    ∀ {C : Set} {s : C → B} {y : B} →
    Echo s y × (∀ z → s z < y → ⊥) → TropEchoG s y
  tropdecomp-antiecho-gen-from (e , no-miss) =
    antiecho-tropical-decompose-gen-from
      (e , optimality-as-antiecho-flavour-gen-from no-miss)

----------------------------------------------------------------------
-- Sanity instance: the natural numbers.  Builds an `OrderedCodomain`
-- record at ℕ with the same `≤⇒¬<` / `¬<⇒≤` lemmas the concrete
-- `AntiEchoTropical.agda` uses internally.  Pinned so the interface
-- is demonstrably inhabitable; downstream users can build their own
-- instances at other ordered codomains (e.g. `Float`, integers,
-- abstract semirings) without modifying this module.

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥-elim)

private
  ℕ-≤⇒¬< : ∀ {y n : ℕ} → y ≤ n → n < y → ⊥
  ℕ-≤⇒¬< z≤n     ()
  ℕ-≤⇒¬< (s≤s p) (s≤s q) = ℕ-≤⇒¬< p q

  ℕ-¬<⇒≤ : ∀ {y n : ℕ} → (n < y → ⊥) → y ≤ n
  ℕ-¬<⇒≤ {y = zero}  _    = z≤n
  ℕ-¬<⇒≤ {y = suc _} {n = zero}  ¬p = ⊥-elim (¬p (s≤s z≤n))
  ℕ-¬<⇒≤ {y = suc _} {n = suc _} ¬p = s≤s (ℕ-¬<⇒≤ (λ q → ¬p (s≤s q)))

ℕ-ordered-codomain : OrderedCodomain
ℕ-ordered-codomain = record
  { B    = ℕ
  ; _≤_  = _≤_
  ; _<_  = _<_
  ; ≤⇒¬< = ℕ-≤⇒¬<
  ; ¬<⇒≤ = ℕ-¬<⇒≤
  }
