{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Walking parallel-arrow category with a lawful pointwise action.
-- Its two distinct lo → hi arrows act by identity and Boolean negation.
-- sep-compose and sep-deg-comp prove composition is functorial.
-- SepDegradeCompose instead compares a composite with an arbitrary direct
-- arrow: sep-degrade-compose-fails refutes that arrow-independence claim.
-- The ordinary Sigma/Echo map-over laws continue to hold. This separates
-- thinness-dependent path independence from ordinary functoriality; it
-- does not refute functoriality or category composition without thinness.

module EchoSeparating where

open import Echo using (Echo; MapOver; map-over; map-over-id; map-over-comp)
open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

----------------------------------------------------------------------
-- The model: `EchoGraded` minus `≤g-prop`.
--
-- Two grades and a NON-propositional loss order — two distinct
-- arrows from `lo` to `hi`. (Contrast `EchoGraded._≤g_`, where
-- `≤g-prop` makes every hom a singleton.)

data G : Set where
  lo hi : G

data _⊑_ : G → G → Set where
  rfl-lo : lo ⊑ lo
  rfl-hi : hi ⊑ hi
  s₀ s₁  : lo ⊑ hi          -- two distinct lo→hi arrows: not a prop

-- Grade-indexed carrier (mirrors `EchoGraded.GEcho`).
Obj : G → Set
Obj lo = Bool
Obj hi = Bool

-- Reindexing along the loss order (mirrors `EchoGraded.degrade`).
-- The two lo→hi arrows act differently — this is the whole point.
deg : ∀ {g₁ g₂} → g₁ ⊑ g₂ → Obj g₁ → Obj g₂
deg rfl-lo b = b
deg rfl-hi b = b
deg s₀     b = b
deg s₁     b = not b

-- Ordinary composition retains the choice of parallel arrow. It does
-- not identify an arbitrary direct arrow with the chosen composite.
sep-id : (g : G) → g ⊑ g
sep-id lo = rfl-lo
sep-id hi = rfl-hi

sep-compose : ∀ {g₁ g₂ g₃} → g₁ ⊑ g₂ → g₂ ⊑ g₃ → g₁ ⊑ g₃
sep-compose rfl-lo rfl-lo = rfl-lo
sep-compose rfl-lo s₀ = s₀
sep-compose rfl-lo s₁ = s₁
sep-compose s₀ rfl-hi = s₀
sep-compose s₁ rfl-hi = s₁
sep-compose rfl-hi rfl-hi = rfl-hi

sep-compose-idˡ : ∀ {g₁ g₂} (p : g₁ ⊑ g₂) →
  sep-compose (sep-id g₁) p ≡ p
sep-compose-idˡ rfl-lo = refl
sep-compose-idˡ rfl-hi = refl
sep-compose-idˡ s₀ = refl
sep-compose-idˡ s₁ = refl

sep-compose-idʳ : ∀ {g₁ g₂} (p : g₁ ⊑ g₂) →
  sep-compose p (sep-id g₂) ≡ p
sep-compose-idʳ rfl-lo = refl
sep-compose-idʳ rfl-hi = refl
sep-compose-idʳ s₀ = refl
sep-compose-idʳ s₁ = refl

sep-compose-assoc : ∀ {g₁ g₂ g₃ g₄}
  (p : g₁ ⊑ g₂) (q : g₂ ⊑ g₃) (r : g₃ ⊑ g₄) →
  sep-compose (sep-compose p q) r ≡ sep-compose p (sep-compose q r)
sep-compose-assoc rfl-lo rfl-lo rfl-lo = refl
sep-compose-assoc rfl-lo rfl-lo s₀ = refl
sep-compose-assoc rfl-lo rfl-lo s₁ = refl
sep-compose-assoc rfl-lo s₀ rfl-hi = refl
sep-compose-assoc rfl-lo s₁ rfl-hi = refl
sep-compose-assoc s₀ rfl-hi rfl-hi = refl
sep-compose-assoc s₁ rfl-hi rfl-hi = refl
sep-compose-assoc rfl-hi rfl-hi rfl-hi = refl

-- Pointwise action laws need no equality principle for functions.
sep-deg-id : ∀ g (e : Obj g) → deg (sep-id g) e ≡ e
sep-deg-id lo e = refl
sep-deg-id hi e = refl

sep-deg-comp : ∀ {g₁ g₂ g₃}
  (p : g₁ ⊑ g₂) (q : g₂ ⊑ g₃) (e : Obj g₁) →
  deg q (deg p e) ≡ deg (sep-compose p q) e
sep-deg-comp rfl-lo rfl-lo e = refl
sep-deg-comp rfl-lo s₀ e = refl
sep-deg-comp rfl-lo s₁ e = refl
sep-deg-comp s₀ rfl-hi e = refl
sep-deg-comp s₁ rfl-hi e = refl
sep-deg-comp rfl-hi rfl-hi e = refl

sep-parallel-actions-distinct : ¬ (deg s₀ true ≡ deg s₁ true)
sep-parallel-actions-distinct ()

----------------------------------------------------------------------
-- The loss order here is NOT propositional. This is the *single*
-- hypothesis whose presence (`EchoGraded.≤g-prop`) makes
-- `degrade-compose` true and whose absence breaks it below.

sep-order-not-prop : ¬ (s₀ ≡ s₁)
sep-order-not-prop ()

-- The functorial UNIT law still holds (the generic graded-structure
-- part is untouched): identity arrows reindex by the identity.
sep-deg-unit-lo : (b : Obj lo) → deg rfl-lo b ≡ b
sep-deg-unit-lo _ = refl

sep-deg-unit-hi : (b : Obj hi) → deg rfl-hi b ≡ b
sep-deg-unit-hi _ = refl

----------------------------------------------------------------------
-- Generic Σ/Echo functoriality STILL HOLDS in this model.
--
-- Instantiate the generic `Echo` machinery at a model map (the
-- `s₁`-action `not`, viewed as a `MapOver` over the point base `⊤`).
-- `map-over-id` / `map-over-comp` hold here verbatim — they are the
-- model-independent Σ laws, and this model is a bona-fide Echo
-- setting. Only the *grade* law (next section) is what fails.

sep-f : Bool → ⊤
sep-f _ = tt

sep-MO : MapOver sep-f sep-f
sep-MO = not , (λ _ → refl)

sep-map-over-id :
  (e : Echo sep-f tt) → map-over (id , (λ _ → refl)) e ≡ e
sep-map-over-id = map-over-id

sep-map-over-comp :
  (e : Echo sep-f tt) →
  map-over ((not ∘ not) , (λ _ → trans refl refl)) e
  ≡ map-over sep-MO (map-over sep-MO e)
sep-map-over-comp e = map-over-comp not (λ _ → refl) not (λ _ → refl) e

----------------------------------------------------------------------
-- Independence from an arbitrary direct arrow FAILS.
--
-- `SepDegradeCompose` is `EchoGraded.degrade-compose` transcribed
-- with `_⊑_` / `deg` for `_≤g_` / `degrade`. It is refuted at the
-- concrete witness g₁=lo, g₂=lo, g₃=hi, p₁₂=rfl-lo, p₂₃=s₀, p₁₃=s₁,
-- e=true:  deg s₀ (deg rfl-lo true) = true,  deg s₁ true = false.

SepDegradeCompose : Set
SepDegradeCompose =
  ∀ {g₁ g₂ g₃}
  (p₁₂ : g₁ ⊑ g₂) (p₂₃ : g₂ ⊑ g₃) (p₁₃ : g₁ ⊑ g₃) (e : Obj g₁) →
  deg p₂₃ (deg p₁₂ e) ≡ deg p₁₃ e

true≢false : ¬ (true ≡ false)
true≢false ()

sep-degrade-compose-fails : ¬ SepDegradeCompose
sep-degrade-compose-fails law = true≢false (law rfl-lo s₀ s₁ true)

-- Conclusion (for the establishment plan). The generic Σ-functoriality
-- laws (`sep-map-over-id` / `sep-map-over-comp`) and the functorial
-- unit (`sep-deg-unit-*`) hold in this model exactly as in
-- `EchoGraded`; the only difference is `sep-order-not-prop` (no
-- `≤g-prop`), and that alone is enough to refute the characteristic
-- composition law. Therefore `EchoGraded.degrade-compose` is NOT a
-- generic Σ-consequence — it is carried precisely by propositionality
-- of the loss order. The graded-loss structure is real.
