{-# OPTIONS --safe --without-K #-}

-- Pillar C of docs/echo-types/establishment-plan.adoc.
--
-- REAL MODULE (separating model landed 2026-05-17).
--
-- Goal: a SEPARATING MODEL. The only objection every referee raises
-- is "isn't this all Σ-lemmas with renamed components?" The
-- gold-standard answer is a model in which the *generic* Σ/Echo
-- functoriality laws (`Echo.map-over-id` / `map-over-comp`) still
-- hold, yet the *characteristic* loss-grade composition law
-- `EchoGraded.degrade-compose` (equivalently `degrade-via-join`)
-- FAILS — at a concrete, decidable witness. That proves the graded
-- family is genuine structure, not bookkeeping.
--
-- The precise pin. `EchoGraded.degrade-compose` holds for exactly
-- one reason: `≤g-prop` — the loss order `_≤g_` is propositional, so
-- the chosen factoring `p12 ∙ p23` and the direct `p13` are forced
-- equal, and `degrade-comp` then closes it. This model is `EchoGraded`
-- with that single hypothesis removed: a "loss order" `_⊑_` with TWO
-- distinct arrows `s₀ , s₁ : lo ⊑ hi` (so `sep-order-not-prop`), a
-- reindexing `deg` that distinguishes them (`s₀ ↦ id`, `s₁ ↦ not`).
-- Nothing else changes; in particular the Σ/`map-over` layer is the
-- *same generic layer* and its laws still hold here (`sep-map-over-*`).
-- The path-independence law breaks (`sep-degrade-compose-fails`).
--
-- This continues the negative-exhibit discipline of
-- `characteristic/VisibleConstraintAudit.agda` /
-- `characteristic/IntegrationAudit.agda` (collapsing pseudo-theorems
-- to `proj₂`), but in the positive direction: an explicit
-- countermodel object, with the failure a checked `true ≢ false`.

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
-- The characteristic law FAILS.
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
