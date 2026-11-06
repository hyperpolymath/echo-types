{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoVariance: fibre composition, retained-witness recovery, and the
-- iterated-product split/merge equivalence. These are the statements below.
-- They do not supply the categorical data for a tropical graded monad.
--
-- The core fibre is standard dependent-sum mathematics. Accumulation and
-- splitting are inverse for specified maps f and g. Total completion has
-- no grade parameter and recovers the source stored in the fibre witness.
-- Its round trips alone are not an adjunction; EchoDependentPushforward
-- supplies the separate dependent-pushforward/reindexing adjunction.
--
-- no-bare-recovery forbids a LEFT inverse of a particular Boolean collapse.
-- It does not forbid graded comonads: EchoErasingGradedComonad gives a
-- natural graded comonad whose positive-grade carriers erase the input.
-- Its counit is required only at the unit grade.
--
-- F1 supplies an iterated-product model. The split/merge inverse laws below
-- do not themselves package a graded monad. Naturality for its graded
-- comonad is certified separately by EchoGradedComonadNaturality and the
-- concrete instance modules. Ordered/tropical compatibility needs its own
-- explicitly specified laws; it is not a consequence of these map shapes.
--
-- Legacy theorem names are retained for API compatibility. The NotProved
-- markers below are unit-valued documentation markers, not theorem proofs.
module EchoVariance where

open import Level using (Level)
open import Function.Base using (_∘_)
open import Function.Bundles using (_↔_)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (¬_)

open import Echo
  using ( Echo
        ; Echo-comp-iso-to ; Echo-comp-iso-from
        ; Echo-comp-iso-from-to ; Echo-comp-iso-to-from )
open import EchoCharacteristic
  using ( collapse ; echo-true ; echo-false ; echo-true≢echo-false )
open import EchoNoSectionGeneric using ( no-section-of-collapsing-map )
open import EchoTotalCompletion using ( A↔ΣEcho )
open import EchoGradedComonadF1 using ( D ; δ ; D-+ ; coe )

private variable
  ℓa ℓb ℓc : Level
  A : Set ℓa
  B : Set ℓb
  C : Set ℓc

----------------------------------------------------------------------
-- (1) COMPOSITION OF FIBRES FOR TWO SPECIFIED MAPS.
--
-- A "nested loss" is an f-echo sitting under a g-step: the layered data
-- `Σ B (λ b → Echo f b × (g b ≡ y))`. `accumulate` composes the two
-- layers into a single (g ∘ f)-echo. It is TOTAL and CANONICAL: it is
-- definable from the layered data alone — the factoring (f, g) is exactly
-- its input — so no choice is made. This is the graded-MONAD
-- multiplication shape, and the loss magnitudes accumulate (the
-- (g ∘ f)-fibre carries both the f-witness and the g-witness).
----------------------------------------------------------------------

accumulate :
  (f : A → B) (g : B → C) {y : C} →
  Σ B (λ b → Echo f b × (g b ≡ y)) → Echo (g ∘ f) y
accumulate f g = Echo-comp-iso-from f g

-- δ for a FIXED factoring (f, g): split the combined echo back into the
-- layered data. Total ONLY because the factoring is supplied as data —
-- contrast (3), where no factoring is given.
split-with-factoring :
  (f : A → B) (g : B → C) {y : C} →
  Echo (g ∘ f) y → Σ B (λ b → Echo f b × (g b ≡ y))
split-with-factoring f g = Echo-comp-iso-to f g

----------------------------------------------------------------------
-- (2) RECOVERABILITY IS EXACT ON THE FIBRE.
--
-- For a FIXED factoring the two maps are mutually inverse — both
-- round-trips are `refl`. A fibre inhabitant retains its chosen source
-- witness and equality proof. No storage-minimality result follows.
----------------------------------------------------------------------

accumulate-split-id :
  (f : A → B) (g : B → C) {y : C} (e : Echo (g ∘ f) y) →
  accumulate f g (split-with-factoring f g e) ≡ e
accumulate-split-id f g = Echo-comp-iso-from-to f g

split-accumulate-id :
  (f : A → B) (g : B → C) {y : C}
  (r : Σ B (λ b → Echo f b × (g b ≡ y))) →
  split-with-factoring f g (accumulate f g r) ≡ r
split-accumulate-id f g = Echo-comp-iso-to-from f g

-- Total completion A ≅ Σ B (Echo f), with no grading parameter.
-- This type equivalence alone is not a categorical adjunction.
recoverable-fibre : (f : A → B) → A ↔ Σ B (Echo f)
recoverable-fibre = A↔ΣEcho

----------------------------------------------------------------------
-- (3) NO INPUT-RECONSTRUCTING LEFT INVERSE FOR BOOLEAN COLLAPSE.
--
-- No raise : ⊤ → Bool satisfies raise ∘ collapse ≡ id. Right inverses
-- do exist. This result is not an obstruction to graded comonads.
----------------------------------------------------------------------

no-bare-recovery :
  ¬ Σ (⊤ → Bool) (λ raise → ∀ b → raise (collapse b) ≡ b)
no-bare-recovery =
  no-section-of-collapsing-map collapse true false (λ ()) refl

-- The fibre nevertheless retains the lost bit EXACTLY: `echo-true` and
-- `echo-false` are distinct echoes over the SAME residue `tt`. The loss
-- witness is retained in each fibre inhabitant; it is absent from the
-- bare output. This explains the different recovery statements.
fibre-retains-lost-bit : echo-true ≢ echo-false
fibre-retains-lost-bit = echo-true≢echo-false

----------------------------------------------------------------------
-- (4) INVERTIBLE SPLIT/MERGE FOR THE SEPARATE ITERATED-PRODUCT MODEL.
--
-- `EchoGradedComonadF1` is a genuine nested graded comonad, but its model
-- `D r A = A × Boolʳ` RETAINS its residue layers. Its comultiplication is
-- `δ = coe (D-+ m n A)` along the TYPE EQUALITY `D (m+n) A ≡ D m (D n A)`,
-- so it is INVERTIBLE. We exhibit the inverse `μ-writer` and prove both
-- round-trips. A corresponding graded-monad package additionally needs
-- naturality, its unit and coherent multiplication laws.
--
-- `μ-writer : D_m (D_n A) → D_{m+n} A` — note the type literally adds the
-- grades m + n; no tropical ordering compatibility is proved here.
----------------------------------------------------------------------

coe-sym : ∀ {X Y : Set} (p : X ≡ Y) (x : X) → coe (sym p) (coe p x) ≡ x
coe-sym refl x = refl

coe-sym′ : ∀ {X Y : Set} (p : X ≡ Y) (y : Y) → coe p (coe (sym p) y) ≡ y
coe-sym′ refl y = refl

μ-writer : ∀ m n {A : Set} → D m (D n A) → D (m + n) A
μ-writer m n {A} = coe (sym (D-+ m n A))

-- μ-writer is a SECTION of F1's δ: combining-then-splitting is the
-- identity. (δ m n = coe (D-+ m n A).)
writer-μ-section :
  ∀ m n {A : Set} (x : D (m + n) A) → μ-writer m n (δ m n x) ≡ x
writer-μ-section m n {A} = coe-sym (D-+ m n A)

-- μ-writer is also a RETRACTION of δ: splitting-then-combining is the
-- identity. Together these show δ is an isomorphism.
writer-δ-section :
  ∀ m n {A : Set} (y : D m (D n A)) → δ m n (μ-writer m n y) ≡ y
writer-δ-section m n {A} = coe-sym′ (D-+ m n A)

----------------------------------------------------------------------
-- Honest scope. Matched-negatives as ⊤-aliases (so `grep NotProved`
-- catches them). The verdict is about the SHAPE of the canonical
-- structure maps and the LOCUS of recoverability — not a universal
-- categorical impossibility theorem.
----------------------------------------------------------------------

-- Compatibility marker only. No universal obstruction is proved here;
-- EchoErasingGradedComonad explicitly permits positive-grade loss.
NotProved-no-graded-comonad-of-any-kind : Set
NotProved-no-graded-comonad-of-any-kind = ⊤

-- NOT claimed: a numeric realisation of the min-plus grade semiring with
-- ∞ and the full graded-monad law triangle. The MEASURE seam
-- (`Echo.Measure.Examples.tropical-cost-measure`) supplies the tropical
-- carrier; this module pins only the variance SHAPE.
NotProved-full-min-plus-graded-monad-laws : Set
NotProved-full-min-plus-graded-monad-laws = ⊤

-- NOT claimed: that `split-with-factoring` is non-canonical. Given the
-- factoring it is the unique inverse (2). The obstruction (3) is strictly
-- about recovery from a BARE residue with no factoring supplied.
NotProved-no-split-even-with-factoring : Set
NotProved-no-split-even-with-factoring = ⊤
