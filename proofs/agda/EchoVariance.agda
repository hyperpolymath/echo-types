{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoVariance — resolving, IN --safe AGDA RATHER THAN ASSERTED, the
-- monad / comonad / adjunction variance of loss accumulation.
--
-- THE LIVE QUESTION (the new understanding of echo-types). An echo-type
-- is a tropically-graded modality of structured information loss: an
-- instance of graded-(co)monad machinery over the min-plus semiring
-- (ℕ ∪ {∞}, min, +), with recoverability "exact on a homotopy fibre
-- rather than over-approximating or complement-storing". Its precise
-- variance was unsettled: the *combining* direction of loss is monadic
-- (accumulation is μ : D_r (D_s A) → D_{r+s} A), so is the right word
-- "graded comonad", "graded monad", or "graded adjunction (with the
-- section as unit/counit)"?  R-2026-05-18 (docs/retractions.adoc)
-- already RETRACTED the unqualified "graded comonad" claim on
-- `EchoGradedComonad`, reframing it as a loss-graded *reindexing*
-- modality with NO nested D_r D_s.  This module supplies the nested maps
-- the question is actually about, and lets the type-checker decide.
--
-- HOW THE TROPICAL SEMIRING SPLITS ACROSS THE TWO AXES (already the
-- repo's architecture):
--   * min (⊕, the order / lattice) is the thin echo INDEX
--     (`Echo.Index.ThinPoset`); `degrade` reindexes along it. This is the
--     proof-relevant modality CORE, deliberately semiring-free.
--   * + (⊗, accumulation) is the residue MEASURE (`Echo.Measure.*`), a
--     lossy, monotone OBSERVATION. The accumulation μ : D_r D_s → D_{r+s}
--     the live question names lives on THIS axis.
--
-- THE VERDICT (each clause proved below, not asserted):
--
--  (1) ACCUMULATION IS MONADIC. The combining map μ on the genuine
--      (fibre) loss modality — nested loss → combined loss — is total
--      and CANONICAL: it is definable from the layered data alone (the
--      factoring is its input). `accumulate` = `Echo-comp-iso-from`.
--      This is the graded-monad multiplication shape; the loss
--      magnitudes add.
--
--  (2) RECOVERABILITY IS EXACT ON THE FIBRE. For a FIXED factoring,
--      accumulate and split are mutually inverse (both round-trips
--      `refl`): the fibre stores the loss precisely — not over-
--      approximating, not complement-storing.  At grade 0 this is the
--      totality iso `A ↔ Σ B (Echo f)` (`recoverable-fibre`): the
--      section/retraction pair, i.e. the unit/counit of the ADJUNCTION
--      reading.
--
--  (3) THE COMONAD DIRECTION FAILS FOR GENUINE LOSS. A graded comonad
--      would supply a NATURAL δ on the BARE residual functor: recover the
--      intermediate/layered data from a residue WITHOUT being handed a
--      factoring. For genuine loss that is exactly the irreversibility
--      obstruction: the canonical collapse has NO section
--      (`no-bare-recovery`). The forgotten bit is retained ON THE FIBRE
--      (`fibre-retains-lost-bit`) but is NOT a recoverable complement of
--      the residue.
--
--  (4) THE "GRADED COMONAD" READING IS THE COMPLEMENT-STORING NEIGHBOUR.
--      `EchoGradedComonadF1` IS a genuine nested graded comonad — but its
--      model `D r A = A × Boolʳ` RETAINS its residue layers, so its δ is
--      `coe` along a TYPE EQUALITY `D (m+n) A ≡ D m (D n A)`, hence
--      INVERTIBLE. We exhibit the inverse `μ-writer` and prove both
--      round-trips: the writer is simultaneously a graded comonad AND a
--      graded monad. That bi-directionality is the signature of a
--      COMPLEMENT-STORING (resource / coeffect) modality — precisely what
--      the new understanding says echo-types is NOT.
--
-- ONE-LINE RESOLUTION. Echo-types (fibre-based loss) is a GRADED MONAD of
-- accumulation (the + axis) together with a section/retraction ADJUNCTION
-- that is exact on the grade-0 fibre; it is NOT a graded comonad — the
-- comonad reading silently substitutes the complement-storing writer,
-- which is lossless. The min axis (order / `degrade`) carries the
-- reindexing modality; the + axis (accumulation) carries the monad.
--
-- --safe --without-K, zero postulates. Everything reuses existing kernel
-- theorems (`Echo-comp-iso`, `no-section-of-collapsing-map`, `A↔ΣEcho`,
-- and F1's `δ`/`D-+`/`coe`); nothing here is new trust.

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
-- (1) ACCUMULATION IS MONADIC — μ : D_r (D_s A) → D_{r+s} A.
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
-- round-trips are `refl`. The fibre stores the loss precisely: no
-- over-approximation, no stored complement. This is the
-- "exact-on-a-homotopy-fibre" half of the verdict at the level of a
-- single layered computation.
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

-- The grade-0 instance: A ≅ Σ B (Echo f). The unit (encode) / counit
-- (decode) of the section/retraction ADJUNCTION live on the grade-0
-- fibre. This is the "section/retraction pair whose round-trip is exact
-- on a homotopy fibre", pinned as a genuine ↔.
recoverable-fibre : (f : A → B) → A ↔ Σ B (Echo f)
recoverable-fibre = A↔ΣEcho

----------------------------------------------------------------------
-- (3) THE COMONAD DIRECTION FAILS FOR GENUINE LOSS.
--
-- A graded COMONAD would supply a NATURAL δ on the BARE residual functor:
-- recover the intermediate / layered data from a residue WITHOUT being
-- handed a factoring. For genuine loss that is the irreversibility
-- obstruction. The canonical collapse `collapse : Bool → ⊤` has NO
-- section: no `raise : ⊤ → Bool` satisfies `raise ∘ collapse ≡ id`. The
-- forgotten bit cannot be recovered from the residue alone — genuine loss
-- does NOT store its complement.
----------------------------------------------------------------------

no-bare-recovery :
  ¬ Σ (⊤ → Bool) (λ raise → ∀ b → raise (collapse b) ≡ b)
no-bare-recovery =
  no-section-of-collapsing-map collapse true false (λ ()) refl

-- The fibre nevertheless retains the lost bit EXACTLY: `echo-true` and
-- `echo-false` are distinct echoes over the SAME residue `tt`. The loss
-- is stored on the FIBRE, not as a recoverable residue-complement — which
-- is exactly why `no-bare-recovery` holds while `accumulate-split-id`
-- is `refl`.
fibre-retains-lost-bit : echo-true ≢ echo-false
fibre-retains-lost-bit = echo-true≢echo-false

----------------------------------------------------------------------
-- (4) THE "GRADED COMONAD" READING IS THE COMPLEMENT-STORING NEIGHBOUR.
--
-- `EchoGradedComonadF1` is a genuine nested graded comonad, but its model
-- `D r A = A × Boolʳ` RETAINS its residue layers. Its comultiplication is
-- `δ = coe (D-+ m n A)` along the TYPE EQUALITY `D (m+n) A ≡ D m (D n A)`,
-- so it is INVERTIBLE. We exhibit the inverse `μ-writer` and prove both
-- round-trips: the writer is simultaneously a graded comonad AND a graded
-- monad. That bi-directionality is the signature of a COMPLEMENT-STORING
-- (resource / coeffect) modality — precisely what echo-types is NOT.
--
-- `μ-writer : D_m (D_n A) → D_{m+n} A` — note the type literally adds the
-- grades m + n, the additive (⊗ = +) axis of the tropical semiring.
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
-- identity. Together these show δ is an isomorphism — the writer is
-- LOSSLESS, hence both a graded comonad and a graded monad.
writer-δ-section :
  ∀ m n {A : Set} (y : D m (D n A)) → δ m n (μ-writer m n y) ≡ y
writer-δ-section m n {A} = coe-sym′ (D-+ m n A)

----------------------------------------------------------------------
-- Honest scope. Matched-negatives as ⊤-aliases (so `grep NotProved`
-- catches them). The verdict is about the SHAPE of the canonical
-- structure maps and the LOCUS of recoverability — not a universal
-- categorical impossibility theorem.
----------------------------------------------------------------------

-- NOT claimed: that no graded comonad of any kind touches Echo. F1 is one
-- — on the complement-storing writer. The claim is that GENUINE
-- (fibre-based, non-complement-storing) loss is not a graded comonad.
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
