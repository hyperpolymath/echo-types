{-# OPTIONS --safe --without-K #-}

-- EchoFiberCount: honest finite-domain fiber counting.
--
-- Companion to EchoDecidable. Where EchoDecidable answers
-- "does an echo exist?" (axis-8 decidability), this module
-- answers "how many?" — but only in the regime where the
-- question has a constructive answer: a finite domain `Fin n`
-- with decidable equality on the codomain.
--
-- The headline value `FiberSize-fin f y _≟_` counts the
-- preimages of `y : B` under `f : Fin n → B`, computed by
-- enumerating `Fin n` and asking the decidable equality at
-- each index. This replaces the earlier
-- `EchoThermodynamics.FiberSize = 1` hardcode (which rendered
-- every Landauer/Bennett claim vacuous): with an actual count
-- in hand we can state honest finite-domain bounds.
--
-- Headline lemmas (pinned in Smoke.agda):
--
--   * FiberSize-fin-id-zero       -- id : Fin (suc m) → Fin (suc m) has fiber 1 at zero
--   * FiberSize-fin-const         -- (λ _ → y₀) has fiber n at y₀
--   * FiberSize-fin≡0⇒no-echo     -- count 0 ⇒ no echo witness
--   * no-echo⇒FiberSize-fin≡0     -- no echo witness ⇒ count 0
--
-- The id-zero lemma is the single instance the
-- `bennett-reversible` corollary in `EchoThermodynamics`
-- runs on; the const lemma is the worst-case input for
-- `landauer-collapse`; the bidirectional ≡0/¬Echo lemmas
-- pin the count to the metatheoretic structure of `Echo`.

module EchoFiberCount where

open import Function.Base                         using (_∘_)
open import Data.Empty                            using (⊥; ⊥-elim)
import      Data.Nat.Base                         as ℕ
open        ℕ                                     using (ℕ)
open import Data.Fin.Base                         using (Fin; zero; suc)
open import Data.Product.Base                     using (Σ; _,_)
open import Relation.Nullary                      using (¬_)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Echo                                  using (Echo)

----------------------------------------------------------------------
-- The fiber count
----------------------------------------------------------------------

-- Counts the preimages of `y` under `f : Fin n → B` by enumerating
-- the domain and asking the decidable equality at each index. Total
-- and terminating: each recursion call shrinks the implicit `n`.

FiberSize-fin :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) →
  ((y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  ℕ
FiberSize-fin {n = ℕ.zero}  f y _≟_ = ℕ.zero
FiberSize-fin {n = ℕ.suc m} f y _≟_ with f zero ≟ y
... | yes _ = ℕ.suc (FiberSize-fin (f ∘ suc) y _≟_)
... | no  _ = FiberSize-fin (f ∘ suc) y _≟_

----------------------------------------------------------------------
-- Auxiliary "all-hit" / "no-hit" lemmas
----------------------------------------------------------------------

private
  suc≢0 : ∀ {k} → ℕ.suc k ≡ ℕ.zero → ⊥
  suc≢0 ()

  suc≢zero-Fin : ∀ {n} (i : Fin n) → ¬ (suc i ≡ zero)
  suc≢zero-Fin _ ()

----------------------------------------------------------------------
-- "no-hit" / "all-hit" lemmas (exposed for downstream use).
--
-- These are the two extremal shapes of the count: the count is
-- zero exactly when no index hits, and the count is `n` exactly
-- when every index hits. Both proofs walk the FiberSize-fin
-- recursion in lock-step with a hypothesis on f.
----------------------------------------------------------------------

-- If f never hits y, the count is 0.
FiberSize-fin-no-hit :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  (∀ i → ¬ (f i ≡ y)) →
  FiberSize-fin f y _≟_ ≡ ℕ.zero
FiberSize-fin-no-hit {n = ℕ.zero}  f y _≟_ h = refl
FiberSize-fin-no-hit {n = ℕ.suc m} f y _≟_ h with f zero ≟ y
... | yes p = ⊥-elim (h zero p)
... | no  _ = FiberSize-fin-no-hit (f ∘ suc) y _≟_ (λ i → h (suc i))

-- If f hits y everywhere, the count is n.
FiberSize-fin-all-hit :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  (∀ i → f i ≡ y) →
  FiberSize-fin f y _≟_ ≡ n
FiberSize-fin-all-hit {n = ℕ.zero}  f y _≟_ h = refl
FiberSize-fin-all-hit {n = ℕ.suc m} f y _≟_ h with f zero ≟ y
... | yes _ = cong ℕ.suc (FiberSize-fin-all-hit (f ∘ suc) y _≟_ (λ i → h (suc i)))
... | no ¬p = ⊥-elim (¬p (h zero))

----------------------------------------------------------------------
-- Headline 1 — FiberSize-fin-id-zero
--
-- The identity `id : Fin (suc m) → Fin (suc m)` has fiber size 1
-- at the zero index. Specific instance of "any injection has
-- singleton fibers everywhere"; the `bennett-reversible` corollary
-- in `EchoThermodynamics` runs on this lemma plus `⌊log₂ 1 ⌋ ≡ 0`.
----------------------------------------------------------------------

FiberSize-fin-id-zero :
  ∀ {m : ℕ} (_≟_ : (a b : Fin (ℕ.suc m)) → Dec (a ≡ b)) →
  FiberSize-fin {n = ℕ.suc m} (λ x → x) zero _≟_ ≡ ℕ.suc ℕ.zero
FiberSize-fin-id-zero {m} _≟_ with (zero {m}) ≟ (zero {m})
... | yes refl = cong ℕ.suc (FiberSize-fin-no-hit (λ x → suc x) zero _≟_ suc≢zero-Fin)
... | no  ¬p   = ⊥-elim (¬p refl)

----------------------------------------------------------------------
-- Headline 2 — FiberSize-fin-const
--
-- The constant function `(λ _ → y₀) : Fin n → B` has fiber size n
-- at `y₀`: every domain index hits, so the count equals the domain
-- size. This is the worst-case input for the Landauer bound — every
-- Fin-index is collapsed onto a single output value.
----------------------------------------------------------------------

FiberSize-fin-const :
  ∀ {b} {B : Set b} {n : ℕ}
  (y₀ : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  FiberSize-fin {n = n} (λ _ → y₀) y₀ _≟_ ≡ n
FiberSize-fin-const y₀ _≟_ = FiberSize-fin-all-hit (λ _ → y₀) y₀ _≟_ (λ _ → refl)

----------------------------------------------------------------------
-- Headline 3 — FiberSize-fin ≡ 0 ⟺ ¬ Echo (split into two halves).
--
-- The constructive count zero is exactly the constructive absence
-- of an echo. Pins `FiberSize-fin` to the metatheoretic structure
-- of `Echo` from `Echo.agda`: count zero is the *only* numerical
-- shape consistent with there being no witness.
----------------------------------------------------------------------

FiberSize-fin≡0⇒no-echo :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  FiberSize-fin f y _≟_ ≡ ℕ.zero →
  ¬ Echo f y
FiberSize-fin≡0⇒no-echo {n = ℕ.zero}  f y _≟_ p (() , _)
FiberSize-fin≡0⇒no-echo {n = ℕ.suc m} f y _≟_ p (zero  , q) with f zero ≟ y
... | yes _  = ⊥-elim (suc≢0 p)
... | no  ¬q = ¬q q
FiberSize-fin≡0⇒no-echo {n = ℕ.suc m} f y _≟_ p (suc i , q) with f zero ≟ y
... | yes _ = ⊥-elim (suc≢0 p)
... | no  _ = FiberSize-fin≡0⇒no-echo (f ∘ suc) y _≟_ p (i , q)

no-echo⇒FiberSize-fin≡0 :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  ¬ Echo f y →
  FiberSize-fin f y _≟_ ≡ ℕ.zero
no-echo⇒FiberSize-fin≡0 {n = ℕ.zero}  f y _≟_ ¬e = refl
no-echo⇒FiberSize-fin≡0 {n = ℕ.suc m} f y _≟_ ¬e with f zero ≟ y
... | yes p = ⊥-elim (¬e (zero , p))
... | no  _ = no-echo⇒FiberSize-fin≡0 (f ∘ suc) y _≟_ (λ { (i , q) → ¬e (suc i , q) })

----------------------------------------------------------------------
-- Companion remark.
--
-- This module deliberately stays at the finite-domain `Fin n` level.
-- The infinite-domain case (e.g. `ProgramState = ℕ → ℕ`) is *not*
-- addressed: counting fibers of a function on an infinite type is
-- not constructively meaningful in general. EchoThermodynamics's
-- claims about CNOs over infinite state spaces are out of reach
-- without a heavier semantic framework (capacity, measure, or
-- equivalence-class quotients), and that limitation is now made
-- explicit in `docs/ECHO-CNO-BRIDGE.adoc`.
