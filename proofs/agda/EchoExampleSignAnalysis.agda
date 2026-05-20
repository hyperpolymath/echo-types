{-# OPTIONS --safe --without-K #-}

-- Example 10 (`docs/echo-types/examples.md` §10): abstract
-- interpretation / sign analysis.
--
-- An Agda exhibit accompanying `applications-compiler-analysis.adoc`
-- § "Example 2".  Models a fragment of compiler-analysis residue:
-- the residue at each abstract class is non-propositional, exhibited
-- by two distinct concrete witnesses at the same abstract value.
--
-- This is the *exact* echo layer.  Axis 2 (approximate echoes /
-- widening) lives in `EchoApprox.agda`; a follow-on exhibit could
-- thread widening's tolerance accumulation through this example.
--
-- Headline lemmas (pinned in `Smoke.agda`):
--
--   * nat-sign-non-injective     -- collapse witness on pos class
--   * echo-1-pos                  -- 1 abstracts to pos
--   * echo-2-pos                  -- 2 abstracts to pos
--   * echo-1≢echo-2              -- distinct concrete witnesses
--   * echo-pos-classification     -- every pos-class echo is suc-shaped

module EchoExampleSignAnalysis where

open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)

open import Echo using (Echo)

----------------------------------------------------------------------
-- The sign lattice
----------------------------------------------------------------------

-- Two-point sign lattice over ℕ: `zero-sign` for 0, `pos-sign` for
-- positive naturals.  A three-element {neg, zero, pos} lattice over
-- ℤ would be the textbook AI shape; the two-point version captures
-- the residue structure with ℕ-only arithmetic.

data Sign : Set where
  zero-sign : Sign
  pos-sign  : Sign

-- The abstraction function.  `nat-sign` collapses every positive
-- natural to `pos-sign`; this is the canonical lossy projection of
-- compiler-analysis sign tracking.

nat-sign : ℕ → Sign
nat-sign zero    = zero-sign
nat-sign (suc _) = pos-sign

----------------------------------------------------------------------
-- Headline 1 — non-injectivity of the abstraction
--
-- The abstraction is non-injective at `pos-sign`: any two distinct
-- positive ℕ values both map there.  This is the "what is lost" in
-- the loss / residue language of `applications-compiler-analysis.adoc`.
----------------------------------------------------------------------

nat-sign-non-injective :
  Σ ℕ (λ m → Σ ℕ (λ n → (nat-sign m ≡ nat-sign n) × (m ≢ n)))
nat-sign-non-injective = 1 , 2 , refl , λ ()

----------------------------------------------------------------------
-- Headline 2 — concrete witnesses at the pos-sign class
--
-- `Echo nat-sign pos-sign = Σ ℕ (λ n → nat-sign n ≡ pos-sign)`.  Any
-- successor witnesses the residue at `pos-sign`; we pin two
-- concretely.
----------------------------------------------------------------------

echo-1-pos : Echo nat-sign pos-sign
echo-1-pos = 1 , refl

echo-2-pos : Echo nat-sign pos-sign
echo-2-pos = 2 , refl

----------------------------------------------------------------------
-- Headline 3 — the residue is not propositional
--
-- The two pinned witnesses are distinct as `Σ`-pairs because their
-- first projections (1 and 2) are distinct.  This is the
-- `echo-not-prop` shape of `examples.md` example 10 — the residue
-- carries witness data the abstract class itself does not.
----------------------------------------------------------------------

echo-1≢echo-2 : echo-1-pos ≢ echo-2-pos
echo-1≢echo-2 p with cong proj₁ p
... | ()

----------------------------------------------------------------------
-- Headline 4 — classification of pos-class residues
--
-- Every echo at the pos-sign class has a successor as its first
-- projection: the residue at `pos-sign` is exactly the family of
-- positive naturals.  Proved by case analysis on the carrier.
----------------------------------------------------------------------

echo-pos-classification :
  ∀ (e : Echo nat-sign pos-sign) → Σ ℕ (λ k → proj₁ e ≡ suc k)
echo-pos-classification (zero  , ())
echo-pos-classification (suc k , refl) = k , refl
