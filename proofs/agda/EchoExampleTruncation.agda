{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Example 6 (`docs/echo-types/examples.md` §6): lossy numerical
-- truncation.
--
-- An Agda exhibit demonstrating compiler-analysis-style residue
-- in a numerical setting. This uses `halve : ℕ → ℕ` (integer division
-- by 2), whose small structural definitions expose both preimages
-- of each output. It is an analogue of lossy real-valued floor,
-- which has an interval of preimages rather than just two.
--
-- The applications-chapter axis-2 widening discussion
-- (`applications-compiler-analysis.adoc` § Example 2) uses the
-- approximate-echo refinement to thread tolerance through this
-- kind of lossy projection.  This exhibit is the *exact* layer;
-- a follow-on could pair it with `EchoApprox` for the tolerance
-- accumulation.
--
-- Headline lemmas:
--
--   * halve                       -- the truncation function
--   * halve-non-injective         -- 6 and 7 both halve to 3
--   * echo-6-halve3               -- 6 is a witness at 3
--   * echo-7-halve3               -- 7 is a witness at 3
--   * echo-6≢echo-7              -- the residue is not propositional
--   * echo-halve-even / odd       -- witnesses over every output n
--   * echo-halve-witnesses-distinct -- their origins remain distinct
--   * echo-halve-classification-general -- origins at n are {2n, 2n+1}
--   * echo-halve-classification   -- the original n = 3 specialisation

module EchoExampleTruncation where

open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base                         using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_)

open import Echo using (Echo)

----------------------------------------------------------------------
-- The truncation function
----------------------------------------------------------------------

-- Integer division by 2 via successor-pair pattern.  Every output
-- has exactly two preimages: `n` is hit by `2n` and `2n+1` (the
-- "lossy" floor pattern, adapted to ℕ from the ℝ → ℤ original).

halve : ℕ → ℕ
halve zero          = zero
halve (suc zero)    = zero
halve (suc (suc n)) = suc (halve n)

-- A structural doubling operation keeps the arithmetic specification
-- aligned with halve's successor-pair recursion.
double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

halve-double : ∀ n → halve (double n) ≡ n
halve-double zero    = refl
halve-double (suc n) = cong suc (halve-double n)

halve-suc-double : ∀ n → halve (suc (double n)) ≡ n
halve-suc-double zero    = refl
halve-suc-double (suc n) = cong suc (halve-suc-double n)

-- Both possible origins are inhabited at every output, including zero.
echo-halve-even : ∀ n → Echo halve n
echo-halve-even n = double n , halve-double n

echo-halve-odd : ∀ n → Echo halve n
echo-halve-odd n = suc (double n) , halve-suc-double n

private
  suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-injective refl = refl

  distinct-successor : ∀ n → n ≢ suc n
  distinct-successor zero ()
  distinct-successor (suc n) p = distinct-successor n (suc-injective p)

echo-halve-witnesses-distinct : ∀ n → echo-halve-even n ≢ echo-halve-odd n
echo-halve-witnesses-distinct n p = distinct-successor (double n) (cong proj₁ p)

----------------------------------------------------------------------
-- Headline 1 — non-injectivity at every output
--
-- The truncation is non-injective at every output: each output `n`
-- has both `2n` and `2n+1` as preimages.  Demonstrated concretely
-- at `n = 3`: both 6 and 7 halve to 3.
----------------------------------------------------------------------

halve-non-injective :
  Σ ℕ (λ m → Σ ℕ (λ n → (halve m ≡ halve n) × (m ≢ n)))
halve-non-injective = 6 , 7 , refl , λ ()

----------------------------------------------------------------------
-- Headline 2 — concrete witnesses at halve = 3
--
-- `Echo halve 3 = Σ ℕ (λ n → halve n ≡ 3)`. Both 6 and 7 witness
-- the residue at 3 in this integer-halving model. The corresponding
-- real-valued floor fibre over 3 is the interval [3, 4).
----------------------------------------------------------------------

echo-6-halve3 : Echo halve 3
echo-6-halve3 = 6 , refl

echo-7-halve3 : Echo halve 3
echo-7-halve3 = 7 , refl

----------------------------------------------------------------------
-- Headline 3 — the residue is not propositional
--
-- The two pinned witnesses are distinct because their first
-- projections (6 and 7) differ.  This is the `echo-not-prop` shape
-- — the residue carries witness data the truncated integer does
-- not.  In the applications setting: the truncation discards the
-- low-order bit, but the residue records which of the two
-- preimage halves was active.
----------------------------------------------------------------------

echo-6≢echo-7 : echo-6-halve3 ≢ echo-7-halve3
echo-6≢echo-7 p with cong proj₁ p
... | ()

----------------------------------------------------------------------
-- Headline 4 — classification: every preimage of n is 2n or 2n+1
--
-- Every possible source natural at output n is double n or its
-- successor. Together with the distinct witnesses above this gives
-- both directions of the classification of source values. This
-- statement does not compare the equality-proof components of echoes.
-- Recursion reduces n and removes a successor pair from the source.
----------------------------------------------------------------------

echo-halve-classification-general :
  ∀ n (e : Echo halve n) →
  (proj₁ e ≡ double n) ⊎ (proj₁ e ≡ suc (double n))
echo-halve-classification-general zero (zero , _) = inj₁ refl
echo-halve-classification-general zero (suc zero , _) = inj₂ refl
echo-halve-classification-general zero (suc (suc m) , ())
echo-halve-classification-general (suc n) (zero , ())
echo-halve-classification-general (suc n) (suc zero , ())
echo-halve-classification-general (suc n) (suc (suc m) , p)
  with echo-halve-classification-general n (m , suc-injective p)
... | inj₁ q = inj₁ (cong (λ k → suc (suc k)) q)
... | inj₂ q = inj₂ (cong (λ k → suc (suc k)) q)

-- Retain the original public statement for existing callers.
echo-halve-classification :
  ∀ (e : Echo halve 3) → (proj₁ e ≡ 6) ⊎ (proj₁ e ≡ 7)
echo-halve-classification = echo-halve-classification-general 3
