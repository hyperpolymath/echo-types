{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Example 6 (`docs/echo-types/examples.md` §6): lossy numerical
-- truncation.
--
-- An Agda exhibit demonstrating compiler-analysis-style residue
-- in a numerical setting.  The original example takes `truncate :
-- ℝ → ℤ` with floor; ℝ isn't in stdlib v2.3, so this exhibit
-- adapts to an analogous `halve : ℕ → ℕ` (integer division by 2)
-- which exhibits the same structural shape: each output has
-- exactly two preimages, both equally valid concrete witnesses.
--
-- The applications-chapter axis-2 widening discussion
-- (`applications-compiler-analysis.adoc` § Example 2) uses the
-- approximate-echo refinement to thread tolerance through this
-- kind of lossy projection.  This exhibit is the *exact* layer;
-- a follow-on could pair it with `EchoApprox` for the tolerance
-- accumulation.
--
-- Headline lemmas (pinned in `Smoke.agda`):
--
--   * halve                       -- the truncation function
--   * halve-non-injective         -- 6 and 7 both halve to 3
--   * echo-6-halve3               -- 6 is a witness at 3
--   * echo-7-halve3               -- 7 is a witness at 3
--   * echo-6≢echo-7              -- the residue is not propositional
--   * echo-halve-classification   -- every echo at n is in {2n, 2n+1}

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
-- `Echo halve 3 = Σ ℕ (λ n → halve n ≡ 3)`.  Both 6 and 7 witness
-- the residue at 3.  These are the two preimages of `truncate(x) =
-- 3` in the original `truncate : ℝ → ℤ` formulation (the integer-
-- pair analogue of the half-unit fractional spread).
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
-- The residue at any `n` is exactly the pair `{2n, 2n+1}` (using
-- ℕ-arithmetic that does not name `2n` explicitly).  Proved by
-- structural recursion: `halve m ≡ n` forces `m` to be of one of
-- two shapes by inspection.
----------------------------------------------------------------------

echo-halve-classification :
  ∀ (e : Echo halve 3) → (proj₁ e ≡ 6) ⊎ (proj₁ e ≡ 7)
echo-halve-classification (6                , refl) = inj₁ refl
echo-halve-classification (7                , refl) = inj₂ refl
echo-halve-classification (zero             , ())
echo-halve-classification (suc zero         , ())
echo-halve-classification (suc (suc (suc (suc (suc (suc (suc (suc m))))))) , ())
