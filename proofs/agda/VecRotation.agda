{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

------------------------------------------------------------------------
-- Vec-rotation infrastructure.
--
-- One cyclic-rotation fact about the alternating (sign-flipping)
-- vector, factored out of `examples/Transport.agda` where it blocked
-- the `∀ n` generalisation of `nyquist-in-step-kernel`.  Polymorphic
-- over any carrier with an involutive "negation"; the ℚ Nyquist mode
-- is the intended instance (`-_` is involutive via
-- `Data.Rational.Properties.neg-involutive`).
--
-- `rotL`/`rotR` are reproduced verbatim from `examples/Transport.agda`
-- (stdlib carries no cyclic rotation), so the lemma is drop-in for the
-- consumer.  Scope is deliberately one lemma plus its `map` corollary;
-- this is not a general rotation theory.
--
-- Note on the statement.  The minimally honest signature carries an
-- explicit involution hypothesis `neg (neg x) ≡ x`: rotating an
-- *even*-length alternating vector by one equals its pointwise
-- negation, and the equality genuinely needs `neg² = id` (it fails
-- pointwise otherwise).  The `2 * n` length is what makes the
-- alternation parity-stable; the builder mirrors Transport's
-- `concat ∘ replicate` 2-block construction exactly.
------------------------------------------------------------------------

module VecRotation where

open import Data.Nat.Base using (ℕ; zero; suc; _*_)
open import Data.Vec.Base
  using (Vec; []; _∷_; _++_; map; concat; replicate; _∷ʳ_; reverse)
open import Data.Vec.Properties
  using (reverse-∷; reverse-involutive)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

private
  variable
    A : Set

-- Cyclic rotations (verbatim from examples/Transport.agda).
rotL : ∀ {n} → Vec A n → Vec A n
rotL []       = []
rotL (x ∷ xs) = xs ∷ʳ x

rotR : ∀ {n} → Vec A n → Vec A n
rotR xs = reverse (rotL (reverse xs))

-- The alternating vector [a, neg a, a, neg a, …] of length 2·n,
-- built from n copies of the 2-block (the shape of Transport's
-- `nyquist`, modulo its outer `*-comm` `vcast`).
alternating : (A → A) → (n : ℕ) → A → Vec A (n * 2)
alternating neg n a = concat (replicate n (a ∷ neg a ∷ []))

-- One-step unfolding.  Definitional: the 2-block keeps `a` fixed, so
-- there is no parity flip to track here.
alt-cons : ∀ (neg : A → A) n a →
  alternating neg (suc n) a ≡ a ∷ neg a ∷ alternating neg n a
alt-cons neg n a = refl

-- `map neg` walks the alternation forward by one block.  No involution
-- needed; the consumer's homogeneity step uses this corollary.
map-alternating : ∀ (neg : A → A) n a →
  map neg (alternating neg n a) ≡ alternating neg n (neg a)
map-alternating neg zero    a = refl
map-alternating neg (suc n) a =
  cong (λ z → neg a ∷ neg (neg a) ∷ z) (map-alternating neg n a)

-- Snoc/cons reshuffle: appending `a` at the tail of an alternating
-- vector equals consing `a` onto its pointwise negation.  This is the
-- single inductive step the rotation lemma turns on; the involution
-- enters here (and only here).
alt-snoc : ∀ (neg : A → A) (inv : ∀ x → neg (neg x) ≡ x) n a →
  alternating neg n a ∷ʳ a ≡ a ∷ map neg (alternating neg n a)
alt-snoc neg inv zero    a = refl
alt-snoc neg inv (suc n) a =
  cong (λ z → a ∷ neg a ∷ z)
    (trans (alt-snoc neg inv n a)
           (cong (_∷ map neg (alternating neg n a)) (sym (inv a))))

-- Headline: left-rotating the (even-length) alternating vector equals
-- negating it.  This is exactly the Vec-rotation fact stdlib does not
-- provide and that `examples/Transport.agda` documents as the blocker
-- for `∀ n → step (nyquist n) ≡ 0`.
rotL-alternating : ∀ (neg : A → A) (inv : ∀ x → neg (neg x) ≡ x) n a →
  rotL (alternating neg n a) ≡ map neg (alternating neg n a)
rotL-alternating neg inv zero    a = refl
rotL-alternating neg inv (suc n) a =
  cong (neg a ∷_)
    (trans (alt-snoc neg inv n a)
           (cong (_∷ map neg (alternating neg n a)) (sym (inv a))))

------------------------------------------------------------------------
-- rotR variant.
--
-- `rotR` is `step`'s other rotation, so the consumer needs it too.
-- Rather than re-run the inductive argument through `reverse`'s
-- double-snoc (which has no clean stdlib support), `rotR` is recovered
-- as the inverse of `rotL`: `rotR ∘ rotL ≡ id` reduces, via the
-- one derived helper `reverse-∷ʳ` (dual of stdlib `reverse-∷`), to
-- `reverse-involutive`.  `rotR-alternating` then reuses the landed
-- `rotL-alternating` with no new induction over the alternation.

-- Dual of stdlib `reverse-∷`: snoc-then-reverse is reverse-then-cons.
reverse-∷ʳ : ∀ x {n} (xs : Vec A n) → reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
reverse-∷ʳ x xs =
  trans (cong reverse
           (sym (trans (reverse-∷ x (reverse xs))
                       (cong (_∷ʳ x) (reverse-involutive xs)))))
        (reverse-involutive (x ∷ reverse xs))

-- `rotR` undoes `rotL`.
rotR-rotL : ∀ {n} (v : Vec A n) → rotR (rotL v) ≡ v
rotR-rotL []       = refl
rotR-rotL (x ∷ xs) =
  trans (cong (λ z → reverse (rotL z)) (reverse-∷ʳ x xs))
        (trans (reverse-∷ʳ x (reverse xs))
               (cong (x ∷_) (reverse-involutive xs)))

-- One step of the rotation, the right-handed way: `rotR` of the
-- block-shifted alternation recovers the original.
rotR-alternating-shift : ∀ (neg : A → A) (inv : ∀ x → neg (neg x) ≡ x)
  n a → rotR (alternating neg n (neg a)) ≡ alternating neg n a
rotR-alternating-shift neg inv n a =
  trans (cong rotR
           (sym (trans (rotL-alternating neg inv n a)
                       (map-alternating neg n a))))
        (rotR-rotL (alternating neg n a))

-- Headline (rotR twin of `rotL-alternating`).
rotR-alternating : ∀ (neg : A → A) (inv : ∀ x → neg (neg x) ≡ x) n a →
  rotR (alternating neg n a) ≡ map neg (alternating neg n a)
rotR-alternating neg inv n a =
  trans (cong rotR (cong (alternating neg n) (sym (inv a))))
        (trans (rotR-alternating-shift neg inv n (neg a))
               (sym (map-alternating neg n a)))
