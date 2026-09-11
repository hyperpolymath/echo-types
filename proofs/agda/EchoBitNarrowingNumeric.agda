{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Numeric specification for the typed-wasm-echo receipt. This proves the
-- natural-number equation and bounds, not a refinement of compiled Rust.
-- Prepared with Codex (GPT-6) assistance, 2026-09-07.
module EchoBitNarrowingNumeric where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc; +-identityʳ; *-assoc; ≤-step)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; module ≡-Reasoning)
open import EchoExampleTruncation using (double)
open import EchoExampleBitNarrowing
  using (Bit; O; I; joinBit; restore; keepBits; dropBits; reconstruct-original)

open ≡-Reasoning

radix : ℕ → ℕ
radix width = 2 ^ width

value : ∀ {width} → Vec Bit width → ℕ
value = restore 0

private
  double-sum : ∀ n → double n ≡ n + n
  double-sum zero = refl
  double-sum (suc n) = trans
    (cong (λ k → suc (suc k)) (double-sum n))
    (sym (cong suc (+-suc n n)))

  double-times-two : ∀ n → double n ≡ 2 * n
  double-times-two n = trans (double-sum n)
    (sym (cong (n +_) (+-identityʳ n)))

  double-plus : ∀ m n → double (m + n) ≡ double m + double n
  double-plus zero n = refl
  double-plus (suc m) n = cong (λ k → suc (suc k)) (double-plus m n)

  join-plus : ∀ m n b → joinBit (m + n) b ≡ double m + joinBit n b
  join-plus m n O = double-plus m n
  join-plus m n I = trans (cong suc (double-plus m n))
    (sym (+-suc (double m) (double n)))

  double-mono : ∀ {m n} → m ≤ n → double m ≤ double n
  double-mono z≤n = z≤n
  double-mono (s≤s p) = s≤s (s≤s (double-mono p))

  join-bound : ∀ {m n} → m < n → ∀ b → joinBit m b < double n
  join-bound (s≤s p) O = s≤s (≤-step (double-mono p))
  join-bound (s≤s p) I = s≤s (s≤s (double-mono p))

-- The bit-vector reconstruction has the exact arithmetic shape of the API.
restore-numeric : ∀ {width} high (bits : Vec Bit width) →
  restore high bits ≡ radix width * high + value bits
restore-numeric high [] = sym
  (trans (+-identityʳ (high + 0)) (+-identityʳ high))
restore-numeric {suc width} high (bit ∷ rest) = begin
  joinBit (restore high rest) bit
    ≡⟨ cong (λ k → joinBit k bit) (restore-numeric high rest) ⟩
  joinBit (radix width * high + value rest) bit
    ≡⟨ join-plus (radix width * high) (value rest) bit ⟩
  double (radix width * high) + joinBit (value rest) bit
    ≡⟨ cong (_+ joinBit (value rest) bit) (double-times-two (radix width * high)) ⟩
  2 * (radix width * high) + joinBit (value rest) bit
    ≡⟨ cong (_+ joinBit (value rest) bit) (sym (*-assoc 2 (radix width) high)) ⟩
  radix (suc width) * high + value (bit ∷ rest) ∎

-- A width-indexed output is always below its radix, including width zero.
value-bounded : ∀ {width} (bits : Vec Bit width) → value bits < radix width
value-bounded [] = s≤s z≤n
value-bounded {suc width} (bit ∷ rest) = subst
  (joinBit (value rest) bit <_)
  (double-times-two (radix width))
  (join-bound (value-bounded rest) bit)

numeric-decomposition : ∀ width n →
  n ≡ radix width * dropBits width n + value (keepBits width n)
numeric-decomposition width n = trans
  (sym (reconstruct-original width n))
  (restore-numeric (dropBits width n) (keepBits width n))

-- Under any declared word bound, reconstruction stays within that bound.
-- In particular wordBits = 32 expresses the mathematical u32 obligation.
reconstruction-bounded : ∀ wordBits width n → n < radix wordBits →
  radix width * dropBits width n + value (keepBits width n) < radix wordBits
reconstruction-bounded wordBits width n input-bound = subst
  (_< radix wordBits) (numeric-decomposition width n) input-bound
