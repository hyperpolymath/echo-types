{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- An exact echo for unsigned bit narrowing. The visible output is a
-- little-endian vector of retained bits; the residue is the discarded
-- quotient. Reconstruction is proved for every width and natural input.
-- This is a mathematical specification, not a refinement proof of a Rust
-- shift/mask implementation or of a Wasm compiler/runtime.
module EchoExampleBitNarrowing where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Echo using (Echo)
open import EchoExampleTruncation
  using (halve; double; halve-double; halve-suc-double)

data Bit : Set where
  O I : Bit

lowBit : ℕ → Bit
lowBit zero = O
lowBit (suc zero) = I
lowBit (suc (suc n)) = lowBit n

joinBit : ℕ → Bit → ℕ
joinBit n O = double n
joinBit n I = suc (double n)

private
  low-double : ∀ n → lowBit (double n) ≡ O
  low-double zero = refl
  low-double (suc n) = low-double n

  low-suc-double : ∀ n → lowBit (suc (double n)) ≡ I
  low-suc-double zero = refl
  low-suc-double (suc n) = low-suc-double n

  halve-join : ∀ n b → halve (joinBit n b) ≡ n
  halve-join n O = halve-double n
  halve-join n I = halve-suc-double n

  low-join : ∀ n b → lowBit (joinBit n b) ≡ b
  low-join n O = low-double n
  low-join n I = low-suc-double n

  join-suc : ∀ n b → joinBit (suc n) b ≡ suc (suc (joinBit n b))
  join-suc n O = refl
  join-suc n I = refl

join-split : ∀ n → joinBit (halve n) (lowBit n) ≡ n
join-split zero = refl
join-split (suc zero) = refl
join-split (suc (suc n)) = trans
  (join-suc (halve n) (lowBit n))
  (cong (λ k → suc (suc k)) (join-split n))

-- Drop the retained low bits, leaving the upper quotient as residue.
dropBits : ℕ → ℕ → ℕ
dropBits zero n = n
dropBits (suc width) n = dropBits width (halve n)

keepBits : (width : ℕ) → ℕ → Vec Bit width
keepBits zero n = []
keepBits (suc width) n = lowBit n ∷ keepBits width (halve n)

restore : ∀ {width} → ℕ → Vec Bit width → ℕ
restore high [] = high
restore high (bit ∷ rest) = joinBit (restore high rest) bit

-- Every input is recovered, including width zero and widths above its size.
reconstruct-original : ∀ width n →
  restore (dropBits width n) (keepBits width n) ≡ n
reconstruct-original zero n = refl
reconstruct-original (suc width) n = trans
  (cong (λ high → joinBit high (lowBit n))
    (reconstruct-original width (halve n)))
  (join-split n)

-- Any high residue reconstructs an origin in the fibre over these low bits.
keep-restored : ∀ {width} high (bits : Vec Bit width) →
  keepBits width (restore high bits) ≡ bits
keep-restored high [] = refl
keep-restored high (bit ∷ rest)
  rewrite low-join (restore high rest) bit
        | halve-join (restore high rest) bit
        | keep-restored high rest = refl

restored-echo : ∀ {width} high (bits : Vec Bit width) → Echo (keepBits width) bits
restored-echo high bits = restore high bits , keep-restored high bits

-- Reassembly also preserves the specified high residue, not just the output.
drop-restored : ∀ {width} high (bits : Vec Bit width) →
  dropBits width (restore high bits) ≡ high
drop-restored high [] = refl
drop-restored high (bit ∷ rest)
  rewrite halve-join (restore high rest) bit = drop-restored high rest
