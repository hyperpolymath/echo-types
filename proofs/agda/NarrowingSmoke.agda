{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-- Focused entrypoint for the Wasm narrowing model and numeric contract.
-- Prepared with Codex (GPT-6) assistance, 2026-09-07.
module NarrowingSmoke where

open import Data.Nat.Base using (_+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import EchoExampleTruncation using
  (echo-halve-even; echo-halve-odd; echo-halve-witnesses-distinct;
   echo-halve-classification-general)
open import EchoExampleBitNarrowing using
  (dropBits; keepBits; restore; reconstruct-original;
   keep-restored; drop-restored; restored-echo)
open import EchoBitNarrowingNumeric using
  (radix; value; restore-numeric; value-bounded;
   numeric-decomposition; reconstruction-bounded)

u8-radix : radix 8 ≡ 256
u8-radix = refl

u8-retained : value (keepBits 8 263) ≡ 7
u8-retained = refl

u8-discarded : dropBits 8 263 ≡ 1
u8-discarded = refl

u8-numeric-reconstruction :
  263 ≡ radix 8 * dropBits 8 263 + value (keepBits 8 263)
u8-numeric-reconstruction = numeric-decomposition 8 263
