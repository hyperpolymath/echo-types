{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Echo.Measure.Examples — concrete residue measures over the
-- canonical loss modality `grade-echoModality`.
--
-- These DEMONSTRATE that the residue-measure seam
-- (`Echo.Measure.Interface`) admits the usual resource readings —
-- cost, tropical (min-plus) cost, and probability/confidence — WITHOUT
-- any of them entering Echo core. They live here, in
-- `Echo.Measure.Examples`, precisely so they do not pollute
-- `Echo.Modality.Core`.
--
-- Each example is a `ResidueMeasure grade-echoModality R`: a measure on
-- the three-point loss residues into an ordered carrier `R`, with the
-- monotonicity law discharged. They also show the variance is a free
-- choice of the carrier's order: the cost/tropical readings use `ℕ`
-- with `≤` (degradation accumulates cost), while the confidence
-- reading uses `ℕ` with the OPPOSITE order (degradation lowers
-- confidence) — same seam, opposite variance.

module Echo.Measure.Examples where

open import Level using (0ℓ)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

open import Echo.Modality.Core
  using ( Grade ; keep ; residue ; forget
        ; _≤g_
        ; keep≤keep ; keep≤residue ; keep≤forget
        ; residue≤residue ; residue≤forget ; forget≤forget
        ; grade-echoModality
        )
open import Echo.Measure.Interface using (OrderedCarrier; ResidueMeasure)

----------------------------------------------------------------------
-- Ordered carriers built from ℕ.
----------------------------------------------------------------------

-- ℕ under its usual order: the cost / tropical target.
ℕ-≤ : OrderedCarrier 0ℓ 0ℓ
ℕ-≤ = record
  { Carrier = ℕ
  ; _≤_     = _≤_
  ; ≤-refl  = ≤-refl
  ; ≤-trans = ≤-trans
  }

-- ℕ under the OPPOSITE order: the confidence target (higher ℕ = more
-- confident; the order is flipped so that "decreasing confidence" is
-- the monotone direction the seam asks for).
ℕ-≥ : OrderedCarrier 0ℓ 0ℓ
ℕ-≥ = record
  { Carrier = ℕ
  ; _≤_     = λ a b → b ≤ a
  ; ≤-refl  = ≤-refl
  ; ≤-trans = λ p q → ≤-trans q p
  }

----------------------------------------------------------------------
-- Example 1 — a cost measure.
--
-- `keep` is free, `residue` costs 1, `forget` costs 2. Degrading the
-- residue can only raise the cost, so the measure is monotone.
----------------------------------------------------------------------

grade-cost : Grade → ℕ
grade-cost keep    = 0
grade-cost residue = 1
grade-cost forget  = 2

grade-cost-mono : ∀ {i j} → i ≤g j → grade-cost i ≤ grade-cost j
grade-cost-mono keep≤keep       = z≤n
grade-cost-mono keep≤residue    = z≤n
grade-cost-mono keep≤forget     = z≤n
grade-cost-mono residue≤residue = s≤s z≤n
grade-cost-mono residue≤forget  = s≤s z≤n
grade-cost-mono forget≤forget   = s≤s (s≤s z≤n)

cost-measure : ResidueMeasure grade-echoModality ℕ-≤
cost-measure = record
  { measure  = λ {i} _ → grade-cost i
  ; monotone = λ p _ → grade-cost-mono p
  }

----------------------------------------------------------------------
-- Example 2 — a tropical-cost measure.
--
-- The carrier `ℕ-≤` is exactly the order-reduct of the tropical
-- (min-plus) semiring `(ℕ, min, +, ≤)`: the seam needs only the order,
-- so this measure lands in the tropical carrier under its natural
-- order. (The `min` / `+` operations are not exercised here — the seam
-- is order-only; a measure that also composes additively along
-- degradation would supply them.) A different cost profile from
-- Example 1 — `keep` and `residue` are both free, only `forget` costs
-- (1) — so it also shows many distinct measures inhabit one carrier.
----------------------------------------------------------------------

grade-trop : Grade → ℕ
grade-trop keep    = 0
grade-trop residue = 0
grade-trop forget  = 1

grade-trop-mono : ∀ {i j} → i ≤g j → grade-trop i ≤ grade-trop j
grade-trop-mono keep≤keep       = z≤n
grade-trop-mono keep≤residue    = z≤n
grade-trop-mono keep≤forget     = z≤n
grade-trop-mono residue≤residue = z≤n
grade-trop-mono residue≤forget  = z≤n
grade-trop-mono forget≤forget   = s≤s z≤n

tropical-cost-measure : ResidueMeasure grade-echoModality ℕ-≤
tropical-cost-measure = record
  { measure  = λ {i} _ → grade-trop i
  ; monotone = λ p _ → grade-trop-mono p
  }

----------------------------------------------------------------------
-- Example 3 — a probability/confidence measure.
--
-- `keep` is fully confident (2), `residue` partial (1), `forget` none
-- (0). Confidence DROPS as the residue degrades; with the opposite
-- order on `ℕ` (`ℕ-≥`) that drop is exactly the seam's monotone
-- direction. Same interface, opposite variance.
----------------------------------------------------------------------

grade-conf : Grade → ℕ
grade-conf keep    = 2
grade-conf residue = 1
grade-conf forget  = 0

-- Anti-monotone in the usual order = monotone in the flipped order.
grade-conf-anti : ∀ {i j} → i ≤g j → grade-conf j ≤ grade-conf i
grade-conf-anti keep≤keep       = s≤s (s≤s z≤n)
grade-conf-anti keep≤residue    = s≤s z≤n
grade-conf-anti keep≤forget     = z≤n
grade-conf-anti residue≤residue = s≤s z≤n
grade-conf-anti residue≤forget  = z≤n
grade-conf-anti forget≤forget   = z≤n

confidence-measure : ResidueMeasure grade-echoModality ℕ-≥
confidence-measure = record
  { measure  = λ {i} _ → grade-conf i
  ; monotone = λ p _ → grade-conf-anti p
  }
