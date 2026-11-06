{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Gate F3 phase 1 — instance 1 of N.
--
-- Packages the F1 iterated-residue construction
-- (`EchoGradedComonadF1.agda`) as an inhabitant of the
-- `EchoGradedComonadInterface.GradedComonadStructure` record at the
-- grade monoid `(ℕ, +, 0)`. The structure and laws are reused
-- verbatim — F1 already discharged them — so this module is purely
-- structural: it shows the abstract interface is *inhabitable* by
-- the existing F1 witness, with no shape mismatch and no extra
-- assumptions imported.
--
-- F1's gc-counit-l/r/coassoc are stated against ℕ's specific
-- equation proofs (`+-identityˡ`, `+-identityʳ`, `+-assoc`), so the
-- interface's monoid-equation `subst` reduces exactly to F1's
-- existing equations. The `gc-counit-r` field reduces by `refl`
-- because stdlib's `+-identityˡ` is itself `refl` for every
-- argument (`+` recurses on the left; `0 + n` is `n` definitionally).
--
-- F3 only PASSES when at least two non-isomorphic-grade-monoid
-- instances of the interface are mechanised. This module is one of
-- them; instance 2 (e.g. `(List X, ++, [])` for a non-trivial `X`)
-- is the phase-2 follow-up.

module EchoGradedComonadInstance1 where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; +-assoc)

open import EchoGradedComonadInterface using (GradedComonadStructure)
import EchoGradedComonadF1 as F1
open import EchoGradedComonadNaturality using (NaturalGradedComonad)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import EchoGradedComonadF1 using
  ( D
  ; mapD ; mapD-id ; mapD-∘
  ; ε
  ; δ
  ; gc-counit-l
  ; gc-counit-r
  ; gc-coassoc
  )

----------------------------------------------------------------------
-- The ℕ-graded instance.

nat-instance : GradedComonadStructure
nat-instance = record
  { G            = ℕ
  ; 1G           = 0
  ; _·G_         = _+_
  ; ·G-identityˡ = +-identityˡ
  ; ·G-identityʳ = +-identityʳ
  ; ·G-assoc     = +-assoc

  ; D            = D
  ; mapD         = mapD
  ; mapD-id      = mapD-id
  ; mapD-∘       = mapD-∘

  ; ε            = ε
  ; δ            = δ

  ; gc-counit-r  = gc-counit-r
  ; gc-counit-l  = gc-counit-l
  ; gc-coassoc   = gc-coassoc
  }

-- Explicit naturality witnesses for the packaged instance. The public
-- interface's choice of naturality fields is a separate design decision.
nat-ε-natural : ∀ {A B} (f : A → B)
  (x : GradedComonadStructure.D nat-instance 0 A) →
  GradedComonadStructure.ε nat-instance
    (GradedComonadStructure.mapD nat-instance 0 f x)
  ≡ f (GradedComonadStructure.ε nat-instance x)
nat-ε-natural = F1.ε-natural

nat-δ-natural : ∀ m n {A B} (f : A → B)
  (x : GradedComonadStructure.D nat-instance (m + n) A) →
  GradedComonadStructure.δ nat-instance m n
    (GradedComonadStructure.mapD nat-instance (m + n) f x)
  ≡ GradedComonadStructure.mapD nat-instance m
      (GradedComonadStructure.mapD nat-instance n f)
      (GradedComonadStructure.δ nat-instance m n x)
nat-δ-natural = F1.δ-natural

nat-natural-instance : NaturalGradedComonad nat-instance
nat-natural-instance = record
  { mapD-cong = F1.mapD-cong
  ; ε-natural = F1.ε-natural
  ; δ-natural = F1.δ-natural
  ; grade-isSet = F1.ℕ-uip
  }
