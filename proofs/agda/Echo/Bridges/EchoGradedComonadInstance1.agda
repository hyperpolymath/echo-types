{-# OPTIONS --safe --without-K #-}

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

module Echo.Bridges.EchoGradedComonadInstance1 where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; +-assoc)

open import Echo.Bridges.EchoGradedComonadInterface using (GradedComonadStructure)
open import Echo.Bridges.EchoGradedComonadF1 using
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
