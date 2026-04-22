{-# OPTIONS --safe --without-K #-}

-- Stage S1/S2 scaffolding for docs/buchholz-plan.adoc.
--
-- Formal Ω-index markers only; no ordinal semantics is claimed here.
-- Finite markers are represented by `fin n`, and `ω` is the first
-- limit marker used later by Buchholz syntax.

module Ordinal.OmegaMarkers where

open import Data.Nat.Base using (ℕ; zero; suc)

data OmegaIndex : Set where
  fin : ℕ → OmegaIndex
  ω   : OmegaIndex

Omega0 : OmegaIndex
Omega0 = fin zero

Omega1 : OmegaIndex
Omega1 = fin (suc zero)

Omegaω : OmegaIndex
Omegaω = ω
