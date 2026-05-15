{-# OPTIONS --safe --without-K #-}

-- Rank function `rank : BT → Ord` for the Phase-2 transport route to
-- unbudgeted `WellFounded _<ᵇʳᶠ_`.  Echidna's design-search +
-- 4-agent swarm both unanimously recommended this shape (energy
-- [3, 0, 1]: three downstream blockers, zero capability gaps,
-- minimal structural cost).
--
-- See `echidna/docs/decisions/2026-04-28-corpus-and-design-search.md`
-- and `echo-types/docs/echidna-design-search-2026-04-28.adoc` for
-- the SA + swarm output, including the 5 next-best alternatives all
-- of which scored strictly worse.
--
-- ## What's here
--
-- * `rank : BT → Ord` — the recommended shape, structural recursion
--   on BT.
--
-- ## What's deferred
--
-- The transport theorem `rank-mono : ∀ {x y} → x <ᵇʳᶠ y → rank x <
-- rank y` requires three downstream lemmas:
--
--   * `<ᵇʳᶠ-core x<ᵇy` ⟹ Phase-2.2 `rank-mono-<ᵇ`  (open)
--   * `<ᵇʳᶠ-ψα α<ᵇʳᶠβ`  ⟹ `⊕-mono-<-right`           (landed, Phase13.agda)
--   * `<ᵇʳᶠ-+2 y<ᵇʳᶠz`  ⟹ `⊕-mono-<-right`           (landed, Phase13.agda)
--
-- Once `rank-mono-<ᵇ` lands, the closing chain is:
--
--   wf-<ᵇʳᶠ : WellFounded _<ᵇʳᶠ_
--   wf-<ᵇʳᶠ = Subrelation.wellFounded rank-mono
--               (InverseImage.wellFounded rank wf-<′)

module Ordinal.Buchholz.RankBrouwer where

open import Ordinal.Brouwer using (Ord; oz)
open import Ordinal.Brouwer.Arithmetic using (_⊕_; ω-rank; psi-rank)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bOmega; bplus; bpsi)

----------------------------------------------------------------------------
-- The recommended rank function
----------------------------------------------------------------------------

-- `rank` interprets each Buchholz term as a Brouwer ordinal.  The
-- shape was selected by SA over a 27-candidate design space (3 ×
-- 3 × 3 = bplus × bpsi × bOmega knobs):
--
--   * `bzero ↦ oz`              — fixed (no nontrivial choice).
--   * `bOmega ν ↦ ω-rank ν`     — wins over `osuc (ω-rank ν)` by
--                                 structural cost.
--   * `bplus x y ↦ rank x ⊕ rank y`
--                               — wins over `osuc (rank x ⊕ rank y)`
--                                 because the outer `osuc` is dead
--                                 weight for `<ᵇʳᶠ-+2`'s right-
--                                 monotonicity argument.
--   * `bpsi ν α ↦ psi-rank ν (rank α)`
--                               — wins over `ω-rank ν ⊕ rank α` and
--                                 `osuc (ω-rank ν) ⊕ rank α` by
--                                 carrying the strictness witness
--                                 (the `osuc` baked into psi-rank).

rank : BT → Ord
rank bzero        = oz
rank (bOmega ν)   = ω-rank ν
rank (bplus x y)  = rank x ⊕ rank y
rank (bpsi ν α)   = psi-rank ν (rank α)
