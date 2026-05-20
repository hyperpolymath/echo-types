{-# OPTIONS --safe --without-K #-}

-- Rank function `rank : BT → Ord` originally proposed for the
-- Phase-2 transport route to unbudgeted `WellFounded _<ᵇʳᶠ_`.
-- Echidna's design-search + 4-agent swarm unanimously recommended
-- this shape (energy [3, 0, 1]).
--
-- See `echidna/docs/decisions/2026-04-28-corpus-and-design-search.md`
-- and `echo-types/docs/echidna-design-search-2026-04-28.adoc` for
-- the SA + swarm output.
--
-- ## STATUS (CORRECTED 2026-05-20): the transport theorem is impossible
--
-- The transport theorem `rank-mono : ∀ {x y} → x <ᵇʳᶠ y → rank x <
-- rank y` would require three downstream lemmas:
--
--   * `<ᵇʳᶠ-core x<ᵇy` ⟹ `rank-mono-<ᵇ`        (was "open", ACTUALLY IMPOSSIBLE)
--   * `<ᵇʳᶠ-ψα α<ᵇʳᶠβ`  ⟹ `⊕-mono-<-right`     (landed, Phase13.agda)
--   * `<ᵇʳᶠ-+2 y<ᵇʳᶠz`  ⟹ `⊕-mono-<-right`     (landed, Phase13.agda)
--
-- `rank-mono-<ᵇ` is structurally impossible for the `_<ᵇ_`
-- constructor `<ᵇ-+Ω : x <ᵇ bOmega μ → bplus x y <ᵇ bOmega μ`:
-- instantiate `μ = fin 0`, `x = bzero`, `y = bOmega (fin 1)`. The
-- witness `bplus bzero (bOmega (fin 1)) <ᵇ bOmega (fin 0)` exists
-- via `<ᵇ-+Ω <ᵇ-0-Ω`, but additive rank gives `oz ⊕ ω-rank (fin 1)
-- = two` on the LHS and `ω-rank (fin 0) = one` on the RHS — so
-- `rank-mono-<ᵇ` would force `two <′ one`, which reduces to `⊥`.
--
-- The Echidna SA blueprint validated only the `<ᵇʳᶠ-ψα`/`<ᵇʳᶠ-+2`
-- blockers, not the 13-constructor `_<ᵇ_` interior. `_<ᵇ_` is a
-- syntactic strict order on raw BT, chosen so that direct
-- accessibility in `WellFounded.agda` closes — not the ordinal
-- order on Cantor normal forms. Constructors like `<ᵇ-+Ω`/`<ᵇ-Ω+`
-- admit derivations whose ordinal semantics is unrelated. No
-- additive, multiplicative, or constructive ordinal arithmetic on
-- `rank x` / `rank y` resolves the joint `<ᵇ-+Ω` ∧ `<ᵇʳᶠ-+2`
-- tension (former: `rank-+ x y` must be bounded-in-`y`; latter:
-- must be strict-monotone-in-`y`).
--
-- See `docs/echo-types/buchholz-rank-obstruction.adoc` for the
-- full counterexample, the five attempted routes (rank, direct
-- mutual, tower-stratification, lex measure, inverse-image —
-- *all walled*), and the recommended next moves (WF-restricted
-- `_<ᵇ_`, non-additive denotational measure, or accepting the
-- budgeted form as canonical).
--
-- ## What still ships
--
-- The `rank` function itself is left in this module as a historical
-- artefact and a sanity check that the underlying arithmetic
-- compiles. It is not used downstream. The closing chain
--
--   wf-<ᵇʳᶠ = Subrelation.wellFounded rank-mono
--               (InverseImage.wellFounded rank wf-<′)
--
-- cannot be constructed because `rank-mono-<ᵇ` (the `<ᵇʳᶠ-core`
-- case of `rank-mono`) cannot be inhabited.

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
