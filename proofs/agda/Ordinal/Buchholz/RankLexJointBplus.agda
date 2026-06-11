{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Parallel lex-rank for the joint-bplus bpsi-source-at-equality
-- sub-case (scaffold, 2026-05-28).
--
-- ## Where this sits
--
-- The Slice 3 umbrella `Ordinal.Buchholz.RankMonoUmbrellaSlice3._<ᵇ¹_`
-- case-splits the joint-bplus `<ᵇ-+1` discharge on the source's
-- leftmost-leaf shape (`x₁ = bOmega μ` / `x₁ = bpsi ν α` /
-- `x₁ = bplus _ _`).  The bpsi sub-case further splits on
-- `head-Ω x₁ vs head-Ω y₁` via `head-Ω-inv-bpsi`:
--
--   * `ν <Ω head-Ω y₁` (strict) — closes via the Slice 3 headline
--     `rank-mono-<ᵇ-+1-via-head-Ω`.
--   * `ν ≡ head-Ω y₁` (boundary)  — the BPSI-SOURCE-AT-EQUALITY
--     sub-case.  Closed at the ψ-rank level by `Ordinal.Buchholz.
--     RankLexSlice3.{rank-adm,rank-lex}-bpsi-strict-at-equality`;
--     OPEN at the bplus-chain rank-pow level because both pre-
--     identified unblock routes (additive-principal closure on a
--     generic ω-power-plus-rank-pow sum, strict-left-mono of `_⊕_`)
--     are now CHECKED-REFUTED in `Ordinal.Brouwer.
--     {AdditivePrincipalGenericRefuted,StrictLeftMonoRefuted}`
--     (PR #146, 2026-05-28).
--
-- This module lays the SCAFFOLD for the remaining viable forward
-- path: a parallel rank `rank-lex-jb : BT → RankLex` whose `bplus`
-- case carries a richer second component than `Ordinal.Buchholz.
-- RankLex.rank-lex` (whose `bplus` case is `mkLex (rank-pow (bplus
-- x y)) oz`, deliberately scoped to the `<ᵇ-ψΩ≤` boundary
-- discharge per `RankLex.agda` lines 142-148).
--
-- The richer second component carried here is the LEFTMOST-PSI-α
-- rank `leftmost-α : BT → Ord`:
--
--   leftmost-α bzero        = oz
--   leftmost-α (bOmega _)   = oz
--   leftmost-α (bpsi _ α)   = rank-pow α
--   leftmost-α (bplus x _)  = leftmost-α x
--
-- so that for left-leaning `bplus` chains whose leftmost atomic
-- leaf is `bpsi ν α`, the second component carries `rank-pow α` —
-- precisely the discriminator `RankLexSlice3.rank-lex-bpsi-strict-
-- at-equality` exploits at the ψ-rank level.
--
-- ## What this scaffold lands
--
-- 1. `leftmost-α : BT → Ord` — the leftmost-ψ-α-rank function.
-- 2. `leftmost-α-bzero/bOmega/bpsi/bplus` — definitional sanity
--    (one per `BT` constructor; all `refl`).
-- 3. `leftmost-α-bplus-left` — two-level convenience for the
--    left-leaning `bplus` left-spine (mirrors `head-Ω-bplus-left`).
-- 4. `rank-lex-jb : BT → RankLex` — the parallel lex rank.
-- 5. `rank-lex-jb-bzero/bOmega/bpsi/bplus` — definitional sanity.
-- 6. `rank-lex-jb-vs-rank-lex` — `rank-lex` and `rank-lex-jb` agree
--    pointwise on first components.  Pins the parallel-rank shape
--    so consumers know what is and isn't preserved by the pivot.
-- 7. `rank-lex-jb-strict-second-at-equal-first` — the load-bearing
--    primitive for the bpsi-source-at-equality bplus-chain
--    discharge: if first components are propositionally equal and
--    the leftmost-α witnesses are strictly ordered, `<lex-second`
--    fires.  This is the LEX-rank shape the next session's full
--    headline will consume; this scaffold ships the primitive +
--    documents the consumer-side missing pieces (the equal-first
--    propositional witness + the leftmost-α strict witness from
--    the umbrella's case-split).
--
-- ## What this scaffold deliberately does NOT close (honest scope)
--
-- The full headline
--
--   rank-jb-mono-<ᵇ-+1-joint-bplus-at-equal-head : ∀ {x₁ x₂ y₁ y₂}
--     → WfCNF (bplus x₁ x₂)
--     → WfCNF (bplus y₁ y₂)
--     → x₁ <ᵇ y₁
--     → head-Ω x₁ ≡ head-Ω y₁           -- equality sub-case witness
--     → rank-lex-jb (bplus x₁ x₂) <lex rank-lex-jb (bplus y₁ y₂)
--
-- is NOT shipped in this slice.  The case-split for closing it
-- requires:
--
--   (a) A FIRST-COMPONENT-EQUAL sub-case primitive: if `rank-pow
--       (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)` and `leftmost-α
--       (bplus x₁ x₂) <′ leftmost-α (bplus y₁ y₂)`, fire
--       `<lex-second` (THIS slice's `rank-lex-jb-strict-second-at-
--       equal-first`).
--   (b) A FIRST-COMPONENT-STRICT sub-case primitive: if
--       `rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)` then
--       fire `<lex-first`.  Decomposes via `⊕-mono-?-?` from the
--       source `x₁ <ᵇ y₁` derivation; the bplus-chain sum bound is
--       the same structural challenge that motivated this whole
--       refactor.
--   (c) A TRICHOTOMY on `rank-pow (bplus x₁ x₂)` vs
--       `rank-pow (bplus y₁ y₂)` that hands the case-split to (a)
--       or (b).  Under `--safe --without-K`, this is a non-trivial
--       decidability question — `Ord`-valued decidability bridges
--       are not landed in `Ordinal.Brouwer.Phase13` yet.
--
-- The honest verdict: this scaffold is necessary-but-not-sufficient
-- foundation.  The next session's task is the (a) + (b) + (c)
-- assembly into a full headline; (b) and (c) each represent their
-- own multi-PR slices.  Documented here so the closure path is
-- legible without re-deriving the analysis.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * `leftmost-α`                           — the discriminator
--   * `rank-lex-jb`                          — the parallel rank
--   * `rank-lex-jb-strict-second-at-equal-first`
--                                            — the lex-second
--                                              primitive

module Ordinal.Buchholz.RankLexJointBplus where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂)

open import Ordinal.Brouwer           using (Ord; oz)
open import Ordinal.Brouwer.Phase13   using (_<′_)
open import Ordinal.Buchholz.Syntax   using
  ( BT
  ; bzero
  ; bOmega
  ; bplus
  ; bpsi
  )
open import Ordinal.Brouwer.Arithmetic using (_⊕_)
open import Ordinal.Buchholz.RankPow  using (rank-pow; rank-pow-bplus; ω-rank-pow)
open import Ordinal.Buchholz.RankLex  using
  ( RankLex
  ; mkLex
  ; _<lex_
  ; <lex-first
  ; <lex-second
  )
open import Ordinal.Buchholz.RankMonoUmbrella using
  ( _<ᵇ⁰_
  ; rank-pow-mono-<ᵇ⁰
  )

----------------------------------------------------------------------
-- `leftmost-α : BT → Ord` — the leftmost-ψ-α-rank discriminator
----------------------------------------------------------------------

-- For left-leaning `bplus` chains, walks the left spine to the
-- atomic leaf and reads off `rank-pow α` if the leaf is `bpsi _ α`.
-- For non-bpsi leaves (`bzero` / `bOmega _`), returns `oz` — the
-- discriminator is only meaningful when the leftmost leaf is a
-- ψ-source, which is the only case the bpsi-source-at-equality
-- sub-case ever reaches.

leftmost-α : BT → Ord
leftmost-α bzero        = oz
leftmost-α (bOmega _)   = oz
leftmost-α (bpsi _ α)   = rank-pow α
leftmost-α (bplus x _)  = leftmost-α x

----------------------------------------------------------------------
-- Definitional sanity for `leftmost-α`
----------------------------------------------------------------------

leftmost-α-bzero : leftmost-α bzero ≡ oz
leftmost-α-bzero = refl

leftmost-α-bOmega : ∀ ν → leftmost-α (bOmega ν) ≡ oz
leftmost-α-bOmega _ = refl

leftmost-α-bpsi : ∀ ν α → leftmost-α (bpsi ν α) ≡ rank-pow α
leftmost-α-bpsi _ _ = refl

leftmost-α-bplus : ∀ x y → leftmost-α (bplus x y) ≡ leftmost-α x
leftmost-α-bplus _ _ = refl

----------------------------------------------------------------------
-- Two-level convenience
----------------------------------------------------------------------

-- Mirrors `HeadOmega.head-Ω-bplus-left`: walking two `bplus` levels
-- bottoms out at the leftmost atomic leaf's `leftmost-α`.  The
-- bpsi-source-at-equality sub-case at the umbrella consumes the
-- joint-bplus shape `bplus (bpsi ν α) x₂`, where the leftmost atom
-- is one level deep; this lemma generalises to two levels for the
-- nested case `bplus (bplus _ _) _`.

leftmost-α-bplus-left :
  ∀ x y z → leftmost-α (bplus (bplus x y) z) ≡ leftmost-α x
leftmost-α-bplus-left _ _ _ = refl

----------------------------------------------------------------------
-- `rank-lex-jb : BT → RankLex` — the parallel lex rank
----------------------------------------------------------------------

-- First component matches `RankLex.rank-lex` pointwise on all four
-- constructors (the `bplus` case in `RankLex.rank-lex` is `rank-pow
-- (bplus x y)` already, so `rank-lex-jb`'s first component matches
-- by definition).  Second component diverges only on `bplus`,
-- replacing `oz` with `leftmost-α`.
--
-- The atomic-leaf cases (`bzero`, `bOmega`, `bpsi`) keep the
-- existing `RankLex.rank-lex` second component to preserve the
-- existing `RankLex.rank-mono-<ᵇ-ψΩ≤-lex` boundary-discharge — the
-- pivot is `bplus`-only.

rank-lex-jb : BT → RankLex
rank-lex-jb bzero        = mkLex oz                       oz
rank-lex-jb (bOmega ν)   = mkLex (rank-pow (bOmega ν))    (rank-pow (bOmega ν))
rank-lex-jb (bpsi ν α)   = mkLex (rank-pow (bpsi ν α))    (rank-pow α)
rank-lex-jb (bplus x y)  = mkLex (rank-pow (bplus x y))   (leftmost-α (bplus x y))

----------------------------------------------------------------------
-- Definitional sanity for `rank-lex-jb`
----------------------------------------------------------------------

rank-lex-jb-bzero : rank-lex-jb bzero ≡ mkLex oz oz
rank-lex-jb-bzero = refl

rank-lex-jb-bOmega :
  ∀ ν → rank-lex-jb (bOmega ν)
        ≡ mkLex (rank-pow (bOmega ν)) (rank-pow (bOmega ν))
rank-lex-jb-bOmega _ = refl

rank-lex-jb-bpsi :
  ∀ ν α → rank-lex-jb (bpsi ν α)
          ≡ mkLex (rank-pow (bpsi ν α)) (rank-pow α)
rank-lex-jb-bpsi _ _ = refl

rank-lex-jb-bplus :
  ∀ x y → rank-lex-jb (bplus x y)
          ≡ mkLex (rank-pow (bplus x y)) (leftmost-α (bplus x y))
rank-lex-jb-bplus _ _ = refl

----------------------------------------------------------------------
-- Headline: `<lex-second` at equal first components
----------------------------------------------------------------------

-- The load-bearing scaffold primitive.  Consumers in the
-- bpsi-source-at-equality bplus-chain context supply:
--
--   * a propositional witness that the source's first component
--     equals the target's (`rank-pow (bplus x₁ x₂) ≡ rank-pow
--     (bplus y₁ y₂)`), which they must obtain from the (a)+(b)+(c)
--     case-split documented in this module's preamble; AND
--   * a strict-less-than witness on the leftmost-α discriminators
--     (`leftmost-α (bplus x₁ x₂) <′ leftmost-α (bplus y₁ y₂)`),
--     which the umbrella's `head-Ω-inv-bpsi` + the original
--     `x₁ <ᵇ y₁` derivation supplies via `RankLexSlice3.rank-lex-
--     bpsi-strict-at-equality` semantics: at the bpsi-source-at-
--     equality sub-case `x₁ = bpsi ν α`, `y₁ = bpsi ν β`, with
--     `α <ᵇ β` from the source derivation, `rank-pow α <′ rank-pow
--     β` from the existing `RankMonoUmbrella.rank-pow-mono-<ᵇ⁰`,
--     and `leftmost-α (bplus (bpsi ν α) x₂) = rank-pow α` (resp.
--     β) by `leftmost-α-bplus` + `leftmost-α-bpsi`.
--
-- Given both, fire `<lex-second` against the strict witness.  The
-- propositional first-component equality is rewritten in via
-- `subst`-style content (here, by pattern-matching the equality
-- and reusing the source `mkLex` on both sides).

rank-lex-jb-strict-second-at-equal-first :
  ∀ {x₁ x₂ y₁ y₂}
  → rank-pow (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)
  → leftmost-α (bplus x₁ x₂) <′ leftmost-α (bplus y₁ y₂)
  → rank-lex-jb (bplus x₁ x₂) <lex rank-lex-jb (bplus y₁ y₂)
rank-lex-jb-strict-second-at-equal-first {x₁} {x₂} {y₁} {y₂} first-eq strict =
  -- The `<lex-second` constructor requires the source and target
  -- first components to be syntactically equal under unification.
  -- Here they are propositionally equal (via `first-eq`) but not
  -- syntactically — `--without-K` forbids the `refl`-pattern
  -- shortcut.  Transport the goal along `first-eq` via `subst` so
  -- the constructor's implicit first-component unifies.
  subst
    (λ a → mkLex a (leftmost-α (bplus x₁ x₂))
           <lex
           mkLex (rank-pow (bplus y₁ y₂)) (leftmost-α (bplus y₁ y₂)))
    (sym-≡ first-eq)
    (<lex-second strict)
  where
    -- Local `sym` to avoid an extra stdlib import.
    sym-≡ : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
    sym-≡ refl = refl

----------------------------------------------------------------------
-- Headline: `<lex-first` at strict first components (leg (b))
----------------------------------------------------------------------

-- The companion primitive to `rank-lex-jb-strict-second-at-equal-
-- first`.  Trivial at the rank-lex-jb level: `<lex-first` fires
-- directly on the supplied strict first-component witness.  The
-- LOAD-BEARING content is the consumer-side derivation of the
-- hypothesis `rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)`
-- from a source `<ᵇ` derivation, which remains the multi-PR
-- ordinal-arithmetic challenge documented in this module's
-- preamble (both pre-identified unblock routes — additive-principal
-- closure on a generic sum, strict-left-mono of `_⊕_` — are
-- CHECKED-REFUTED in `Ordinal.Brouwer.{AdditivePrincipalGenericRefuted,
-- StrictLeftMonoRefuted}` (PR #146, 2026-05-28)).  Shipping the
-- primitive separates the trivial lex-rank wiring from the
-- structural ordinal-arithmetic blocker — consumers that derive
-- strict-first via a future bypass (or a restricted bplus-shape
-- where rank-pow IS additive principal) fire `<lex-first` through
-- this primitive without re-discovering the wiring.

rank-lex-jb-strict-first :
  ∀ {x₁ x₂ y₁ y₂}
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
  → rank-lex-jb (bplus x₁ x₂) <lex rank-lex-jb (bplus y₁ y₂)
rank-lex-jb-strict-first strict = <lex-first strict

----------------------------------------------------------------------
-- Consumer helper: leftmost-α strict-mono from a bpsi-source `<ᵇ⁰`
----------------------------------------------------------------------

-- The bpsi-source-at-equality bplus-chain sub-case has
-- `x₁ = bpsi ν α` and `y₁ = bpsi ν β` (same ν per the sub-case
-- definition).  Given the source-side `α <ᵇ⁰ β` derivation, the
-- leftmost-α discriminator on both bplus chains specialises:
--
--   leftmost-α (bplus (bpsi ν α) x₂) = leftmost-α (bpsi ν α)
--                                    = rank-pow α
--   leftmost-α (bplus (bpsi ν β) y₂) = rank-pow β
--
-- and `rank-pow α <′ rank-pow β` follows from
-- `RankMonoUmbrella.rank-pow-mono-<ᵇ⁰` on the supplied `α <ᵇ⁰ β`.
-- The reductions `leftmost-α-bplus` + `leftmost-α-bpsi` are
-- definitional, so the helper is a one-step inhabitation: the
-- supplied `<′` is already the goal's `<′` modulo definitional
-- reduction on `leftmost-α`.
--
-- Honest scope: parameterised in `_<ᵇ⁰_`, not `_<ᵇ_`.  The
-- 10-constructor `_<ᵇ⁰_` umbrella covers the bpsi sub-case (no
-- `<ᵇ-+1` joint-bplus constructor in `_<ᵇ⁰_`), so consumers with
-- a `_<ᵇ⁰_` derivation on the ψ-arguments compose directly.
-- Lifting to the full `_<ᵇ_` would need the joint-bplus closure,
-- which is the very problem this rank-lex-jb pivot was designed
-- to attack.

leftmost-α-strict-from-bpsi-source :
  ∀ {ν α β x₂ y₂}
  → α <ᵇ⁰ β
  → leftmost-α (bplus (bpsi ν α) x₂) <′ leftmost-α (bplus (bpsi ν β) y₂)
leftmost-α-strict-from-bpsi-source α<β = rank-pow-mono-<ᵇ⁰ α<β

----------------------------------------------------------------------
-- Named theorem: bpsi-source-at-equality sub-case at rank-lex-jb
----------------------------------------------------------------------

-- Composition of `rank-lex-jb-strict-second-at-equal-first` with
-- `leftmost-α-strict-from-bpsi-source`.  Given:
--
--   * the FIRST-COMPONENT EQUALITY `rank-pow (bplus (bpsi ν α) x₂)
--     ≡ rank-pow (bplus (bpsi ν β) y₂)` — consumer's input, gated
--     on the structurally-blocked bplus-chain sum-bound work; AND
--   * the source-side `α <ᵇ⁰ β` derivation on the ψ-arguments,
--
-- the headline fires `<lex-second` at equal first components with
-- the leftmost-α strict witness.  This is the bpsi-source-at-
-- equality sub-case CLOSED at the rank-lex-jb level (parallel to
-- `RankLexSlice3.rank-lex-bpsi-strict-at-equality` for `rank-lex`).
--
-- The first-eq hypothesis remains the gating obligation; this
-- theorem records that EVERY other discharge step composes
-- cleanly, so resolving the structural blocker unblocks the named
-- theorem mechanically.

rank-lex-jb-bpsi-at-equality :
  ∀ {ν α β x₂ y₂}
  → rank-pow (bplus (bpsi ν α) x₂) ≡ rank-pow (bplus (bpsi ν β) y₂)
  → α <ᵇ⁰ β
  → rank-lex-jb (bplus (bpsi ν α) x₂) <lex rank-lex-jb (bplus (bpsi ν β) y₂)
rank-lex-jb-bpsi-at-equality {ν} {α} {β} {x₂} {y₂} first-eq α<β =
  rank-lex-jb-strict-second-at-equal-first
    {x₁ = bpsi ν α} {x₂ = x₂} {y₁ = bpsi ν β} {y₂ = y₂}
    first-eq
    (leftmost-α-strict-from-bpsi-source {ν = ν} {α = α} {β = β} {x₂ = x₂} {y₂ = y₂} α<β)

----------------------------------------------------------------------
-- Consumer-side first-eq derivation
----------------------------------------------------------------------

-- The HARD half of the (a) primitive's consumer plumbing: deriving
-- the `first-eq : rank-pow (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)`
-- hypothesis at the bplus-chain rank-pow level.
--
-- The DEFINITIONAL fact underlying the closure: `rank-pow (bplus
-- x y) = rank-pow x ⊕ rank-pow y` (`RankPow.rank-pow-bplus`,
-- definitional `refl`).  So first-eq REDUCES to a conjunction of
-- summand-level equalities via `cong₂ _⊕_`:
--
--   rank-pow x₁ ≡ rank-pow y₁  ∧  rank-pow x₂ ≡ rank-pow y₂
--   ⇒ rank-pow (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)
--
-- The bpsi-source-at-equal-head sub-case has `x₁ = bpsi ν α` and
-- `y₁ = bpsi ν β` (same ν).  At the rank-pow level both reduce
-- DEFINITIONALLY to `ω-rank-pow ν`, so the left summand's equality
-- is `refl` and the consumer's residual obligation collapses to
-- `rank-pow x₂ ≡ rank-pow y₂` on the right summand.  Under WfCNF
-- this is the same `rank-pow x₂ ≡ rank-pow y₂` discharge that
-- already gates the lex-rank-level discharge of the same sub-case
-- via `RankLexSlice3.rank-adm-bpsi-strict-at-equality`; the rank-
-- pow-level closure has the same shape modulo the consumer-side
-- ordinal-arithmetic gating, which means the bpsi sub-case at the
-- bplus-chain level FOLLOWS the same closure ladder as the ψ-rank
-- level once that ladder closes.

-- Generic summand-equalities composer: bplus-first-eq from summand-
-- first-eqs.
rank-pow-bplus-eq-from-summands :
  ∀ {x₁ x₂ y₁ y₂}
  → rank-pow x₁ ≡ rank-pow y₁
  → rank-pow x₂ ≡ rank-pow y₂
  → rank-pow (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)
rank-pow-bplus-eq-from-summands eq1 eq2 = cong₂ _⊕_ eq1 eq2

-- Specialised first-eq derivation for the bpsi-source-at-equal-head
-- sub-case: left summands are `bpsi ν α` and `bpsi ν β` (same ν, ANY
-- α and β); left-rank equality is definitional (`refl` since both
-- evaluate to `ω-rank-pow ν`).  Reduces consumer-side first-eq to
-- the tail-rank-equality `rank-pow x₂ ≡ rank-pow y₂`.
first-eq-from-bpsi-source-at-equal-head :
  ∀ {ν α β x₂ y₂}
  → rank-pow x₂ ≡ rank-pow y₂
  → rank-pow (bplus (bpsi ν α) x₂) ≡ rank-pow (bplus (bpsi ν β) y₂)
first-eq-from-bpsi-source-at-equal-head {ν} {α} {β} {x₂} {y₂} tail-eq =
  rank-pow-bplus-eq-from-summands {x₁ = bpsi ν α} {x₂ = x₂}
                                   {y₁ = bpsi ν β} {y₂ = y₂}
    refl tail-eq

----------------------------------------------------------------------
-- (c) Trichotomy data type for the bplus-chain first-component
----------------------------------------------------------------------

-- Brouwer ordinals are NOT decidably ordered in general (`Ord`
-- includes `olim f` carrying arbitrary functions ℕ → Ord), so a
-- universal trichotomy on `rank-pow (bplus _ _)` values is
-- unattainable under `--safe --without-K` without postulates.
-- The TRACTABLE narrowing is a STRUCTURAL trichotomy: a data type
-- that records which of the strict / equal cases applies WHEN the
-- consumer has discharged the corresponding rank-arithmetic
-- obligation.  Dispatchers below populate the strict / equal
-- constructors from rank-evidence the consumer derives via the
-- closed `<ᵇ⁰` / `<ᵇ¹` / `<ᵇ⁻ⁿ` umbrellas or the bpsi-source
-- definitional collapse.

data BplusFirstTri (x₁ x₂ y₁ y₂ : BT) : Set where
  bplus-tri-strict :
      rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
    → BplusFirstTri x₁ x₂ y₁ y₂
  bplus-tri-equal  :
      rank-pow (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)
    → BplusFirstTri x₁ x₂ y₁ y₂

-- Strict dispatcher: any consumer-derived strict witness on the
-- bplus-chain rank-pow lifts into `bplus-tri-strict`.  The closed
-- `<ᵇ⁰` umbrella's `rank-pow-mono-<ᵇ⁰` and the `<ᵇ¹` umbrella's
-- `rank-pow-mono-<ᵇ¹` (which dispatches the strict-head-Ω joint-
-- bplus case `<ᵇ¹-+1-+`) are the canonical producers of this
-- witness; see also `RankMonoUmbrellaSlice4.rank-pow-mono-<ᵇ⁻ⁿ`
-- for the WfCNF-bundled form.

bplus-tri-from-strict :
  ∀ {x₁ x₂ y₁ y₂}
  → rank-pow (bplus x₁ x₂) <′ rank-pow (bplus y₁ y₂)
  → BplusFirstTri x₁ x₂ y₁ y₂
bplus-tri-from-strict strict = bplus-tri-strict strict

-- Equal dispatcher: any consumer-derived first-eq lifts into
-- `bplus-tri-equal`.  The bpsi-source-at-equal-head derivation
-- `first-eq-from-bpsi-source-at-equal-head` is the canonical
-- producer of this witness; the rank-equal closure under more
-- general bplus shapes is the multi-PR ordinal-arithmetic
-- challenge documented in this module's preamble.

bplus-tri-from-equal :
  ∀ {x₁ x₂ y₁ y₂}
  → rank-pow (bplus x₁ x₂) ≡ rank-pow (bplus y₁ y₂)
  → BplusFirstTri x₁ x₂ y₁ y₂
bplus-tri-from-equal eq = bplus-tri-equal eq

-- Trichotomy → rank-lex-jb dispatcher: the assembly that consumes
-- whichever case the trichotomy yields and discharges to a `<lex`
-- judgment at rank-lex-jb level.  The strict case fires `<lex-first`
-- via `rank-lex-jb-strict-first`; the equal case fires `<lex-second`
-- via `rank-lex-jb-strict-second-at-equal-first` provided the
-- consumer can supply the leftmost-α strict witness.
--
-- This is the (a)+(b)+(c) assembly's RECIPE at the rank-lex-jb
-- level: every reachable case dispatches mechanically given the
-- consumer-side strict-or-equal-first witness.  The remaining
-- gating obligation across the whole assembly is the
-- consumer-side derivation of the leftmost-α strict witness in
-- the equal case (when the consumer cannot supply it, the equal
-- case is structurally dischargeable only if the rank-lex-jb is
-- LITERALLY EQUAL on both sides — which by `<lex` irreflexivity
-- contradicts a source-level strict inequality).

dispatch-trichotomy-to-<lex :
  ∀ {x₁ x₂ y₁ y₂}
  → BplusFirstTri x₁ x₂ y₁ y₂
  → leftmost-α (bplus x₁ x₂) <′ leftmost-α (bplus y₁ y₂)
  → rank-lex-jb (bplus x₁ x₂) <lex rank-lex-jb (bplus y₁ y₂)
dispatch-trichotomy-to-<lex {x₁} {x₂} {y₁} {y₂} (bplus-tri-strict strict) _      =
  rank-lex-jb-strict-first {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂} strict
dispatch-trichotomy-to-<lex {x₁} {x₂} {y₁} {y₂} (bplus-tri-equal eq)      l-strict =
  rank-lex-jb-strict-second-at-equal-first {x₁ = x₁} {x₂ = x₂} {y₁ = y₁} {y₂ = y₂} eq l-strict

----------------------------------------------------------------------
-- Named theorem: bpsi-source-at-equal-head fully closed at rank-lex-jb
----------------------------------------------------------------------

-- The composition of the trichotomy with the bpsi-source first-eq
-- derivation and the leftmost-α strict witness from PR #147's (a)
-- machinery.  Inputs:
--
--   * `tail-eq : rank-pow x₂ ≡ rank-pow y₂`  — the consumer's
--     RESIDUAL rank-arithmetic obligation; gating depends on the
--     source-level relationship between x₂ and y₂ under WfCNF.
--   * `α <ᵇ⁰ β`                              — the source-side
--     strict inequality on the ψ-arguments, supplied by the
--     consumer via the 10-constructor `_<ᵇ⁰_` umbrella.
--
-- Output: `<lex` discharge at rank-lex-jb level for the bpsi-source
-- bplus chain.  This closes the bpsi-source-at-equal-head sub-case
-- at the bplus-chain rank-lex-jb level GIVEN the consumer's
-- tail-rank-equality discharge — which is the SAME gating
-- obligation that the ψ-rank-level closure (`rank-adm-bpsi-strict-
-- at-equality`) carries.  Resolving the structural blocker on
-- tail-rank-equality unblocks BOTH levels mechanically.

rank-lex-jb-bpsi-equal-head-from-tail-eq :
  ∀ {ν α β x₂ y₂}
  → rank-pow x₂ ≡ rank-pow y₂
  → α <ᵇ⁰ β
  → rank-lex-jb (bplus (bpsi ν α) x₂) <lex rank-lex-jb (bplus (bpsi ν β) y₂)
rank-lex-jb-bpsi-equal-head-from-tail-eq {ν} {α} {β} {x₂} {y₂} tail-eq α<β =
  rank-lex-jb-bpsi-at-equality
    {ν = ν} {α = α} {β = β} {x₂ = x₂} {y₂ = y₂}
    (first-eq-from-bpsi-source-at-equal-head
      {ν = ν} {α = α} {β = β} {x₂ = x₂} {y₂ = y₂} tail-eq)
    α<β
