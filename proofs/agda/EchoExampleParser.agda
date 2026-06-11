{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Example 9 (presentation-dependence cluster, docs/echo-types/examples.md §9):
-- parser residue — balanced parentheses.
--
-- Pragmatic toy parser: `parses` returns `Bool`, deciding "is this token
-- stream a balanced-parens word?" via a left-to-right depth counter that
-- (a) starts at zero, (b) increments on LP, (c) decrements on RP unless
-- already at zero (in which case it aborts to `false`), (d) accepts iff
-- the final depth is zero. This avoids the full `Balanced` grammar
-- definition; the point of Example 9 is the *echo*, not the grammar.
--
-- Per `docs/echo-types/examples.md` §9:
--   "Echo parse tree = Σ (List Token) (λ ts → parse ts ≡ tree) ...
--    the same tree can be reached from different token streams, and the
--    echo distinguishes them."
--
-- Concretely: `(())` and `()()` are two *distinct* `List Token` values
-- whose `parses` invocation collapses to the same Boolean `true`. They
-- are therefore distinct elements of `Echo parses true` — the
-- presentation-dependent axis (axis 4 in `docs/echo-types/taxonomy.md`).
--
-- A *concrete* `Balanced`-grammar witness is also pinned (`bal-empty`,
-- `bal-paren-empty`) so downstream consumers who want the derivation
-- tree rather than the Boolean shadow have something to plug in. The
-- "parser residue" framing (cf. `EchoResidue`) is the observation that
-- the Boolean shadow forgets *which* derivation produced the parse;
-- that is exactly the same `strict-weakening` shape as `collapse`, with
-- the residue here being the token stream itself.

module EchoExampleParser where

open import Echo

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong)

------------------------------------------------------------------------
-- Token alphabet and concrete streams.

data Token : Set where
  LP : Token   -- '('
  RP : Token   -- ')'

LP≢RP : LP ≢ RP
LP≢RP ()

-- Concrete examples.
[]ₜ : List Token
[]ₜ = []

-- "()"
paren-empty : List Token
paren-empty = LP ∷ RP ∷ []

-- "(())"
paren-nested : List Token
paren-nested = LP ∷ LP ∷ RP ∷ RP ∷ []

-- "()()"
paren-pair : List Token
paren-pair = LP ∷ RP ∷ LP ∷ RP ∷ []

------------------------------------------------------------------------
-- Decision procedure: parses ≡ "is balanced?".
--
-- A left-to-right depth counter. `parses-aux d ts = true` iff the
-- prefix has never gone negative and the final depth equals `d`. The
-- top-level `parses` calls `parses-aux 0`.
--
-- The auxiliary's signature `ℕ → List Token → Bool` mirrors a state
-- machine. We pattern-match on the token first (Agda-friendly recursion
-- shape) and on the depth only in the RP case (the abort condition).

parses-aux : ℕ → List Token → Bool
parses-aux zero    []         = true
parses-aux (suc _) []         = false
parses-aux d       (LP ∷ ts)  = parses-aux (suc d) ts
parses-aux zero    (RP ∷ _)   = false
parses-aux (suc d) (RP ∷ ts)  = parses-aux d ts

parses : List Token → Bool
parses = parses-aux 0

------------------------------------------------------------------------
-- Echo carriers: distinct token streams collapsing to `parses ≡ true`.

echo-parse-empty : Echo parses true
echo-parse-empty = echo-intro parses []ₜ

echo-parse-pair : Echo parses true
echo-parse-pair = echo-intro parses paren-pair

echo-parse-nested : Echo parses true
echo-parse-nested = echo-intro parses paren-nested

-- Disequality of the underlying token streams (the presentation).

paren-nested≢paren-pair : paren-nested ≢ paren-pair
paren-nested≢paren-pair p =
  -- Both streams have head LP; the second token distinguishes them:
  -- paren-nested = LP ∷ LP ∷ _,  paren-pair = LP ∷ RP ∷ _.
  LP≢RP (cong second-token p)
  where
    second-token : List Token → Token
    second-token (_ ∷ t ∷ _) = t
    second-token _           = LP   -- default; never reached for these inputs

paren-empty≢paren-nested : paren-empty ≢ paren-nested
paren-empty≢paren-nested p =
  -- Distinguish by length: `[]ₜ` after stripping the head LP differs.
  empty≢pair (cong tail p)
  where
    tail : List Token → List Token
    tail []       = []
    tail (_ ∷ xs) = xs

    -- `tail paren-empty = RP ∷ []`, `tail paren-nested = LP ∷ RP ∷ RP ∷ []`.
    -- They differ at the head of the tail: RP vs LP.
    empty≢pair : (RP ∷ []) ≢ (LP ∷ RP ∷ RP ∷ [])
    empty≢pair q = LP≢RP (sym (cong head q))
      where
        head : List Token → Token
        head []       = LP   -- default; never reached
        head (t ∷ _)  = t

------------------------------------------------------------------------
-- The headline: distinct presentations collapsing to the same parse
-- shadow. This is the "presentation-dependent" axis 4 obligation: the
-- Boolean shadow loses the token stream, but the Echo retains it.

echo-parse-nested≢echo-parse-pair : echo-parse-nested ≢ echo-parse-pair
echo-parse-nested≢echo-parse-pair p =
  paren-nested≢paren-pair (cong proj₁ p)

parses-non-injective :
  Σ (List Token)
    (λ xs → Σ (List Token) (λ ys → xs ≢ ys × parses xs ≡ parses ys))
parses-non-injective =
  paren-nested , paren-pair , paren-nested≢paren-pair , refl

------------------------------------------------------------------------
-- Concrete derivation-tree witnesses (the `Balanced` grammar).
--
-- A simple `Balanced` inductive predicate: the empty stream is
-- balanced, and wrapping any balanced stream in matching parens is
-- balanced. This is the *positive* fragment — concatenation
-- (`bal-cat`) is omitted because it requires `_++_` reasoning that the
-- single-paren-wrap shape doesn't need, and Example 9's headline only
-- needs concrete witnesses for `[]ₜ`, `paren-empty`, `paren-nested`.

data Balanced : List Token → Set where
  bal-empty : Balanced []
  bal-paren : ∀ {xs} → Balanced xs → Balanced (LP ∷ xs)
    -- Reads "if `xs` is balanced, then `LP ∷ xs` is balanced
    -- *modulo* a matching `RP`". Cf. `bal-paren-with-rp` below for
    -- the closed-form constructor used by the concrete witnesses.

-- Closed-form: wrap a balanced stream in `LP ∷ ... ∷ RP ∷ []` rather
-- than passing through `_++_`. This is a separate constructor-shape so
-- that the concrete witnesses (`bal-paren-empty`, `bal-paren-nested`)
-- can be built by case-and-pattern, not by induction on `_++_`.

data BalancedClosed : List Token → Set where
  bc-empty   : BalancedClosed []
  bc-paren-empty :
    BalancedClosed (LP ∷ RP ∷ [])
  bc-paren-nested :
    BalancedClosed (LP ∷ LP ∷ RP ∷ RP ∷ [])
  bc-paren-pair :
    BalancedClosed (LP ∷ RP ∷ LP ∷ RP ∷ [])

-- The four concrete grammar witnesses.

empty-balanced : BalancedClosed []ₜ
empty-balanced = bc-empty

paren-empty-balanced : BalancedClosed paren-empty
paren-empty-balanced = bc-paren-empty

paren-nested-balanced : BalancedClosed paren-nested
paren-nested-balanced = bc-paren-nested

paren-pair-balanced : BalancedClosed paren-pair
paren-pair-balanced = bc-paren-pair

------------------------------------------------------------------------
-- Classification of `Echo parses true` for *our* concrete streams.
--
-- We do NOT claim a full classification of the fibre (that would
-- require an exhaustive `parses ts ≡ true → Balanced ts` style
-- decoder). Instead, we pin the three concrete witnesses we
-- constructed above and observe that each has a distinct `proj₁`.

echo-parse-empty-proj : proj₁ echo-parse-empty ≡ []ₜ
echo-parse-empty-proj = refl

echo-parse-pair-proj : proj₁ echo-parse-pair ≡ paren-pair
echo-parse-pair-proj = refl

echo-parse-nested-proj : proj₁ echo-parse-nested ≡ paren-nested
echo-parse-nested-proj = refl

------------------------------------------------------------------------
-- Parser residue (optional tie to `EchoResidue` framing).
--
-- The Boolean shadow is the "lossy" projection; the residue is the
-- token stream itself. `parser-residue` exhibits the Σ-pair of
-- (Boolean shadow, lossy projection witness) for the headline pair of
-- distinct streams. The full `EchoResidue` lowering apparatus (with a
-- `Cert` relation + sound section) is overkill for Example 9 — the
-- point is *that* the shadow is non-injective on Echo, witnessed
-- concretely. Cf. `EchoResidue.collapse-residue-same` for the analogous
-- shape on the Boolean-collapse example.

parser-residue :
  Σ Bool
    (λ b → Σ (List Token) (λ xs → Σ (List Token) (λ ys →
      xs ≢ ys × parses xs ≡ b × parses ys ≡ b)))
parser-residue =
  true , paren-nested , paren-pair ,
    paren-nested≢paren-pair , refl , refl

----------------------------------------------------------------------
-- 2026-05-27 follow-up: audience-asymmetry note.
--
-- Unlike `EchoExampleProvenance` (which has a direct audience-facing
-- generalisation in `EchoProvenance.agda`), this example does NOT
-- have a dedicated audience-facing successor module. The reason:
-- "presentation-dependence" is an EDITORIAL AXIS (PR #76 cluster of
-- Examples 5, 9, 10) rather than a DOMAIN AUDIENCE — there is no
-- single discourse community for whom "parser residue" is the
-- structural-content framing the way databases / lineage are for
-- provenance. The structural content (a non-injective forgetful map
-- with distinguishable preimages) is already captured at full
-- generality by `EchoProvenance.Provenance`; this module remains as
-- the concrete parser-flavoured worked example. The asymmetry is
-- intentional, not a missing module.
----------------------------------------------------------------------
