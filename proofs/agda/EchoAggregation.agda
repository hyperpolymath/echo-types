{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoAggregation: aggregation-as-fold over a monoid, with the
-- structured-loss (Echo / no-section) reading.
--
-- This module is the GENERAL aggregation form requested by issue #175
-- (a `Monoid` carrier + a `GroupAggregator`, for the SQL group-by /
-- aggregation-as-monoid-homomorphism consumer in affinescript
-- db-theory #3).  Aggregation-as-Echo is a *fundamental* of echo-types,
-- so the clean name `EchoAggregation` names the general construction.
--
-- The MACRO-economics reading — rolling a micro ledger up into a macro
-- observable, and the Sonnenschein–Mantel–Debreu / representative-agent
-- "you cannot disaggregate" critique — is the oikos `alib` bridge's
-- *interpretation* of this general form.  It lives in
-- `oikos/docs/alib-aggregate-bridge.adoc` and cites the
-- `Example-PairSum` instance below.  Because aggregation is a
-- fundamental here, naming the macro instance `EchoAggregation` over in
-- oikos would be odd; oikos names it `MacroAggregation` and cites back.
--
-- ## What lands (all --safe --without-K, zero postulates)
--
--   * `Monoid`            — the aggregation carrier (#175):
--                           `ε`, `_⊕_`, `assoc`, `identity-l`,
--                           `identity-r`.
--   * `GroupAggregator`   — a value→element aggregator over a monoid,
--                           keyed by `K` (#175).
--   * `⊕-fold` / `⊕-fold-++`
--                         — fold a list through the monoid; the fold is a
--                           monoid homomorphism (it distributes over
--                           `_++_`).
--   * `aggregate-values` / `aggregation-as-fold`
--                         — group-aggregation as a fold, and its
--                           homomorphism law (the #175 "aggregation-as-
--                           fold" property — PROVED here, not merely
--                           signed: aggregating a concatenation equals
--                           combining the aggregates).
--   * `sumMonoid` / `countMonoid` / `maxMonoid` / `minMonoid`
--                         — the four concrete instances #175 asks for
--                           (`min` over `ℕ ∪ {∞}` via `Maybe ℕ`,
--                           `nothing` = ∞).
--   * `countAggregator`   — a worked `GroupAggregator` (every value
--                           contributes 1 to `sumMonoid`).
--   * `no-canonical-disaggregation-of`
--                         — generic non-disaggregability: any aggregation
--                           with a collision admits NO section (a LEFT
--                           inverse).  A re-export of
--                           `EchoNoSectionGeneric.no-section-of-collapsing-map`
--                           at aggregation-flavoured names; also covers
--                           issue #174's no-section sibling.
--   * `module Example-PairSum`
--                         — the worked instance: a two-field record summed
--                           to a total (`ℕ × ℕ → ℕ`).  It is non-injective
--                           and admits no section; and `pairSum` IS the
--                           `sumMonoid` fold of its two fields
--                           (`pairSum-is-fold`).  This is the mechanised
--                           anchor the oikos macro reading cites.
--
-- ## Honest scope
--
-- `aggregation-as-fold` is the monoid-homomorphism property of the fold
-- (folding a concatenation = combining the folds).  It is NOT a claim
-- about SQL GROUP-BY's full operational semantics.  `avg` is
-- deliberately absent: it is not a monoid (no identity); express it as
-- `sum / count`, per #175.  `no-canonical-disaggregation-of` refutes a
-- section (a left inverse), NOT the existence of *some* representative
-- choice — economists pick representatives all the time; the content is
-- that no such choice is canonical.

module EchoAggregation where

open import Echo                 using (Echo; echo-intro)
open import EchoNoSectionGeneric using (no-section-of-collapsing-map)

open import Level                using (Level; 0ℓ; suc)
open import Data.Nat.Base        using (ℕ; _+_; _⊔_; _⊓_)
open import Data.Nat.Properties  using ( +-assoc; +-identityˡ; +-identityʳ
                                       ; ⊔-assoc; ⊔-identityˡ; ⊔-identityʳ
                                       ; ⊓-assoc )
open import Data.Maybe.Base      using (Maybe; just; nothing)
open import Data.List.Base       using (List; []; _∷_; _++_; map; foldr)
open import Data.Product.Base    using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary     using (¬_)

----------------------------------------------------------------------
-- The aggregation carrier: a monoid (issue #175).
----------------------------------------------------------------------

record Monoid (ℓ : Level) : Set (suc ℓ) where
  field
    Elem       : Set ℓ
    ε          : Elem
    _⊕_        : Elem → Elem → Elem
    assoc      : (a b c : Elem) → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
    identity-l : (a : Elem) → ε ⊕ a ≡ a
    identity-r : (a : Elem) → a ⊕ ε ≡ a

----------------------------------------------------------------------
-- Folding a list through a monoid, and the homomorphism law.
--
-- `⊕-fold M` is the monoid fold; `⊕-fold-++` proves it is a monoid
-- homomorphism on `(List Elem, _++_, [])` → `(Elem, _⊕_, ε)`:
-- folding a concatenation equals combining the two folds.  Stated
-- top-level (taking `M` explicitly) so the headlines pin directly.
----------------------------------------------------------------------

⊕-fold : ∀ {ℓ} (M : Monoid ℓ) → List (Monoid.Elem M) → Monoid.Elem M
⊕-fold M = foldr (Monoid._⊕_ M) (Monoid.ε M)

⊕-fold-++ : ∀ {ℓ} (M : Monoid ℓ) (xs ys : List (Monoid.Elem M)) →
            ⊕-fold M (xs ++ ys) ≡ Monoid._⊕_ M (⊕-fold M xs) (⊕-fold M ys)
⊕-fold-++ M []       ys = sym (Monoid.identity-l M (⊕-fold M ys))
⊕-fold-++ M (x ∷ xs) ys =
  trans (cong (Monoid._⊕_ M x) (⊕-fold-++ M xs ys))
        (sym (Monoid.assoc M x (⊕-fold M xs) (⊕-fold M ys)))

----------------------------------------------------------------------
-- Group aggregator (issue #175): a value→element map over a monoid,
-- keyed by `K` (the group-by key; phantom in the carrier, used by the
-- SQL consumer to partition rows before folding each group).
----------------------------------------------------------------------

record GroupAggregator {ℓ} (K V : Set) (M : Monoid ℓ) : Set ℓ where
  field
    agg : V → Monoid.Elem M

-- Aggregate a list of values: map the aggregator, then fold.
aggregate-values : ∀ {ℓ} {K V : Set} {M : Monoid ℓ}
                 → GroupAggregator K V M → List V → Monoid.Elem M
aggregate-values {M = M} G vs = ⊕-fold M (map (GroupAggregator.agg G) vs)

-- Aggregation-as-fold (the #175 headline law): aggregating a
-- concatenation equals combining the two aggregates.  Proved by
-- induction (no `map-++` lemma needed — the cons case reduces
-- definitionally through `map` and `foldr`).
aggregation-as-fold : ∀ {ℓ} {K V : Set} {M : Monoid ℓ}
                      (G : GroupAggregator K V M) (vs ws : List V) →
                      aggregate-values G (vs ++ ws)
                        ≡ Monoid._⊕_ M (aggregate-values G vs) (aggregate-values G ws)
aggregation-as-fold {M = M} G []       ws =
  sym (Monoid.identity-l M (aggregate-values G ws))
aggregation-as-fold {M = M} G (v ∷ vs) ws =
  trans (cong (Monoid._⊕_ M (GroupAggregator.agg G v)) (aggregation-as-fold G vs ws))
        (sym (Monoid.assoc M (GroupAggregator.agg G v)
                             (aggregate-values G vs) (aggregate-values G ws)))

----------------------------------------------------------------------
-- The four concrete monoid instances (issue #175).
----------------------------------------------------------------------

-- Sum / count: (ℕ, 0, +).  `count` is "sum of 1s" — the SAME monoid;
-- the counting happens in the aggregator (`countAggregator`).
sumMonoid : Monoid 0ℓ
sumMonoid = record
  { Elem = ℕ ; ε = 0 ; _⊕_ = _+_
  ; assoc = +-assoc ; identity-l = +-identityˡ ; identity-r = +-identityʳ }

countMonoid : Monoid 0ℓ
countMonoid = sumMonoid

-- Max: (ℕ, 0, ⊔).  0 is the max-identity on ℕ (0 ≤ n for all n).
maxMonoid : Monoid 0ℓ
maxMonoid = record
  { Elem = ℕ ; ε = 0 ; _⊕_ = _⊔_
  ; assoc = ⊔-assoc ; identity-l = ⊔-identityˡ ; identity-r = ⊔-identityʳ }

-- Min: (ℕ ∪ {∞}, ∞, ⊓).  `ℕ` has no top, so adjoin one as `nothing`
-- (= ∞, the min-identity); `just n` = n.
_⊓∞_ : Maybe ℕ → Maybe ℕ → Maybe ℕ
nothing ⊓∞ y       = y
just a  ⊓∞ nothing = just a
just a  ⊓∞ just b  = just (a ⊓ b)

⊓∞-identity-r : (x : Maybe ℕ) → x ⊓∞ nothing ≡ x
⊓∞-identity-r nothing  = refl
⊓∞-identity-r (just a) = refl

⊓∞-assoc : (x y z : Maybe ℕ) → (x ⊓∞ y) ⊓∞ z ≡ x ⊓∞ (y ⊓∞ z)
⊓∞-assoc nothing  y        z        = refl
⊓∞-assoc (just a) nothing  z        = refl
⊓∞-assoc (just a) (just b) nothing  = refl
⊓∞-assoc (just a) (just b) (just c) = cong just (⊓-assoc a b c)

minMonoid : Monoid 0ℓ
minMonoid = record
  { Elem = Maybe ℕ ; ε = nothing ; _⊕_ = _⊓∞_
  ; assoc = ⊓∞-assoc ; identity-l = λ _ → refl ; identity-r = ⊓∞-identity-r }

-- A worked aggregator: count.  Every value contributes 1 to the sum
-- monoid; `aggregate-values countAggregator` is then list length, and
-- `aggregation-as-fold` specialises to "count of a concatenation =
-- sum of the counts".
countAggregator : ∀ {K V : Set} → GroupAggregator K V sumMonoid
countAggregator = record { agg = λ _ → 1 }

----------------------------------------------------------------------
-- Generic non-disaggregability.
--
-- Any aggregation map with a collision (two distinct inputs, the same
-- output) admits NO section: there is no `raise` recovering the input
-- from the aggregate for every input.  This is exactly
-- `EchoNoSectionGeneric.no-section-of-collapsing-map` at aggregation-
-- flavoured names, and it is also issue #174's no-section sibling.
----------------------------------------------------------------------

no-canonical-disaggregation-of :
  ∀ {a r} {A : Set a} {R : Set r}
  (agg-map : A → R) (x y : A) → x ≢ y → agg-map x ≡ agg-map y →
  ¬ Σ (R → A) (λ raise → ∀ z → raise (agg-map z) ≡ z)
no-canonical-disaggregation-of agg-map x y x≢y collides =
  no-section-of-collapsing-map agg-map x y x≢y collides

----------------------------------------------------------------------
-- Worked instance: a two-field record summed to a total.
--
-- The smallest faithful aggregation — `ℕ × ℕ → ℕ` by `+`.  This is the
-- mechanised anchor the oikos macro-economics reading cites (a micro
-- ledger of two sector balances rolled up into one Godley column
-- total).  It exhibits, concretely:
--
--   * `pairSum-is-fold`        — `pairSum` IS the `sumMonoid` fold of
--                                the two fields (it is an instance of
--                                the general form, not a separate idea);
--   * `pairSum-non-injective`  — two distinct ledgers, same total,
--                                distinct echoes ("aggregation is
--                                many-to-one", as a theorem);
--   * `no-canonical-disaggregation`
--                              — no section: the total cannot in general
--                                be disaggregated (SMD / representative-
--                                agent critique, type-theoretically).
----------------------------------------------------------------------

module Example-PairSum where

  Pair : Set
  Pair = ℕ × ℕ

  pairSum : Pair → ℕ
  pairSum (a , b) = a + b

  -- `pairSum` is exactly the `sumMonoid` fold of its two fields, so the
  -- macro instance is a *special case* of the general aggregation form.
  pairSum-is-fold : (p : Pair) → pairSum p ≡ ⊕-fold sumMonoid (proj₁ p ∷ proj₂ p ∷ [])
  pairSum-is-fold (a , b) = cong (a +_) (sym (+-identityʳ b))

  -- The fibre over total 1 is non-trivial: (0,1) and (1,0) both sum to 1.
  ledger₁ : Pair
  ledger₁ = 0 , 1

  ledger₂ : Pair
  ledger₂ = 1 , 0

  ledger₁≢ledger₂ : ledger₁ ≢ ledger₂
  ledger₁≢ledger₂ eq with cong proj₁ eq
  ... | ()

  pairSum-collapses : pairSum ledger₁ ≡ pairSum ledger₂
  pairSum-collapses = refl

  echo-ledger₁ : Echo pairSum 1
  echo-ledger₁ = echo-intro pairSum ledger₁

  echo-ledger₂ : Echo pairSum 1
  echo-ledger₂ = echo-intro pairSum ledger₂

  pairSum-non-injective : echo-ledger₁ ≢ echo-ledger₂
  pairSum-non-injective eq = ledger₁≢ledger₂ (cong proj₁ eq)

  -- The keystone: no canonical disaggregation of the total.
  no-canonical-disaggregation :
    ¬ Σ (ℕ → Pair) (λ raise → ∀ p → raise (pairSum p) ≡ p)
  no-canonical-disaggregation =
    no-canonical-disaggregation-of pairSum ledger₁ ledger₂ ledger₁≢ledger₂ pairSum-collapses
