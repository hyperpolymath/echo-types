{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoSelectiveProjection: the relational-algebra selection/projection
-- commutativity (the subset case) as an Echo-fibre statement. Closes
-- echo-types#174's sibling echo-types#176 (consumer: affinescript
-- db-theory #4, `stdlib/Select.affine`).
--
-- The classical law (Codd): for selection σ_p (predicate-driven row
-- filter) and projection π_S (column-subset),
--
--     σ_p(π_S(R)) = π_S(σ_p(R))   when p references only columns in S,
--     σ_p(π_S(R)) ≠ π_S(σ_p(R))   when p references a column NOT in S.
--
-- *Honest level.* "=" between relations is SET equality: same rows.
-- The Echo formalisation states it as a per-projected-value LOGICAL
-- equivalence `_⇔_` of the two result fibres (co-membership), which is
-- exactly set-equality of the result relations. A full `_↔_` (with
-- round-trips) would additionally require the predicate family to be
-- proof-irrelevant (`is-prop`); set-equality does not, and `_⇔_` is the
-- faithful level. See the companion remark.
--
-- *The column-safe condition.* "p references only columns in S" is
-- formalised as: p factors through the projection — there is a
-- predicate `q : S → Set` on the projected columns with `p b ⇔ q
-- (projection b)` for every record `b`. This `factors` field IS the
-- "uses only columns in S" hypothesis.
--
-- *The Echo content.* With `pf = projection ∘ f` (the projected map),
-- `Echo pf s` is π_S(R) at projected value `s` — the rows projecting to
-- `s`. The two composites:
--
--   ProjectSelect s  =  Σ (Echo pf s) (λ e → p (f (proj₁ e)))
--       -- π_S(σ_p(R)) at s: rows projecting to s that satisfy p
--   SelectProject s  =  Σ (Echo pf s) (λ _ → q s)
--       -- σ_q(π_S(R)) at s: rows projecting to s, kept iff q holds at s
--
-- `select-project-commute` is `∀ s → ProjectSelect s ⇔ SelectProject s`.
-- The proof is K-free: pattern-matching the fibre witness `pf x ≡ s` as
-- `refl` (s a free variable, so --without-K-safe) collapses the
-- transport, and the predicate move is exactly the `factors` field.
--
-- *The counterexample.* `no-column-safe-lift` shows a predicate that
-- reads a projected-away column (`proj₂`, with projection `= proj₁`)
-- admits NO column-restricted lift `q` at all: the records `(true,true)`
-- and `(true,false)` share projection `true` but disagree on the
-- predicate, so any `q true` would be both inhabited and empty. This is
-- the "≠" direction: σ and π do not commute for such a predicate.
--
-- Headlines (pinned in Smoke.agda):
--   * SelectiveProjection        -- the column-safe setup record
--   * select-project-commute     -- σ–π commute (column-safe), per s
--   * column-safe-example        -- worked column-safe instance
--   * no-column-safe-lift        -- counterexample (non-column-safe ⇒ ✗)

module EchoSelectiveProjection where

open import Echo                  using (Echo)
open import Data.Product.Base    using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Bool.Base       using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary     using (¬_)

----------------------------------------------------------------------
-- Logical equivalence (set-equality level). Kept local and minimal —
-- the σ–π law is co-membership of the two result relations, not a
-- structure-carrying bijection.
----------------------------------------------------------------------

record _⇔_ (P Q : Set) : Set where
  constructor equiv
  field
    to   : P → Q
    from : Q → P

----------------------------------------------------------------------
-- The column-safe selection/projection setup.
----------------------------------------------------------------------

record SelectiveProjection {A B : Set} (f : A → B) (S : Set) : Set₁ where
  field
    projection : B → S          -- π_S
    p          : B → Set        -- σ predicate on full records
    q          : S → Set        -- its restriction to the projected columns
    -- "p uses only columns in S": p factors through projection as q.
    factors    : ∀ b → p b ⇔ q (projection b)

  -- The projected map; `Echo pf s` = π_S(R) at projected value s.
  pf : A → S
  pf a = projection (f a)

  -- π_S(σ_p(R)) at s : rows projecting to s that satisfy p.
  ProjectSelect : S → Set
  ProjectSelect s = Σ (Echo pf s) (λ e → p (f (proj₁ e)))

  -- σ_q(π_S(R)) at s : rows projecting to s, kept iff q holds at s.
  SelectProject : S → Set
  SelectProject s = Σ (Echo pf s) (λ _ → q s)

----------------------------------------------------------------------
-- σ–π commute (column-safe): the two result relations co-inhabit at
-- every projected value. Set-equality of σ_p(π_S(R)) and π_S(σ_p(R)).
----------------------------------------------------------------------

select-project-commute :
  ∀ {A B : Set} {f : A → B} {S : Set} (sp : SelectiveProjection f S) (s : S) →
  SelectiveProjection.ProjectSelect sp s ⇔ SelectiveProjection.SelectProject sp s
select-project-commute {f = f} sp s = equiv to from
  where
    open SelectiveProjection sp
    to : ProjectSelect s → SelectProject s
    to ((x , refl) , pe) = (x , refl) , _⇔_.to (factors (f x)) pe
    from : SelectProject s → ProjectSelect s
    from ((x , refl) , qs) = (x , refl) , _⇔_.from (factors (f x)) qs

----------------------------------------------------------------------
-- Worked column-safe instance: 2-column Bool records, project to
-- column 0, predicate "column 0 is true" — uses only the projected
-- column, so it factors (the identity equivalence).
----------------------------------------------------------------------

column-safe-example : SelectiveProjection {Bool × Bool} {Bool × Bool} (λ b → b) Bool
column-safe-example = record
  { projection = proj₁
  ; p          = λ b → proj₁ b ≡ true
  ; q          = λ s → s ≡ true
  ; factors    = λ b → equiv (λ z → z) (λ z → z)
  }

----------------------------------------------------------------------
-- Counterexample (the "≠" direction): a predicate reading a
-- projected-away column has NO column-restricted lift. `(true,true)`
-- and `(true,false)` share projection `true` but disagree on
-- `proj₂ · ≡ true`, so any candidate `q true` is both inhabited and
-- empty. Hence σ and π do not commute for such a predicate.
----------------------------------------------------------------------

no-column-safe-lift :
  ¬ Σ (Bool → Set) (λ q → ∀ b → (proj₂ b ≡ true) ⇔ q (proj₁ b))
no-column-safe-lift (q , fac)
  with _⇔_.from (fac (true , false)) (_⇔_.to (fac (true , true)) refl)
... | ()

----------------------------------------------------------------------
-- Companion remark.
--
-- `_⇔_` (set-equality of the result relations) is the faithful level:
-- relational-algebra equality is membership equality. Upgrading to a
-- structure-preserving `_↔_` would need the predicate family to be
-- proof-irrelevant (an `is-prop (p b)` field); under `--safe
-- --without-K` that is an extra hypothesis, not free, and it adds no
-- relational-algebra content. NOT claimed: σ–π commutativity for
-- arbitrary (non-column-safe) predicates (refuted by
-- `no-column-safe-lift`); any runtime query-planner behaviour (the
-- decision of whether a predicate is column-safe lives in the
-- consumer). The carrier encodes only the property.
----------------------------------------------------------------------

NotProved-arbitrary-predicate-commute : Set
NotProved-arbitrary-predicate-commute = Bool

NotProved-runtime-query-planner : Set
NotProved-runtime-query-planner = Bool
