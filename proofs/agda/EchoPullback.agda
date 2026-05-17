{-# OPTIONS --safe --without-K #-}

-- Pillar B (part 1) of docs/echo-types/establishment-plan.adoc.
--
-- SCAFFOLD ONLY. Documentation module: no declarations, hence no
-- postulates and no holes — it typechecks under `--safe --without-K`
-- and is tracked in `All.agda` per the rung-consolidation policy.
-- The intended theorems are recorded here as commented specifications
-- so a fresh session can start without re-deriving the design.
--
-- Goal: present `Echo f y` as the pullback of `f : A → B` along the
-- point `y : ⊤ → B`, and prove its terminal-cone universal property.
-- This is the categorical-semantics anchor: it lets a category
-- theorist accept echo as a *real object* rather than a notation.
--
-- Intended signatures (to be filled, in dependency order):
--
--   -- The pullback square: cone over (f , const y).
--   record EchoCone {A B : Set} (f : A → B) (y : B) (V : Set) ...
--
--   -- Echo is a cone.
--   echo-cone : (f : A → B) (y : B) → EchoCone f y (Echo f y)
--
--   -- Universal property: any cone factors uniquely through Echo.
--   echo-pullback-univ :
--     (f : A → B) (y : B) (V : Set) (c : EchoCone f y V) →
--     ∃! (λ (m : V → Echo f y) → <cone c factors through echo-cone via m>)
--
-- Reuse: `Echo.echo-intro`, `Echo.map-over`, and the existing
-- `EchoCategorical.SliceHom` packaging (a SliceHom is already a cone
-- morphism in disguise — start by relating the two).

module EchoPullback where
