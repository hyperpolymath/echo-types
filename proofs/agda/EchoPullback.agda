{-# OPTIONS --safe --without-K #-}

-- Pillar B (part 1) of docs/echo-types/establishment-plan.adoc.
--
-- REAL MODULE (H1 landed 2026-05-17).
--
-- Goal: present `Echo f y` as the pullback of `f : A → B` along the
-- point `y : ⊤ → B`, and prove its terminal-cone universal property.
-- This is the categorical-semantics anchor: it lets a category
-- theorist accept echo as a *real object* (the limit of a cospan)
-- rather than a notation.
--
-- The cospan / pullback square:
--
--        Echo f y ----proj₁----> A
--           |                    |
--      (! to ⊤)                  f
--           |                    |
--           v                    v
--           ⊤ -------const y---> B
--
-- The ⊤-leg `V → ⊤` is forced (it is constantly `tt`), so a cone over
-- the cospan with apex `V` is *exactly* a map `p₁ : V → A` together
-- with the square condition `∀ v → f (p₁ v) ≡ y`. That is precisely an
-- `EchoCategorical.SliceHom (λ (_ : V) → y) f` — a SliceHom IS a cone,
-- not merely "in disguise"; the bridge lemmas below make that a
-- checked fact (round-trips are `refl` by record η).
--
-- Universal property (terminal cone), stated `--safe --without-K`:
-- for every cone `c` there is a mediator `m` factoring both legs, and
-- it is unique *pointwise* among cone morphisms. Uniqueness is stated
-- pointwise (`∀ v → m' v ≡ m v`), NOT as `m' ≡ m`, so the statement is
-- funext-free — respecting the establishment-plan funext guardrail.
-- The second Σ-component is a witness, so the cone-morphism notion
-- carries the transport-coherence leg `coherent`; this is what makes
-- uniqueness provable without K (no UIP on `f a ≡ y` is assumed).

module EchoPullback where

open import Echo using (Echo)
open import EchoCategorical using (SliceHom; arrow; commute)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

----------------------------------------------------------------------
-- Cones over the cospan  A --f--> B <--const y-- ⊤.
--
-- The ⊤-leg is forced, so the cone data is just the A-leg plus the
-- square. Kept at `Set` (level 0): the categorical anchor is cleaner
-- for a referee without universe noise, and `SliceHom` instantiates
-- fine at Set₀.

record EchoCone {A B : Set} (f : A → B) (y : B) (V : Set) : Set where
  field
    apex-map : V → A
    square   : ∀ v → f (apex-map v) ≡ y

open EchoCone public

-- Echo itself is the canonical cone: proj₁ is the A-leg, proj₂ is the
-- square. (This is the cone that the universal property is terminal
-- among.)
echo-cone : {A B : Set} (f : A → B) (y : B) → EchoCone f y (Echo f y)
echo-cone f y = record { apex-map = proj₁ ; square = proj₂ }

----------------------------------------------------------------------
-- A SliceHom IS a cone (the establishment-plan "in disguise" claim,
-- now a checked fact). A cone with apex V is exactly a slice morphism
-- from the constant map `λ (_ : V) → y` to `f`.

cone→slice :
  {A B : Set} {f : A → B} {y : B} {V : Set} →
  EchoCone f y V → SliceHom (λ (_ : V) → y) f
cone→slice c = record { arrow = apex-map c ; commute = square c }

slice→cone :
  {A B : Set} {f : A → B} {y : B} {V : Set} →
  SliceHom (λ (_ : V) → y) f → EchoCone f y V
slice→cone h = record { apex-map = arrow h ; square = commute h }

cone→slice→cone :
  {A B : Set} {f : A → B} {y : B} {V : Set} (c : EchoCone f y V) →
  slice→cone (cone→slice c) ≡ c
cone→slice→cone c = refl

slice→cone→slice :
  {A B : Set} {f : A → B} {y : B} {V : Set}
  (h : SliceHom (λ (_ : V) → y) f) →
  cone→slice (slice→cone h) ≡ h
slice→cone→slice h = refl

----------------------------------------------------------------------
-- Cone morphisms into the canonical Echo cone.
--
-- A morphism from cone `c` (apex V) to `echo-cone` is a map
-- `m : V → Echo f y` that factors the A-leg (`factor`) and whose
-- witness, transported along that factoring, recovers the cone's own
-- square (`coherent`). The `coherent` leg is exactly the Σ-second
-- coherence that lets uniqueness go through without K.

record IsMediator
  {A B : Set} (f : A → B) (y : B) {V : Set}
  (c : EchoCone f y V) (m : V → Echo f y) : Set where
  field
    factor   : ∀ v → proj₁ (m v) ≡ apex-map c v
    coherent : ∀ v →
      subst (λ a → f a ≡ y) (factor v) (proj₂ (m v)) ≡ square c v

open IsMediator public

----------------------------------------------------------------------
-- The universal property: `echo-cone` is the terminal cone.
--
-- For every cone `c` there is a mediator `m` (factoring both legs),
-- and any cone morphism `m'` agrees with `m` pointwise. Existence is
-- the obvious pairing; uniqueness is one application of stdlib's
-- `Σ-≡,≡→≡`, fed exactly the `factor`/`coherent` legs — no K, no
-- funext.

echo-pullback-univ :
  {A B : Set} (f : A → B) (y : B) {V : Set} (c : EchoCone f y V) →
  Σ (V → Echo f y) (λ m →
    IsMediator f y c m
    × (∀ (m' : V → Echo f y) → IsMediator f y c m' →
         ∀ v → m' v ≡ m v))
echo-pullback-univ f y c =
  m
  , record { factor = λ _ → refl ; coherent = λ _ → refl }
  , λ m' med v → Σ-≡,≡→≡ (factor med v , coherent med v)
  where
    m : _ → Echo f y
    m v = apex-map c v , square c v
