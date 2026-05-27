{-# OPTIONS --safe --without-K #-}

-- EchoObservationalEquivalence: mode-indexed observational equality
-- on `LEcho`. Closes Tier 2 #5 (final Tier-2 module in the
-- synthesis-roadmap reorder), making the distinction
-- "linear-equality vs affine-equality" crisp.
--
-- `LEcho` has two modes:
--
--   * `LEcho linear  = Echo collapse tt` (full witness retained)
--   * `LEcho affine  = EchoR ⊤ TrivialCert tt` (witness discarded;
--                                                only the trivial
--                                                residue (tt, tt))
--
-- At the `linear` mode, the only sensible equality is propositional
-- `_≡_` on the full echo — two echoes are linear-equal iff their
-- underlying domain elements agree (modulo path equality on the
-- collapse witness). At `affine`, all inhabitants of
-- `EchoR ⊤ TrivialCert tt` are `(tt, tt)`, so the only meaningful
-- equality is `⊤` (every pair of affine echoes is observationally
-- equal — there is nothing left to distinguish them).
--
-- The mode-indexed equality `_≡m_` is therefore:
--
--   _≡m_ {linear} e₁ e₂ = e₁ ≡ e₂   (propositional equality)
--   _≡m_ {affine} _  _  = ⊤         (always equal)
--
-- The headline theorem `mode-equality-strictly-finer-at-linear`
-- exhibits two echoes that are linear-DISTINCT (`echo-true`,
-- `echo-false`) but affine-EQUAL (after `weaken`, they both become
-- the trivial residue `(tt, tt)`). This is the precise content of
-- "affine forgets what linear retains" at the equality level.
--
-- Closes Tier 2 #5 per the synthesis-roadmap reorder. Together
-- with the previous Tier 2 modules (LossTaxonomy, ResidueTaxonomy,
-- DecorationStructure), the Tier 2 spine is complete: the
-- function-side / residue-side / decoration-structure / observation
-- axes are all named theorems.
--
-- Headlines (pinned in Smoke.agda):
--
--   * _≡m_                                  -- mode-indexed equality
--   * ≡m-refl                               -- reflexivity
--   * ≡m-sym                                -- symmetry
--   * linear-distinguishes-true-false       -- linear is witness-aware
--   * affine-collapses                      -- affine is witness-blind
--   * weaken-preserves-≡m                   -- weakening respects equality
--   * mode-equality-strictly-finer-at-linear
--                                           -- headline strictness witness
--
-- Scope guardrail. `_≡m_` is defined by case-split on the mode.
-- At `linear`, it is `_≡_` (the full propositional equality); at
-- `affine`, it is `⊤` (full collapse). This captures the
-- observational content of "the mode dictates what counts as
-- observable equality" without postulating funext, UIP, or any
-- HoTT-strength reasoning. The deeper claim "≡m IS the only
-- compositional equality consistent with weaken-functoriality" is
-- a separate universal-property argument and not made here.

module EchoObservationalEquivalence where

open import Echo                using (Echo)
open import EchoCharacteristic  using
  ( collapse
  ; echo-true
  ; echo-false
  ; echo-true≢echo-false
  )
open import EchoLinear          using (Mode; linear; affine; LEcho; weaken)
open import EchoResidue         using (EchoR; TrivialCert)

open import Data.Product.Base   using (Σ; _,_; _×_)
open import Data.Unit.Base      using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                using (_≡_; refl; sym)
open import Relation.Nullary    using (¬_)

----------------------------------------------------------------------
-- The mode-indexed observational equality on LEcho.
--
-- Definitional case-split on the mode. At linear it is full
-- propositional equality on the underlying echo; at affine it
-- collapses to ⊤ (all pairs equal).
----------------------------------------------------------------------

_≡m_ : ∀ {m} → LEcho m → LEcho m → Set
_≡m_ {linear} e₁ e₂ = e₁ ≡ e₂
_≡m_ {affine} _  _  = ⊤

----------------------------------------------------------------------
-- Reflexivity and symmetry.
--
-- Per-mode case-split. At linear, ≡m-refl reduces to refl; at
-- affine, ≡m-refl reduces to tt. Same for symmetry.
----------------------------------------------------------------------

≡m-refl : ∀ {m} {e : LEcho m} → _≡m_ {m} e e
≡m-refl {linear} = refl
≡m-refl {affine} = tt

≡m-sym : ∀ {m} {e₁ e₂ : LEcho m} → _≡m_ {m} e₁ e₂ → _≡m_ {m} e₂ e₁
≡m-sym {linear} = sym
≡m-sym {affine} _ = tt

----------------------------------------------------------------------
-- Mode-specific characterisations.
--
-- At linear: echo-true and echo-false are observationally distinct
-- (the existing `echo-true≢echo-false` IS the witness).
--
-- At affine: every pair is observationally equal (definitional,
-- because `_≡m_` is constant `⊤` at affine).
----------------------------------------------------------------------

linear-distinguishes-true-false :
  ¬ (_≡m_ {linear} echo-true echo-false)
linear-distinguishes-true-false = echo-true≢echo-false

affine-collapses : (e₁ e₂ : LEcho affine) → _≡m_ {affine} e₁ e₂
affine-collapses _ _ = tt

----------------------------------------------------------------------
-- Weakening respects observational equality.
--
-- If `e₁ ≡m e₂` at linear, then `weaken e₁ ≡m weaken e₂` at
-- affine. Trivial because `_≡m_` at affine is constant `⊤`; this
-- pins the naturality direction (weaken is monotone under ≡m).
----------------------------------------------------------------------

weaken-preserves-≡m :
  (e₁ e₂ : LEcho linear) →
  _≡m_ {linear} e₁ e₂ →
  _≡m_ {affine} (weaken e₁) (weaken e₂)
weaken-preserves-≡m _ _ _ = tt

----------------------------------------------------------------------
-- Headline: linear-equality is strictly finer than affine-equality.
--
-- The Σ-witness packaging: a specific linear-distinct pair
-- (`echo-true`, `echo-false`) whose `weaken`s are affine-equal.
-- "Strictly finer" = there is a pair distinguished at linear but
-- collapsed at affine.
----------------------------------------------------------------------

mode-equality-strictly-finer-at-linear :
  Σ (LEcho linear) (λ e₁ →
  Σ (LEcho linear) (λ e₂ →
    (¬ _≡m_ {linear} e₁ e₂) ×
    _≡m_ {affine} (weaken e₁) (weaken e₂)))
mode-equality-strictly-finer-at-linear =
  echo-true , echo-false , echo-true≢echo-false , tt

----------------------------------------------------------------------
-- Companion remark.
--
-- The mode-indexed equality `_≡m_` captures the standard intuition
-- "the mode controls what counts as observable". The two modes
-- here are the linear/affine pair from `EchoLinear`; the same
-- pattern generalises to every decoration module's grade poset:
--
--   * EchoGraded — `≡g {keep} = ≡` on full echo;
--                  `≡g {residue} = ≡` on trivial residue;
--                  `≡g {forget} = ⊤`.
--   * EchoAccess — `≡a {free} = ≡`; `≡a {decidable} = ≡` on dec;
--                  `≡a {enum} = ⊤`; ...; `≡a {infeasible} = ⊤`.
--   * Similar for the other six decoration modules.
--
-- The general theorem "mode-indexed equality is the coarsest
-- equality refined by all weakening maps" is a universal-property
-- claim over the abstract `DecorationStructure`; it is NOT proved
-- here. The honest scope is: the linear/affine case is the
-- minimum-viable witness that the mode-indexed equality pattern
-- exists and pins the strictly-finer-at-linear witness as a
-- checked theorem. Generalising to the other decoration modules
-- is a per-module mechanical lift; generalising to the abstract
-- DecorationStructure is a deferred universal-property argument.
----------------------------------------------------------------------
