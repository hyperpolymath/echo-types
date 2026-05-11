{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Gate #3 canonical example: linear-mode erasure with retained
-- type structure.
--
-- A linearly-typed source language has function types annotated
-- with modes (linear, unrestricted).  Compilation to an unannotated
-- target erases the mode while preserving the structural shape:
-- functions remain functions, base types remain base types.  The
-- Echo of erasure at a plain type is the type of source annotations
-- consistent with that plain type --- structured loss where the
-- LINEARITY annotation is exactly what is lost and the function /
-- base structure is exactly the residue that survives.
--
-- This file is a tractable miniature of type-preserving compilation:
-- given an erased function type, what mode could the source have
-- had?  Echo answers as a type, not as a propositional "some mode
-- existed".
--
-- Bridge axis: linear.  The README lists "affine/linear bridge ---
-- strict weakening from full echoes to residues".  This file's
-- (lin, unr) distinction is the smallest non-trivial instance:
-- the linear annotation is the lost data, the type structure is
-- the residue.
--
-- Canonicality (against the Gate #3 (a)/(b)/(c) bar):
--
--   (a) Forced.  In type-preserving compilation of linearly-typed
--       languages (Linear Haskell, QTT-style Idris, CompCert-style
--       mechanised compilation), the inverse problem is natively a
--       Σ-type.  Echo is the direct type-theoretic encoding ---
--       it falls out of the typing relation, not retrofitted onto
--       a domain that already had a clean account.
--
--   (b) Linear bridge axis genuinely active.  The example
--       structurally exhibits the loss type the axis names: the
--       mode annotation is the unique data discarded by erasure,
--       the type-shape is what survives.
--
--   (c) `echo-not-prop` certifies the witness type is not a mere
--       proposition.  `retained-shape` certifies the residue
--       structure is preserved.  Any propositional account
--       collapses what these record.
--
-- Falsifier 1 (example-internal).  If `erase` were injective on
-- Type, every Echo at every value is at most a singleton; no
-- genuine erasure of linearity.  Refuted by `linearF`,
-- `unrestrictedF`, and `distinct`.
--
-- Falsifier 2 (load-bearing for canonicality).  If
-- `Echo erase erasedF` is provably contractible, the
-- linearity-vs-non-linearity distinction is not type-data here.
-- Refuted by `echo-not-prop`.
--
-- Falsifier 3 (residue structure).  If `Echo erase` did not
-- preserve function-shape (e.g., if a base type could be the
-- source for a function-shaped target), the residue claim
-- collapses.  Refuted by `retained-shape`.
--
-- Falsifier 4 (canonicality, vs modal type theories).  This stops
-- being canonical if explicit modal type theories (Reed-Pfenning,
-- adjoint modalities, full QTT) reproduce the type-data of Echo
-- natively.  Honest comparison: in those systems mode annotations
-- are first-class and the Σ-type formulation of erasure-inverse
-- coincides with Echo.  Negative result preserved: this example
-- is canonical *over* propositional / classical accounts of mode
-- erasure; it is *coextensive with* native modal Σ-type accounts.
------------------------------------------------------------------------

module examples.LinearErasure where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Self-contained Echo definition.

Echo : ∀ {A B : Set} → (A → B) → B → Set
Echo {A} f y = Σ A (λ x → f x ≡ y)

------------------------------------------------------------------------
-- Modes: linear (use exactly once) and unrestricted.

data Mode : Set where
  lin unr : Mode

------------------------------------------------------------------------
-- Modally-annotated source types and plain target types.

data Type : Set where
  base : Type
  fn   : Mode → Type → Type → Type   -- (mode, domain, codomain)

data Plain : Set where
  base : Plain
  fn   : Plain → Plain → Plain

------------------------------------------------------------------------
-- Erasure: forget the mode, retain the structure.

erase : Type → Plain
erase base       = base
erase (fn _ A B) = fn (erase A) (erase B)

------------------------------------------------------------------------
-- Two distinct mode-annotated types erasing to the same plain
-- function type.  Refutes Falsifier 1: erase is non-injective at
-- the result `fn base base`.

linearF : Type
linearF = fn lin base base

unrestrictedF : Type
unrestrictedF = fn unr base base

erasedF : Plain
erasedF = fn base base

witness₁ : Echo erase erasedF
witness₁ = linearF , refl

witness₂ : Echo erase erasedF
witness₂ = unrestrictedF , refl

------------------------------------------------------------------------
-- Distinguishability via mode extraction.

extract-mode : Type → Mode
extract-mode (fn m _ _) = m
extract-mode base       = lin   -- arbitrary; not exercised by witnesses

lin≢unr : lin ≡ unr → ⊥
lin≢unr ()

distinct : proj₁ witness₁ ≡ proj₁ witness₂ → ⊥
distinct p = lin≢unr (cong extract-mode p)

------------------------------------------------------------------------
-- Retained-structure theorem.  The function-shape of the source
-- type is preserved through Echo: any source consistent with an
-- erased function type IS itself a function type at the source
-- level.  This is the "residue" the linear axis names: what
-- survives strict weakening of the linearity annotation.
--
-- Note (cross-cut to the handoff): this proof is NOT just `proj₂`
-- of the Σ.  The handoff observed that retained-constraint
-- theorems in the earlier dropped examples reduced to `proj₂` and
-- so were not echo-specific.  `retained-shape` here is a genuine
-- inversion lemma on the source structure, derived by pattern
-- matching on the source type --- not extractable from the
-- equality witness alone.

data is-fn-type : Type → Set where
  fn-shape : ∀ {m A B} → is-fn-type (fn m A B)

retained-shape :
  ∀ {P Q} (e : Echo erase (fn P Q)) → is-fn-type (proj₁ e)
retained-shape (base     , ())
retained-shape (fn m A B , _) = fn-shape

------------------------------------------------------------------------
-- The load-bearing canonicality result.
--
-- `Echo erase erasedF` is not a mere proposition: it carries
-- strictly more information than "some annotated type erases here".
-- The linearity annotation is genuine type-data, not subset-data.

is-prop : Set → Set
is-prop A = ∀ (x y : A) → x ≡ y

echo-not-prop : is-prop (Echo erase erasedF) → ⊥
echo-not-prop h = distinct (cong proj₁ (h witness₁ witness₂))
