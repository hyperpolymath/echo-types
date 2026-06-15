{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- EchoDeniability: residue deniability as a first-class echo property.
--
-- A residue-production function f : History → Residue is *perfectly
-- deniable* when its image is a single point — no opener d can
-- distinguish histories via their residues, because all residues are
-- the same. This is the case where f is constant, mirroring
-- `EchoCharacteristic.collapse : Bool → ⊤`.
--
-- When f is injective (each history maps to a distinct residue),
-- deniability fails for arbitrary openers but is restored for the
-- restricted class of *constant openers* — those that ignore the
-- residue entirely.  This is the partial-deniability case from the
-- companion exploration (DeniabilityPartial.agda).
--
-- This module formalises both cases in the echo-types framework and
-- makes the structural connections explicit:
--
--   * The perfect case is the `no-section-of-collapsing-map` story:
--     the production map collapses, so no recovery is possible.
--
--   * The partial case is its dual: the production map is injective,
--     a section exists (`partial-witness`), so recovery IS possible
--     for arbitrary openers — deniability only survives for those who
--     decline to look.
--
--   * `IsConstantOpener` — the class of openers that ignore the
--     residue — is the type-level analogue of the `affine` mode in
--     `EchoObservationalEquivalence._≡m_`: at affine, there is
--     nothing left in the residue to observe, so all openers agree.
--
-- Honest scope:
--
--   * All guarantees are type-level: what pure Agda functions d can
--     and cannot do under --safe --without-K, zero postulates.
--   * No claim is made about side-channels, timing, oracle access,
--     or adversaries with state outside the model.
--   * `partial-deniable-restricted` is the minimum-viable type-level
--     boundary.  Cryptographic deniability requires additional
--     structure beyond the structural no-section property.
--
-- Headlines (pinned in Smoke.agda):
--
--   * History                       -- the two-history type
--   * Residue                       -- the two-residue type (Trace / Erased)
--   * produce-perfect               -- constant production: all → Trace
--   * produce-partial               -- injective production: Intact→Trace, Lost→Erased
--   * IsDeniable                    -- ∀ d, d ∘ f equal on Intact / Lost
--   * IsConstantOpener              -- the restricted-opener class (d Trace ≡ d Erased)
--   * perfect-deniable              -- IsDeniable produce-perfect
--   * partial-witness               -- the distinguishing opener for produce-partial
--   * partial-distinguishable       -- partial-witness separates the two histories
--   * partial-not-deniable          -- ¬ IsDeniable produce-partial
--   * partial-deniable-restricted   -- restricted deniability for produce-partial
--   * no-section-produce-perfect    -- no section for the collapsing map
--   * partial-has-section           -- section exists for the injective map

module EchoDeniability where

open import Echo              using (Echo; echo-intro)
open import EchoNoSectionGeneric using (no-section-of-collapsing-map)

open import Data.Product.Base using (Σ; _,_)
open import Data.Unit.Base    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary  using (¬_)

------------------------------------------------------------------------
-- The two histories and the two residues.
------------------------------------------------------------------------

data History : Set where
  Intact : History
  Lost   : History

-- Two-constructor residue: Trace is a retained mark; Erased is an
-- absent one.  With one constructor the collapse is trivial (refl);
-- with two we can witness failure and recovery.
data Residue : Set where
  Trace  : Residue
  Erased : Residue

------------------------------------------------------------------------
-- The two production functions.
--
-- produce-perfect: constant — both histories leave the same residue.
-- Mirrors `EchoCharacteristic.collapse : Bool → ⊤`.
--
-- produce-partial: injective — each history leaves a distinct residue.
-- Mirrors a Bool-tagged split where the two tags are distinguishable.
------------------------------------------------------------------------

produce-perfect : History → Residue
produce-perfect _ = Trace

produce-partial : History → Residue
produce-partial Intact = Trace
produce-partial Lost   = Erased

------------------------------------------------------------------------
-- Deniability predicate.
--
-- f is deniable when no opener can distinguish which history produced
-- the residue: d(f Intact) ≡ d(f Lost) for every opener d.
------------------------------------------------------------------------

IsDeniable : (History → Residue) → Set
IsDeniable f = (d : Residue → History) → d (f Intact) ≡ d (f Lost)

------------------------------------------------------------------------
-- Perfect deniability: produce-perfect is fully deniable.
--
-- Both histories produce Trace, so d(Trace) ≡ d(Trace) for any d.
-- The proof is refl: definitional equality after computation.
------------------------------------------------------------------------

perfect-deniable : IsDeniable produce-perfect
perfect-deniable d = refl

------------------------------------------------------------------------
-- Distinct residues: Intact ≢ Lost (standard constructor discrimination).
------------------------------------------------------------------------

Intact≢Lost : Intact ≢ Lost
Intact≢Lost ()

------------------------------------------------------------------------
-- Partial case: counterexample opener.
--
-- partial-witness reads off the history directly from the residue.
-- It is a left-inverse of produce-partial: section identity holds
-- by definitional reduction on each constructor.
------------------------------------------------------------------------

partial-witness : Residue → History
partial-witness Trace  = Intact
partial-witness Erased = Lost

partial-distinguishable :
  ¬ (partial-witness (produce-partial Intact) ≡
     partial-witness (produce-partial Lost))
partial-distinguishable ()
-- Reduces to ¬ (Intact ≡ Lost); the empty pattern refutes it.

------------------------------------------------------------------------
-- produce-partial is not deniable.
--
-- The witness partial-witness distinguishes the two histories, so
-- deniability fails for unrestricted openers.
------------------------------------------------------------------------

partial-not-deniable : ¬ IsDeniable produce-partial
partial-not-deniable den = partial-distinguishable (den partial-witness)

------------------------------------------------------------------------
-- Restricted class: constant openers ignore the residue.
--
-- An opener is constant when it returns the same verdict on every
-- residue.  This is the type-level analogue of the `affine` mode in
-- `EchoObservationalEquivalence._≡m_`: at affine, there is nothing
-- left in the residue to distinguish — all affine observers agree.
------------------------------------------------------------------------

IsConstantOpener : (Residue → History) → Set
IsConstantOpener d = d Trace ≡ d Erased

------------------------------------------------------------------------
-- Restricted deniability for produce-partial.
--
-- For any constant opener, the two histories remain indistinguishable
-- even under injective production: d cannot exploit the residue
-- difference if it never looks.  Goal reduces by computation to
-- d Trace ≡ d Erased, which is exactly `const`.
------------------------------------------------------------------------

partial-deniable-restricted :
  (d : Residue → History) →
  IsConstantOpener d →
  d (produce-partial Intact) ≡ d (produce-partial Lost)
partial-deniable-restricted d const = const

------------------------------------------------------------------------
-- No section for produce-perfect.
--
-- Since produce-perfect collapses Intact and Lost onto the same
-- residue (Trace ≡ Trace), `no-section-of-collapsing-map` applies
-- directly: no pure function can recover the history from the residue.
-- This is the structural dual of perfect deniability — the collapse
-- that makes deniability free also makes recovery impossible.
------------------------------------------------------------------------

no-section-produce-perfect :
  ¬ Σ (Residue → History) (λ s → ∀ h → s (produce-perfect h) ≡ h)
no-section-produce-perfect =
  no-section-of-collapsing-map produce-perfect Intact Lost Intact≢Lost refl

------------------------------------------------------------------------
-- Section exists for produce-partial.
--
-- Since produce-partial is injective, partial-witness is a genuine
-- left-inverse.  This is the dual: injective production gives recovery.
-- Together with `partial-not-deniable`, it shows that the existence of
-- a section and the failure of deniability are the same phenomenon.
------------------------------------------------------------------------

partial-witness-is-section : ∀ h → partial-witness (produce-partial h) ≡ h
partial-witness-is-section Intact = refl
partial-witness-is-section Lost   = refl

partial-has-section :
  Σ (Residue → History) (λ s → ∀ h → s (produce-partial h) ≡ h)
partial-has-section = partial-witness , partial-witness-is-section

------------------------------------------------------------------------
-- Echo witnesses: distinct echoes at the same residue (perfect case).
--
-- When produce-perfect collapses both histories to Trace, both Intact
-- and Lost are valid witnesses for Echo produce-perfect Trace.  They
-- are DISTINCT witnesses (Intact ≢ Lost), yet they share the same
-- residue.  This is structurally identical to the
-- `EchoCharacteristic.echo-true / echo-false` pair at
-- `Echo collapse tt`.
------------------------------------------------------------------------

echo-intact-perfect : Echo produce-perfect Trace
echo-intact-perfect = echo-intro produce-perfect Intact
-- echo-intro f x = (x, refl); result type is Echo f (f x) = Echo produce-perfect Trace.

echo-lost-perfect : Echo produce-perfect Trace
echo-lost-perfect = echo-intro produce-perfect Lost
-- produce-perfect Lost = Trace, so the result type is Echo produce-perfect Trace. ✓

echo-intact-lost-distinct : echo-intact-perfect ≢ echo-lost-perfect
echo-intact-lost-distinct ()
-- The first Σ-components are Intact and Lost; distinct constructors make
-- the equality absurd and the empty pattern closes it.

------------------------------------------------------------------------
-- Companion remark.
--
-- The two production functions sit at opposite ends of the deniability
-- spectrum.  The structural relationship:
--
--                 perfect (constant)    partial (injective)
--   deniable?     YES (all d)           NO (partial-witness)
--   has section?  NO (no-section-…)    YES (partial-witness-is-section)
--   echo count    2 at Trace            1 at Trace, 1 at Erased
--
-- The `IsConstantOpener` class is the exact cut-point at which
-- deniability is restored for the partial case.  In echo-types terms
-- it corresponds to the `affine` mode of
-- `EchoObservationalEquivalence._≡m_`: at affine, the residue
-- collapses to ⊤, removing all distinguishable content — constant
-- openers do the same by construction.
--
-- The `no-section / has-section` duality is load-bearing: it explains
-- WHY perfect deniability is free (the map collapses, so no recovery
-- is possible) and why partial deniability costs something (the map is
-- injective, so non-constant openers can recover, and only constant
-- openers are barred from doing so).
--
-- Honest-bound matched-negative block (grep NotProved catches these):
------------------------------------------------------------------------

NotProved-side-channel-safe : Set
NotProved-side-channel-safe = ⊤

NotProved-cryptographic-deniability : Set
NotProved-cryptographic-deniability = ⊤

NotProved-adaptive-adversary : Set
NotProved-adaptive-adversary = ⊤
