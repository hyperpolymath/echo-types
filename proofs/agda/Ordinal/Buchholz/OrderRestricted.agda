{-# OPTIONS --safe --without-K #-}

-- The WfCNF-restricted Buchholz order `_<ᵇ⁻_`.
--
-- Path-1 next step (per `buchholz-rank-obstruction.adoc`).  Defines
-- the relation between Buchholz terms that:
--   (a) admits the underlying `_<ᵇ_` derivation, and
--   (b) requires both endpoints to be in Cantor normal form
--       (`Ordinal.Buchholz.WellFormedCNF.WfCNF`).
--
-- Why this matters for the unblock:
--
-- The flagship counterexample to the SA-recommended additive
-- rank-mono is `bplus bzero (bOmega (fin 1)) <ᵇ bOmega (fin 0)`
-- via `<ᵇ-+Ω <ᵇ-0-Ω`.  Under `_<ᵇ⁻_` this witness is excluded *by
-- type*: `bplus bzero (bOmega (fin 1))` is not WfCNF (the right
-- summand outsizes the left), so the source-WfCNF field of the
-- record cannot be constructed.
--
-- This module ships:
--   * The relation `_<ᵇ⁻_` as a record bundling source-WfCNF,
--     target-WfCNF, and the underlying `<ᵇ` derivation.
--   * Subrelation projection `<ᵇ⁻-to-<ᵇ : _<ᵇ⁻_ ⇒ _<ᵇ_`.
--   * Well-foundedness `wf-<ᵇ⁻` via `Subrelation.wellFounded`
--     from the existing `wf-<ᵇ`.
--   * Irreflexivity and transitivity (the latter preserves WfCNF on
--     the endpoints, dropping the middle's well-formedness witness).
--
-- The full unblock — `rank-mono-<ᵇ⁻ : x <ᵇ⁻ y → rank x <′ rank y`
-- for all 13 constructors — needs additional structural lemmas
-- (extracting the CNF tail bound, ψ-admissibility) and is the next
-- multi-session step.  This module is the relation foundation that
-- those lemmas will operate over.
--
-- ## Headlines (pinned in `Ordinal/Buchholz/Smoke.agda`)
--
--   * _<ᵇ⁻_                -- the restricted relation
--   * cnf-strict           -- the record constructor
--   * <ᵇ⁻-to-<ᵇ           -- the subrelation projection
--   * wf-<ᵇ⁻               -- well-foundedness via Subrelation
--   * <ᵇ⁻-irrefl           -- inherited irreflexivity
--   * <ᵇ⁻-trans            -- transitivity with WfCNF endpoints

module Ordinal.Buchholz.OrderRestricted where

open import Function.Base                         using (_on_)
open import Induction.WellFounded                 using
  ( Acc
  ; acc
  ; WellFounded
  ; wf⇒asym
  ; module Subrelation
  )
open import Relation.Binary.Core                  using (Rel; _⇒_)
open import Relation.Nullary                      using (¬_)

open import Ordinal.Buchholz.Syntax               using (BT)
open import Ordinal.Buchholz.Order                using (_<ᵇ_; <ᵇ-irrefl; <ᵇ-trans)
open import Ordinal.Buchholz.WellFounded          using (wf-<ᵇ)
open import Ordinal.Buchholz.WellFormedCNF        using (WfCNF)

----------------------------------------------------------------------
-- The WfCNF-restricted relation
----------------------------------------------------------------------

-- A `_<ᵇ⁻_` derivation bundles an underlying `_<ᵇ_` step with
-- well-formedness witnesses on both endpoints.  The record shape
-- (rather than an indexed `data`) keeps the relation a subrelation
-- of `_<ᵇ_` and lets downstream rank-mono proofs pattern-match on
-- the underlying derivation while pulling WfCNF as needed.

record _<ᵇ⁻_ (x y : BT) : Set where
  constructor cnf-strict
  field
    wfcnf-source : WfCNF x
    wfcnf-target : WfCNF y
    underlying   : x <ᵇ y

open _<ᵇ⁻_ public

infix 4 _<ᵇ⁻_

----------------------------------------------------------------------
-- Subrelation projection
----------------------------------------------------------------------

-- The `_<ᵇ⁻_` relation embeds into `_<ᵇ_` by forgetting the WfCNF
-- witnesses.  Used both for the WF lift and to expose the
-- underlying derivation for case analysis in downstream rank-mono
-- proofs.

<ᵇ⁻-to-<ᵇ : _<ᵇ⁻_ ⇒ _<ᵇ_
<ᵇ⁻-to-<ᵇ p = underlying p

----------------------------------------------------------------------
-- Well-foundedness via Subrelation transport
----------------------------------------------------------------------

-- Since `_<ᵇ⁻_ ⊆ _<ᵇ_` and `_<ᵇ_` is well-founded
-- (`Ordinal.Buchholz.WellFounded.wf-<ᵇ`), the subrelation is also
-- well-founded.  This is essentially free; the interesting work is
-- the rank-mono proof (next session).

wf-<ᵇ⁻ : WellFounded _<ᵇ⁻_
wf-<ᵇ⁻ =
  let module SR = Subrelation <ᵇ⁻-to-<ᵇ
  in SR.wellFounded wf-<ᵇ

----------------------------------------------------------------------
-- Irreflexivity (inherited via projection)
----------------------------------------------------------------------

-- `wf⇒asym` gives irreflexivity from well-foundedness, but we can
-- equivalently route through the underlying `<ᵇ-irrefl`.  The two
-- proofs agree definitionally; we pick the projection route for
-- clarity at the call site.

<ᵇ⁻-irrefl : ∀ {x} → ¬ (x <ᵇ⁻ x)
<ᵇ⁻-irrefl p = <ᵇ-irrefl (<ᵇ⁻-to-<ᵇ p)

----------------------------------------------------------------------
-- Transitivity (preserves WfCNF on endpoints, drops middle)
----------------------------------------------------------------------

-- Compose two `<ᵇ⁻` derivations.  The intermediate point's WfCNF
-- witness is consumed by `<ᵇ-trans` and discarded; the resulting
-- derivation carries the source-WfCNF of the first leg and the
-- target-WfCNF of the second.  This is the natural composition
-- shape for a subrelation indexed by endpoint well-formedness.

<ᵇ⁻-trans : ∀ {x y z} → x <ᵇ⁻ y → y <ᵇ⁻ z → x <ᵇ⁻ z
<ᵇ⁻-trans p q =
  cnf-strict (wfcnf-source p) (wfcnf-target q)
    (<ᵇ-trans (<ᵇ⁻-to-<ᵇ p) (<ᵇ⁻-to-<ᵇ q))
