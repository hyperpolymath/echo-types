{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- STATUS: DRAFT. Type-checks under Agda 2.6.3 / agda-stdlib 2.3 (`--safe
-- --without-K`, no postulates; checked 2026-10-19). Deliberately NOT imported
-- from All.agda or Smoke.agda: it stays unwired until the maintainer asks.
--
-- Purpose: a small model of an autoformalisation step as a fibre record.
-- Every source atom (hypothesis, constant, bound, conclusion) receives a
-- verdict: mapped to a target atom, or dropped with a recorded reason.
-- The types enforce that nothing is silently lost. They do NOT establish
-- semantic fidelity; see docs/echos/FIDELITY-FIBRE-DESIGN.adoc.

module EchoFidelity where

open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Verdicts for a single source atom.
------------------------------------------------------------------------

data Verdict (TA : Set) : Set where
  mapped  : TA → Verdict TA
  dropped : String → Verdict TA      -- reason must be recorded

------------------------------------------------------------------------
-- A translation step: a total accounting of source atoms.
------------------------------------------------------------------------

record Translation (SA TA : Set) : Set where
  field
    source-atoms : List SA
    target-atoms : List TA
    -- Totality: every source atom gets a verdict. This is the
    -- "nothing silently lost" constraint, enforced by the type.
    account      : SA → Verdict TA

open Translation public

------------------------------------------------------------------------
-- Fibres: the source atoms that a given target atom traces back to.
-- A fibre is a Σ-type of source atoms together with a proof that the
-- source atom is mapped to that target atom.
------------------------------------------------------------------------

Fibre : {SA TA : Set} → Translation SA TA → TA → Set
Fibre T t = Σ _ (λ s → account T s ≡ mapped t)

-- A target atom with an empty fibre has no source: it is fabricated
-- relative to this step. Stated here as the definition of "fabricated";
-- deciding it for an arbitrary translation needs decidable equality.
Fabricated : {SA TA : Set} → Translation SA TA → TA → Set
Fabricated T t = Fibre T t → ⊥

------------------------------------------------------------------------
-- Checker observation vs auditor observation.
-- The proof checker (Lean, Agda, Coq) sees only the target side. The
-- auditor sees the whole translation, including the fibre.
------------------------------------------------------------------------

checker-obs : {SA TA : Set} → Translation SA TA → List TA
checker-obs T = target-atoms T

-- Two translations that agree on the target side are indistinguishable
-- to the checker, whatever their fibres say.
same-target-same-checker-obs :
  {SA TA : Set} (T T' : Translation SA TA) →
  target-atoms T ≡ target-atoms T' →
  checker-obs T ≡ checker-obs T'
same-target-same-checker-obs T T' eq = eq

------------------------------------------------------------------------
-- Direction check for a numeric parameter, using the 4-vs-5 example.
-- Convention: the parameter k means "to control the output, you need
-- k more derivatives on the input". A smaller k is a stronger claim.
------------------------------------------------------------------------

data Direction : Set where
  same stronger weaker : Direction

-- cmp paper target: `stronger` means the target claims more than the
-- paper, `weaker` means it claims less.
cmp : ℕ → ℕ → Direction
cmp zero    zero    = same
cmp zero    (suc _) = weaker
cmp (suc _) zero    = stronger
cmp (suc m) (suc n) = cmp m n

-- The video's case: paper says 4, Lean needs 5. The Lean statement is
-- weaker, so the composed result is not the paper's result.
lemma-8-6-check : cmp 4 5 ≡ weaker
lemma-8-6-check = refl

-- Sanity cases.
cmp-same : cmp 4 4 ≡ same
cmp-same = refl

cmp-stronger : cmp 5 4 ≡ stronger
cmp-stronger = refl
