{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
--
-- STATUS: type-checks under Agda 2.6.3 / agda-stdlib 2.3 (`--safe
-- --without-K`, no postulates). Deliberately NOT imported from All.agda or
-- Smoke.agda: it stays unwired until the maintainer asks for that.
--
-- Purpose: a small model of an autoformalisation step as a fibre record.
-- Every source atom (hypothesis, constant, bound, conclusion) receives a
-- verdict: mapped to a target atom, or dropped with a recorded reason.
-- The types enforce that nothing is silently lost. They do NOT establish
-- semantic fidelity; see docs/echos/FIDELITY-FIBRE-DESIGN.adoc.
--
-- The fibre of a target atom IS an `Echo` of the accounting map: `Fibre`
-- below is `Echo (account T) (mapped t)` by definition, so the structure
-- theory of Echo (EchoKernel contract, `map-over`, ...) applies to it
-- unchanged. This makes the module a Tier-1 derived module (only `Echo` +
-- stdlib).

module EchoFidelity where

open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Echo using (Echo; echo-intro)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

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
-- A fibre is the Echo of the accounting map at the verdict `mapped t`:
-- a source atom together with a proof that it is mapped to that target.
------------------------------------------------------------------------

Fibre : {SA TA : Set} → Translation SA TA → TA → Set
Fibre T t = Echo (account T) (mapped t)

-- The identification with Echo is definitional, so the structure theory of
-- Echo applies to fibres with no transport.
fibre-is-echo :
  {SA TA : Set} (T : Translation SA TA) (t : TA) →
  Fibre T t ≡ Echo (account T) (mapped t)
fibre-is-echo T t = refl

-- A source atom that the account maps to t lies in the fibre of t.
mapped-in-fibre :
  {SA TA : Set} (T : Translation SA TA) (s : SA) (t : TA) →
  account T s ≡ mapped t → Fibre T t
mapped-in-fibre T s t p = s , p

-- Every source atom lies in the fibre of the verdict it received, when that
-- verdict is a mapping (`echo-intro` at the accounting map).
fibre-of-image :
  {SA TA : Set} (T : Translation SA TA) (s : SA) (t : TA) →
  account T s ≡ mapped t → Echo (account T) (account T s)
fibre-of-image T s t _ = echo-intro (account T) s

-- A dropped atom is in no fibre: the two verdicts are different
-- constructors. This is the "dropped means recorded, not hidden" half of
-- the accounting: an atom with a drop reason cannot also be claimed as the
-- source of a target atom.
dropped-not-mapped :
  {TA : Set} {r : String} {t : TA} → dropped r ≡ mapped t → ⊥
dropped-not-mapped ()

dropped-not-in-fibre :
  {SA TA : Set} (T : Translation SA TA) (s : SA) (r : String) →
  account T s ≡ dropped r → (t : TA) → account T s ≡ mapped t → ⊥
dropped-not-in-fibre T s r d t p = dropped-not-mapped (trans (sym d) p)

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
