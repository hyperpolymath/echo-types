{-# OPTIONS --safe --without-K #-}

-- Example 5 (docs/echo-types/examples.md) — database provenance via
-- K-provenance semiring. A tiny model of a database row tagged with a
-- K-provenance annotation, where the query projects to the payload
-- only and forgets the annotation. `Echo project y` captures the lost
-- provenance: distinct provenances at the same projected value give
-- distinct echoes.
--
-- The shape is the same as Example 1 (`square9 / SignedNine` in
-- EchoExamples.agda): a two-element source whose elements project to
-- the same B-value, witnessed by a pair of constructively distinct
-- echoes at that value. The semantic load shifts: where SignedNine
-- carries the *sign* of a numerical preimage, the K-provenance Row
-- carries the *origin annotation* of a database row. Both are the
-- canonical "what does Echo carry?" demonstration; only the second
-- makes the carried data load-bearing in the database setting.
--
-- The K-semiring is taken as the smallest non-trivial choice: Bool
-- with ∧ as product and ∨ as sum (the trust-token / boolean
-- provenance semiring). We do not need the semiring laws to land the
-- echo lemmas — the constructive distinguishability of `true` and
-- `false` is all the machinery the headline theorems consume.
--
-- Cluster context: this module is the formal Agda counterpart to the
-- informal-only Example 5 in examples.md, which sits in the
-- presentation-dependence cluster (PR #76) alongside the parser
-- recovery (Example 9) and abstract-interpretation widening
-- (Example 10) entries. The Σ-over-extra-parameter shape PR #76
-- identifies for the cluster is, in this slice, the Σ on the row's
-- `prov` field.

module EchoExampleProvenance where

open import Echo
open import EchoResidue using
  ( EchoR ; echo-to-residue )

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_)

-- Reusable B-side disequality. Inlined to keep the module's
-- dependency surface to its direct imports (EchoExamples carries the
-- same lemma; we deliberately do not import it to avoid coupling
-- two example modules).
true≢false : true ≢ false
true≢false ()

------------------------------------------------------------
-- A tiny database row + K-provenance annotation.
------------------------------------------------------------

-- A row carries its visible payload (`payload : ℕ`, the value a
-- projection-only query would return) and its K-provenance
-- annotation (`prov : Bool`, the boolean trust-token).
record Row : Set where
  constructor mkRow
  field
    payload : ℕ
    prov    : Bool
open Row

-- The query: project to the payload, discarding the provenance
-- annotation. This is the Echo signal — the function whose fibre at
-- a payload `n` is the set of rows that would answer the query with `n`.
project : Row → ℕ
project = payload

------------------------------------------------------------
-- Two distinct rows with the same payload but distinct provenances.
------------------------------------------------------------

row-with-prov-true : Row
row-with-prov-true = mkRow 0 true

row-with-prov-false : Row
row-with-prov-false = mkRow 0 false

------------------------------------------------------------
-- Headline 1: projection is non-injective — the database query
-- conflates rows that differ in provenance.
------------------------------------------------------------

provenance-collapses :
  Σ Row (λ r₁ → Σ Row (λ r₂ → prov r₁ ≢ prov r₂ × project r₁ ≡ project r₂))
provenance-collapses =
  row-with-prov-true , row-with-prov-false , true≢false , refl

------------------------------------------------------------
-- Headline 2: concrete echoes at the same projected value carrying
-- the two distinct provenances. These are the two inhabitants the
-- query loses when it returns only the payload.
------------------------------------------------------------

echo-prov-true : Echo project 0
echo-prov-true = echo-intro project row-with-prov-true

echo-prov-false : Echo project 0
echo-prov-false = echo-intro project row-with-prov-false

------------------------------------------------------------
-- Headline 3: Echo remembers what projection forgets. The carriers
-- of the two echoes at the same projected value can have distinct
-- provenance annotations — the precise content the projection
-- discarded.
------------------------------------------------------------

echoes-distinguish-provenance :
  prov (proj₁ echo-prov-true) ≢ prov (proj₁ echo-prov-false)
echoes-distinguish-provenance = true≢false

-- Strengthening: the two specific echoes above are themselves
-- distinct as elements of `Echo project 0`. This is the analogue of
-- `echo-plus3≢echo-minus3` in Example 1; the projection on the
-- Σ-first component is `prov` here (not the SignedNine constructor),
-- and that projection separates the two echoes.
echo-prov-true≢echo-prov-false : echo-prov-true ≢ echo-prov-false
echo-prov-true≢echo-prov-false p =
  true≢false (cong (λ e → prov (proj₁ e)) p)

------------------------------------------------------------
-- Headline 4 (optional residue tie-in): projecting an echo down to
-- the trivial residue layer collapses the two distinct provenances
-- to a single residue inhabitant. This is the database analogue of
-- `collapse-residue-identifies` (Example 4): the residue layer
-- forgets the provenance bit the full echo had been carrying, so
-- the two formerly-distinct echoes become residue-indistinguishable.
------------------------------------------------------------

-- Trivial cert over ℕ: the no-information residue layer, parallel
-- to `EchoResidue.TrivialCert` but at the project-side codomain
-- rather than at `⊤`.
ProjCert : ⊤ → ℕ → Set
ProjCert _ _ = ⊤

prov-kappa : Row → ⊤
prov-kappa _ = tt

prov-sound : ∀ r → ProjCert (prov-kappa r) (project r)
prov-sound _ = tt

-- Lower a project-echo into the trivial residue layer. The Cert
-- relation here is no-information at the projected ℕ — exactly
-- the layer at which provenance becomes unrecoverable.
project-to-residue : ∀ {n : ℕ} → Echo project n → EchoR ⊤ ProjCert n
project-to-residue {n} =
  echo-to-residue project prov-kappa ProjCert prov-sound

collapse-via-residue :
  project-to-residue echo-prov-true ≡ project-to-residue echo-prov-false
collapse-via-residue = refl
