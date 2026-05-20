{-# OPTIONS --safe --without-K #-}

-- EchoExampleAbsInt: Example 10 from `docs/echo-types/examples.md`
-- (abstract interpretation via Sign lattice), realised as the
-- canonical "abstraction map collapses many concretes to one
-- abstract value" instance of Echo.
--
-- The carrier is a hand-rolled five-element integer toy
-- `{m2, m1, z, p1, p2}` (i.e. -2, -1, 0, +1, +2). This keeps the
-- example honest (a real `α : ℤ → Sign` would behave identically
-- on each non-zero strict sign region) while avoiding the weight
-- of `Data.Integer` for what is meant to be a small worked
-- example in the examples cluster.
--
-- Abstraction: `α : Carrier → Sign` sends m1, m2 ↦ neg; z ↦ zero;
-- p1, p2 ↦ pos. The non-injectivity of α on the `pos` (and `neg`)
-- regions IS the lost concretion; `Echo α pos` is the carrier of
-- the recovered concrete-class information.
--
-- Cluster relationship: presentation-dependence (PR #76). The
-- abstract-interpretation example is the canonical compiler-analysis
-- lens on Echo — the structured loss is the abstraction, and the
-- intensional core distinguishes which concrete value in a Sign
-- region was the actual program value. The "widening" / approximate
-- variant (Example 6 + axis 2) is NOT addressed here; this module
-- handles only the exact-Galois-abstraction half. Approximate
-- widening would land in `EchoApprox`'s tolerance-graded family.
--
-- Headline lemmas (pinned in Smoke.agda):
--
--   * concretization-collapses        -- Σ-witness of non-injectivity
--   * α-non-injective-on-pos          -- explicit p1 ≠ p2, α p1 ≡ α p2
--   * echo-pos-p1, echo-pos-p2        -- two concretes for the pos region
--   * echo-zero-witness               -- the singleton echo at zero
--   * distinct-echoes-same-sign       -- the headline: two distinct
--                                        Echo α pos witnesses share
--                                        the same abstract value
--   * absint-classification           -- every Echo α pos has carrier
--                                        p1 or p2 (i.e. the concrete
--                                        class over pos is exactly
--                                        the strictly-positive cell
--                                        of the carrier)

module EchoExampleAbsInt where

open import Echo                                  using (Echo; echo-intro)

open import Data.Product.Base                     using (Σ; _×_; _,_; proj₁)
open import Data.Sum.Base                         using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

----------------------------------------------------------------------
-- Sign lattice (no ⊥/⊤ — keep the abstract domain minimal; the
-- ⊥/⊤ extension is the Galois-closure refinement and adds nothing
-- to the "many concretes ↦ one abstract" headline).
----------------------------------------------------------------------

data Sign : Set where
  neg  : Sign
  zero : Sign
  pos  : Sign

----------------------------------------------------------------------
-- Hand-rolled five-element integer carrier. Standing for ℤ but
-- finite, decidable-equality-free (no _≟_ needed for this example),
-- and `--safe --without-K` friendly out of the box.
----------------------------------------------------------------------

data Carrier : Set where
  m2 : Carrier  -- -2
  m1 : Carrier  -- -1
  z  : Carrier  --  0
  p1 : Carrier  -- +1
  p2 : Carrier  -- +2

----------------------------------------------------------------------
-- The abstraction. Galois-style: collapse the strict-sign regions
-- to their representative element of the Sign lattice.
----------------------------------------------------------------------

α : Carrier → Sign
α m2 = neg
α m1 = neg
α z  = zero
α p1 = pos
α p2 = pos

----------------------------------------------------------------------
-- Constructor disjointness (definitional; no postulates).
----------------------------------------------------------------------

p1≢p2 : p1 ≢ p2
p1≢p2 ()

m1≢m2 : m1 ≢ m2
m1≢m2 ()

----------------------------------------------------------------------
-- Headline 1 — `concretization-collapses`.
--
-- The Σ-witness of non-injectivity: two distinct concretes that
-- α identifies. This is the bare information-loss statement, the
-- "shadow collapse" half of the example.
----------------------------------------------------------------------

concretization-collapses :
  Σ Carrier (λ x₁ → Σ Carrier (λ x₂ → x₁ ≢ x₂ × α x₁ ≡ α x₂))
concretization-collapses = p1 , p2 , p1≢p2 , refl

----------------------------------------------------------------------
-- Headline 2 — `α-non-injective-on-pos`.
--
-- The explicit named variant of the above, pinned to the `pos`
-- region. Used downstream to keep proofs about the `pos` Echo
-- carrier readable.
----------------------------------------------------------------------

α-non-injective-on-pos : p1 ≢ p2 × α p1 ≡ α p2
α-non-injective-on-pos = p1≢p2 , refl

----------------------------------------------------------------------
-- Headline 3 — concrete echoes.
--
-- One per representative of the `pos` cell, plus the canonical
-- `zero` witness. The `Echo α pos` carrier is `Σ Carrier (λ x → α x ≡ pos)`;
-- both p1 and p2 inhabit it.
----------------------------------------------------------------------

echo-pos-p1 : Echo α pos
echo-pos-p1 = echo-intro α p1

echo-pos-p2 : Echo α pos
echo-pos-p2 = echo-intro α p2

echo-zero-witness : Echo α zero
echo-zero-witness = echo-intro α z

----------------------------------------------------------------------
-- Headline 4 — `distinct-echoes-same-sign`.
--
-- The example's headline: two distinct echoes that share the same
-- abstract value. The intensional core carries the concrete (p1 vs
-- p2) while the extensional shadow has been quotiented to `pos`.
----------------------------------------------------------------------

echo-pos-p1≢echo-pos-p2 : echo-pos-p1 ≢ echo-pos-p2
echo-pos-p1≢echo-pos-p2 q = p1≢p2 (cong proj₁ q)

distinct-echoes-same-sign :
  Σ (Echo α pos) (λ e₁ → Σ (Echo α pos) (λ e₂ → e₁ ≢ e₂))
distinct-echoes-same-sign = echo-pos-p1 , echo-pos-p2 , echo-pos-p1≢echo-pos-p2

----------------------------------------------------------------------
-- Headline 5 — `absint-classification`.
--
-- The Sign-region classification: every `Echo α pos` has its
-- carrier-projection inhabiting the strictly-positive cell `{p1, p2}`.
-- This is the abstract-interpretation analogue of
-- `EchoCharacteristic.collapse-classification` and the standard
-- "preimage class is the cell of the partition" statement.
--
-- The proof case-splits on the carrier; the impossible cases
-- (m2, m1, z) are ruled out by the proof `α x ≡ pos` reducing to
-- a clash of distinct Sign constructors (Agda's empty-clause `()`).
----------------------------------------------------------------------

absint-classification :
  ∀ (e : Echo α pos) → proj₁ e ≡ p1 ⊎ proj₁ e ≡ p2
absint-classification (m2 , ())
absint-classification (m1 , ())
absint-classification (z  , ())
absint-classification (p1 , _) = inj₁ refl
absint-classification (p2 , _) = inj₂ refl
