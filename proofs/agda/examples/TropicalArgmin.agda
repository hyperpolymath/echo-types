{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Gate #3 canonical example: tropical argmin with tie multiplicity.
--
-- In a tropical (min, +) optimisation, the meaningful invariant is
-- not just the optimum value but the TYPE of optima: how many
-- distinct candidates achieve it.  Tie-multiplicity is genuine
-- type-data, not subset-data: a propositional truncation
-- ‖ Echo cost (min cost) ‖ would lose the count.
--
-- This is the lane's strongest example on the "Echo carries strictly
-- more than preimage subset" axis: preimage subsets are membership-
-- only, Echo retains witness multiplicity.
--
-- Domain hook in existing modules: EchoTropical (argmin-style witness
-- residues under tropical collapse).  This file is self-contained.
--
-- Falsifier 1 (example-internal).  If `cost` were injective on Path,
-- every Echo at every value is at most a singleton; tie multiplicity
-- does not exist here.  Refuted by `optimum`, `optimum′`, and
-- `tie-witness`.
--
-- Falsifier 2 (load-bearing).  If `Echo cost 5` is provably
-- contractible (singleton up to equality), tie multiplicity is not
-- type-data here.  Refuted by `tie-witness`: the two argmins are
-- distinct, so Echo cost 5 has at least two distinct inhabitants
-- and is therefore not contractible.
--
-- Falsifier 3 (canonicality).  If tropical algorithms could equally
-- well use the propositional image (mere existence of an argmin)
-- instead of the witness type, this is not distinctively echo-shaped.
-- Counting optimal paths and analysing perturbation behaviour at
-- ties both need the witness type, not just inhabited-or-not.  This
-- file's `echo-not-prop` (below) is the constructive certificate for
-- that claim on this concrete instance: `Echo cost 5` is provably
-- not a mere proposition.  The general theorem (for any non-injective
-- `f`, `Echo f y` is not a mere proposition when `y` has multiple
-- preimages) is not proved here; it is forwarded to Gate #2 in
-- `gate-3-handoff.adoc`.
------------------------------------------------------------------------

module examples.TropicalArgmin where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Self-contained Echo definition.

Echo : ∀ {A B : Set} → (A → B) → B → Set
Echo {A} f y = Σ A (λ x → f x ≡ y)

------------------------------------------------------------------------
-- Three candidate paths.  Concrete data type rather than `Fin 3` to
-- keep coverage trivial and the example self-evident on the page.

data Path : Set where
  p₁ p₂ p₃ : Path

-- Cost function: paths p₁ and p₂ tie at 5; p₃ is strictly worse at 7.
-- The optimum cost over Path is 5, achieved by two distinct paths.
cost : Path → ℕ
cost p₁ = 5
cost p₂ = 5
cost p₃ = 7

------------------------------------------------------------------------
-- Two distinct argmins of `cost` at the optimum value 5.  Refutes
-- Falsifier 1: cost is non-injective at the optimum.

optimum : Echo cost 5
optimum = p₁ , refl

optimum′ : Echo cost 5
optimum′ = p₂ , refl

------------------------------------------------------------------------
-- The argmin witnesses are distinct.  This refutes Falsifier 2 for
-- this concrete instance: `Echo cost 5` has at least two distinct
-- inhabitants and is therefore not contractible.
--
-- The "Echo angle": this distinctness is type-level data preserved
-- by Echo.  Propositional truncation of Echo would collapse it.

p₁≢p₂ : p₁ ≡ p₂ → ⊥
p₁≢p₂ ()

tie-witness : proj₁ optimum ≡ proj₁ optimum′ → ⊥
tie-witness = p₁≢p₂

------------------------------------------------------------------------
-- Retained-constraint theorem.  Every inhabitant of `Echo cost 5`
-- carries a proof that its source has cost exactly 5.

retained-cost : ∀ (e : Echo cost 5) → cost (proj₁ e) ≡ 5
retained-cost (p , q) = q

------------------------------------------------------------------------
-- The load-bearing canonicality result.
--
-- `Echo cost 5` is not a mere proposition: it carries strictly more
-- information than "an argmin exists".  This is the formal version of
-- Falsifier 3's "needs the witness type, not just inhabited-or-not".
--
-- Read together with the handoff document: this is the constructive
-- step toward "Echo of a non-injective function is not the
-- propositional truncation of itself", which is the cleanest
-- distinctness line this lane found for Gate #1.

is-prop : Set → Set
is-prop A = ∀ (x y : A) → x ≡ y

echo-not-prop : is-prop (Echo cost 5) → ⊥
echo-not-prop h = tie-witness (cong proj₁ (h optimum optimum′))

------------------------------------------------------------------------
-- Note on what is NOT proved here.
--
-- A full "5 is the minimum cost over Path" theorem would require a
-- pointwise comparison over Path.  It is straightforwardly provable
-- (cost p₁ = 5, cost p₂ = 5, cost p₃ = 7) but is omitted: the load-
-- bearing fact for THIS gate is tie-multiplicity AT a chosen value,
-- not the minimality proof itself.  Adding the minimality proof
-- would be padding without strengthening the falsifiers.
