{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Gate #3 canonical example: epistemic knowledge update via Echo.
--
-- An agent with imperfect observation tracks the set of consistent
-- worlds.  In a propositional / Goguen-Meseguer style account this
-- set is an equivalence class of worlds; refinement (after a second
-- observation) is the meet of equivalence relations.  In an Echo
-- account, the set IS a type whose inhabitants are worlds paired
-- with proofs of consistency, and refinement is sub-Σ-typing.
--
-- The constructive content differs.  This file demonstrates that
-- the *type* structure of Echo is what makes knowledge update a
-- programmable operation rather than a relation-meet, and proves
-- the load-bearing properties: the refinement map is injective
-- (witness preservation), not surjective (genuine information
-- gain), and the initial knowledge is not even a mere proposition.
--
-- Bridge axis: epistemic.  The README lists "epistemic bridge
-- (indistinguishability and echo-indexed knowledge)" as one of the
-- existing modules' axes; this example concretely instantiates
-- echo-indexed knowledge for a finite world.
--
-- Canonicality (against the new bar):
--
--   (a) Forced.  In type-theoretic epistemic logic, agent-knowledge
--       IS naturally a Σ-type carrying the equality-of-observation
--       witness.  The propositional / equivalence-class account
--       requires either powersets or quotient types; Echo is the
--       direct type-theoretic encoding.  Dynamic update preserves
--       individual world identities through Σ-projection, which
--       quotients do not.
--
--   (b) Bridge axis (epistemic) genuinely active.  The example IS
--       agent-knowledge and refinement of agent-knowledge.
--
--   (c) Replacing Echo with preimage subset, fibre, equivalence
--       class, or refinement-with-propositional-predicate loses the
--       witness type.  Refinement (knowledge update) with Echo is
--       sub-Σ-typing, programmable as a function.  With propositional
--       knowledge, refinement is a relation-meet, not a function on
--       individual witnesses.  See `refine` and `refine-injective`
--       below for the constructive form.
--
-- Falsifier (example-internal): if `obs` were injective on World,
-- every Echo at every value would be at most a singleton, no
-- knowledge state to refine.  Refuted internally by `w₁..w₄` and
-- `distinct-w₁-w₃`.
--
-- Falsifier (load-bearing for refinement): if `refine` (knowledge
-- update from a second observation) were surjective onto initial
-- knowledge, there would be no genuine information gain.  Refuted
-- internally by `not-in-image`.
--
-- Falsifier (canonicality, vs Goguen-Meseguer information-flow):
-- this stops being canonical if the propositional equivalence-
-- class account reproduces Echo's type-data.  Comparison: the
-- equivalence relation is propositional; refinement is a meet of
-- relations (also propositional).  Echo's refinement is a sub-Σ-
-- typing (constructive, with witness preservation).  The accounts
-- agree on which worlds are consistent and disagree on whether
-- knowledge is type-data or proposition-data.  Echo wins for
-- dynamic / programmable knowledge update; the two are tied for
-- static / classical knowledge analysis.
------------------------------------------------------------------------

module examples.EpistemicUpdate where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Self-contained Echo definition.

Echo : ∀ {A B : Set} → (A → B) → B → Set
Echo {A} f y = Σ A (λ x → f x ≡ y)

------------------------------------------------------------------------
-- Worlds and observations.  Three latent variables; the agent
-- can observe the first two but not the third.

World : Set
World = Bool × Bool × Bool

obs : World → Bool
obs (a , _ , _) = a

obs' : World → Bool
obs' (_ , b , _) = b

JointObs : World → Bool × Bool
JointObs w = (obs w , obs' w)

------------------------------------------------------------------------
-- Initial knowledge: agent has observed `obs w = false`.  Four
-- worlds are consistent --- the second and third bits are
-- unconstrained.  Refutes Falsifier 1: this is genuine non-trivial
-- knowledge, not a singleton.

w₁ : Echo obs false
w₁ = (false , false , false) , refl

w₂ : Echo obs false
w₂ = (false , false , true) , refl

w₃ : Echo obs false
w₃ = (false , true , false) , refl

w₄ : Echo obs false
w₄ = (false , true , true) , refl

-- Distinctness witness.  Multiplicity of compatible worlds is real.
distinct-w₁-w₃ : proj₁ w₁ ≡ proj₁ w₃ → ⊥
distinct-w₁-w₃ p = false≢true (cong (λ w → proj₁ (proj₂ w)) p)
  where
    false≢true : false ≡ true → ⊥
    false≢true ()

------------------------------------------------------------------------
-- Refinement (dynamic knowledge update).  After a second observation
-- `obs' w = false`, the agent's knowledge refines: from
-- `Echo obs false` (4 worlds) to `Echo JointObs (false , false)`
-- (2 worlds).  In Echo, this refinement is a function.

refine : Echo JointObs (false , false) → Echo obs false
refine ((a , b , c) , eq) = (a , b , c) , cong proj₁ eq

------------------------------------------------------------------------
-- The refinement map is INJECTIVE.  This is the witness-preservation
-- property: refining knowledge does not collapse worlds.  It is what
-- makes Echo's update programmable rather than a relation-meet.

refine-injective :
  ∀ (e₁ e₂ : Echo JointObs (false , false))
  → proj₁ (refine e₁) ≡ proj₁ (refine e₂)
  → proj₁ e₁ ≡ proj₁ e₂
refine-injective ((_ , _ , _) , _) ((_ , _ , _) , _) p = p

------------------------------------------------------------------------
-- The refinement map is NOT SURJECTIVE.  Specifically, the world
-- (false , true , false) is in the initial knowledge `Echo obs false`
-- but is not in the image of `refine`: it is incompatible with the
-- second observation `obs' w = false`.  This is the formal version
-- of "the second observation gave the agent genuine information".

old-only : Echo obs false
old-only = (false , true , false) , refl

mid : Bool × Bool × Bool → Bool
mid (_ , b , _) = b

not-in-image :
  ∀ (e : Echo JointObs (false , false))
  → proj₁ e ≡ proj₁ old-only
  → ⊥
not-in-image ((_ , b , _) , eq) p = false≢true (trans (sym b≡false) b≡true)
  where
    -- From eq : (a , b) ≡ (false , false), extract b ≡ false.
    b≡false : b ≡ false
    b≡false = cong proj₂ eq

    -- From p : (a , b , c) ≡ (false , true , false), extract b ≡ true.
    b≡true : b ≡ true
    b≡true = cong mid p

    false≢true : false ≡ true → ⊥
    false≢true ()

------------------------------------------------------------------------
-- The load-bearing canonicality result.
--
-- `Echo obs false` is not a mere proposition: it carries strictly
-- more information than "some world is consistent with the
-- observation".  This is the formal version of the (c) argument:
-- propositional / equivalence-class accounts collapse to a
-- truncation of this type, which the type itself rejects.

is-prop : Set → Set
is-prop A = ∀ (x y : A) → x ≡ y

echo-not-prop : is-prop (Echo obs false) → ⊥
echo-not-prop h = distinct-w₁-w₃ (cong proj₁ (h w₁ w₃))
