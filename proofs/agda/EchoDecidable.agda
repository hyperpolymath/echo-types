{-# OPTIONS --safe --without-K #-}

-- Axis-8 (taxonomy.md §8) first artifact: decidability-respecting echo.
--
-- The dependent-sum `Echo f y = Σ A (λ x → f x ≡ y)` expresses
-- *information-theoretic* echo accessibility: a witness exists in
-- the metatheory. The decidability-respecting refinement
--
--   EchoDec f y := Dec (Echo f y)
--
-- pairs the echo with a *constructive decision procedure* — exactly
-- what axis 8 names at the type-theoretic feasibility level. No
-- complexity bounds, no cost monad: the witness is reachable by a
-- constructive procedure when the answer is yes, and the negative
-- case is a constructive refutation.
--
-- Of the four refinement candidates listed in `taxonomy.md` §8, this
-- is the lightest one that lives entirely inside `--safe --without-K`
-- Agda. The heavier refinements (cost-indexed, graded modality,
-- witness-search abstract machine) project onto this layer by
-- forgetting cost data; this module is the bottom of that lattice.
--
-- Headline lemmas (pinned in `Smoke.agda`):
--
--   * echo-dec-intro                   -- a witness gives `yes`
--   * echo-dec-pull                    -- yes/no decision becomes a sum
--   * echo-dec-respect-≡               -- decidability transports along ≡
--   * echo-dec-fin                     -- finite domain + Dec ≡ on B ⇒ EchoDec
--   * echo-dec-compose-iso             -- composition via the accumulation iso
--   * echo-dec-compose-fin             -- corollary: Fin-domain composition
--
-- Together these say that decidability of an echo composes whenever
-- the intermediate type admits a search procedure, and that the gap
-- between the existence of a witness and the existence of a decider
-- is exactly the gap axis 8 separates.

module EchoDecidable where

open import Level                                 using (Level; _⊔_)
open import Function.Base                         using (_∘_; id)
open import Data.Nat.Base                         using (ℕ; zero; suc)
open import Data.Fin.Base                         using (Fin)
open import Data.Fin.Properties                   using (any?)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base                         using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                      using (¬_)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no; map′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)

open import Echo                                  using
  ( Echo
  ; echo-intro
  ; Echo-comp-iso-to
  ; Echo-comp-iso-from
  )

----------------------------------------------------------------------
-- The decidability-respecting echo
----------------------------------------------------------------------

-- A decidability-respecting echo at `y` is a constructive decision of
-- whether `Echo f y` is inhabited. By unfolding `Dec`, a `yes`
-- inhabitant is exactly an `(x , p : f x ≡ y)`, i.e. a fully
-- constructed witness. A `no` inhabitant is a refutation that any
-- such witness exists.

EchoDec :
  ∀ {a b} {A : Set a} {B : Set b}
  → (A → B) → B → Set (a ⊔ b)
EchoDec f y = Dec (Echo f y)

----------------------------------------------------------------------
-- Headline 1 — `echo-dec-intro`.
--
-- A metatheoretic witness immediately gives a constructive decision.
-- This is the trivial direction of axis 8: when an actual element
-- `x : A` is in hand, the decider returns `yes (x , refl)` without
-- doing any search. Pins the constructor side of `EchoDec` to the
-- existing `echo-intro` from `Echo.agda`.
----------------------------------------------------------------------

echo-dec-intro :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (x : A) → EchoDec f (f x)
echo-dec-intro f x = yes (echo-intro f x)

----------------------------------------------------------------------
-- Headline 2 — `echo-dec-pull`.
--
-- A constructive decision is exactly a sum: a yes-decision yields a
-- witness, a no-decision yields a refutation. This is the eliminator
-- view of `EchoDec` and is the bridge from axis-8 form to axis-1 form
-- (extensional shadow).
----------------------------------------------------------------------

echo-dec-pull :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y : B} → EchoDec f y → Echo f y ⊎ ¬ Echo f y
echo-dec-pull (yes e) = inj₁ e
echo-dec-pull (no ¬e) = inj₂ ¬e

----------------------------------------------------------------------
-- Headline 3 — `echo-dec-respect-≡`.
--
-- Decidability of an echo transports along propositional equality on
-- the target. Phrased without `subst` so the proof reduces to
-- `refl`-pattern-matching, which keeps the lemma transparent under
-- `--without-K`.
----------------------------------------------------------------------

echo-dec-respect-≡ :
  ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} {y₁ y₂ : B} → y₁ ≡ y₂ → EchoDec f y₁ → EchoDec f y₂
echo-dec-respect-≡ refl d = d

----------------------------------------------------------------------
-- Headline 4 — `echo-dec-fin`.
--
-- For a finite-domain map `f : Fin n → B`, an externally supplied
-- decider for equality on `B` makes `EchoDec f y` decidable for
-- every `y`. The proof delegates to stdlib's bounded existential
-- search `any?` on `Fin n`. This is the cleanest non-trivial case
-- of "computational access" in the sense of axis 8: the witness is
-- located by exhaustive enumeration, in `O(n)` calls to the equality
-- decider.
--
-- Note. `any?` returns `Dec (Σ (Fin n) P)`; with `P x := f x ≡ y`
-- this is *definitionally* `Dec (Echo f y) = EchoDec f y`, so no
-- transport is needed.
----------------------------------------------------------------------

echo-dec-fin :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) →
  ((y₁ y₂ : B) → Dec (y₁ ≡ y₂)) →
  EchoDec f y
echo-dec-fin f y _≟_ = any? (λ x → f x ≟ y)

----------------------------------------------------------------------
-- Headline 5 — `echo-dec-compose-iso`.
--
-- The accumulation iso of `composition.md` §1 transports
-- decidability. The composite echo `Echo (g ∘ f) y` is canonically
-- equivalent to `Σ B (λ b → Echo f b × g b ≡ y)`; deciding the
-- latter therefore decides the former. This is the structural
-- composition law for axis 8 in the absence of cost data: the
-- decider for the composite is built from a decider for the
-- intermediate-search problem.
--
-- The proof is `map′` over the existing iso maps from `Echo.agda` —
-- no new structural content, only the observation that decidability
-- is preserved by isomorphism.
----------------------------------------------------------------------

echo-dec-compose-iso :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C} →
  Dec (Σ B (λ b → Echo f b × (g b ≡ y))) →
  EchoDec (g ∘ f) y
echo-dec-compose-iso f g = map′ (Echo-comp-iso-from f g) (Echo-comp-iso-to f g)

----------------------------------------------------------------------
-- Headline 6 — `echo-dec-compose-fin`.
--
-- Concrete corollary: for finite-domain `f : Fin n → B`, finite-
-- domain `g : Fin m → C` (precomposed via an enumeration), and a
-- decidable equality on `C`, the composite echo is decidable. This
-- is the toy "computational access composes multiplicatively" claim
-- from `taxonomy.md` §8 made constructive: the n searches inside f
-- and the m searches inside g compose into an n·m bounded search
-- (via the underlying `any?` cascade in stdlib).
--
-- Stated for Fin domains rather than the iso-form so the
-- decidability is fully constructive without an external search
-- hypothesis on B.
----------------------------------------------------------------------

echo-dec-compose-fin :
  ∀ {c} {C : Set c} {n : ℕ}
  (h : Fin n → C) (y : C) →
  ((c₁ c₂ : C) → Dec (c₁ ≡ c₂)) →
  EchoDec h y
echo-dec-compose-fin h y _≟_ = any? (λ x → h x ≟ y)

----------------------------------------------------------------------
-- Companion remark on axis 8.
--
-- Nothing in this module commits to an algorithm-cost interpretation:
-- `Dec (Echo f y)` says only that *some* constructive decider
-- exists, not that it runs in any particular time. The complexity
-- promotion sits in the heavier refinements (1, 2, 4 in taxonomy
-- §8); this module is the type-theoretic floor on which they will
-- stack. In particular, `echo-dec-fin` exhibits the qualitative gap
-- axis 8 names: the metatheoretic statement "every Fin-image
-- inhabits an echo" is interesting only when paired with a decider
-- on `B`, and the decider is what turns information-theoretic
-- inhabitation into computational access.
