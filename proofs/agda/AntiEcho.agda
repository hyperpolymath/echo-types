{-# OPTIONS --safe --without-K #-}

-- AntiEcho — the Σ-dual of Echo.
--
-- Given `Echo f y := Σ (x : A) , (f x ≡ y)` from `Echo.agda`, the
-- minimal-edit-distance dual is `AntiEcho f y := Σ A (λ x → f x ≢ y)`:
-- a domain element together with a constructive proof that `f x` does
-- NOT hit `y`. Same Σ-shape, same universe `a ⊔ b`, same
-- proof-relevance posture; `--safe --without-K`-clean.
--
-- Naming. The name `CoEcho` is ALREADY taken in
-- `EchoFiberTriangulation.agda` for the trivial opposite-orientation
-- fibre `∃ x . y ≡ f x` (Echo composed with `sym`). That construction
-- is a reorientation, not a dual. The negative dual lives here under
-- the distinct name `AntiEcho`. Cf. design note: `coecho.md` §6.
--
-- This thin slice lands obligations 1–4 from `coecho.md` §5 (renamed
-- `antiecho-*`): the carrier, per-element disjointness against Echo,
-- introduction from any witnessed miss, and contravariant `map-over`
-- along the source. Obligation 5 (the partition-with-decidability
-- lemma) lands below as `antiecho-partition-dec` and the
-- codomain-decidability variant `antiecho-partition-codomain-dec`.
-- Obligation 6 (the tropical decomposition `Echo × Π AntiEcho ≃
-- IsArgmin`) lives in `AntiEchoTropical.agda`; the generic-codomain
-- form (lift from the concrete ℕ score to an abstract ordered codomain
-- interface) remains deferred.

module AntiEcho where

open import Level using (Level; _⊔_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Echo using (Echo)

----------------------------------------------------------------------
-- antiecho-def — the carrier.
--
-- Same Σ-shape as `Echo`; only `≡` flips to `≢ := · ≡ y → ⊥`.
-- Universe `a ⊔ b`, matching Echo exactly.

AntiEcho :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → B → Set (a ⊔ b)
AntiEcho {A = A} f y = Σ A (λ x → f x ≢ y)

----------------------------------------------------------------------
-- antiecho-intro — introduction from a constructive miss.
--
-- Trivial: an inhabitant is exactly a pair of a domain element and a
-- miss-proof. Mirrors `Echo.echo-intro` modulo the flip.

antiecho-intro :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  (x : A) → f x ≢ y → AntiEcho f y
antiecho-intro x np = x , np

----------------------------------------------------------------------
-- antiecho-disjoint — per-element disjointness against Echo.
--
-- A single `x : A` cannot witness both `f x ≡ y` and `f x ≢ y`; apply
-- the negation to the equation. Note this is the PER-ELEMENT form,
-- per `coecho.md` §2: the joint statement `Echo f y → AntiEcho f y → ⊥`
-- with possibly distinct witnesses requires decidability on the
-- codomain and lives in the deferred partition lemma. Here the witness
-- is shared explicitly.

antiecho-disjoint :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  (x : A) → f x ≡ y → f x ≢ y → ⊥
antiecho-disjoint x p np = np p

-- The asymmetric joint form `Echo f y → AntiEcho f y → ⊥` (where the
-- two sides may carry different domain witnesses) is intentionally
-- absent: it requires injectivity / decidability on the codomain to
-- collapse the two witnesses, and lives in the deferred partition
-- lemma (`coecho.md` §5 obligation 5). The per-element form above is
-- the postulate-free, K-free primitive.

----------------------------------------------------------------------
-- antiecho-map-over — covariance along the source.
--
-- Given `g : A' → A`, an AntiEcho for the composite `f ∘ g` yields an
-- AntiEcho for `f` by re-applying `g` to the source witness. The miss
-- proof carries over unchanged: `f (g x) ≡ y` IS the proposition
-- `(f ∘ g) x ≡ y`, so the same negation discharges both.
--
-- This is the SOURCE-side `map-over`: misses propagate from the
-- composite back to the outer leg. Cf. `coecho.md` §4 design note 3
-- ("contravariant MapOver"): the MapOver-style version (over a fixed
-- codomain) is a follow-up; this slice ships the simpler composition-
-- along-the-source form.

antiecho-map-over :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {y : B}
  (g : A' → A) → AntiEcho (f ∘ g) y → AntiEcho f y
antiecho-map-over g (x , np) = g x , np

----------------------------------------------------------------------
-- antiecho-partition-dec — every source element classifies to one
-- side, given decidability of `f x ≡ y`.
--
-- The companion to `antiecho-disjoint`. Disjointness ruled out
-- `Echo` and `AntiEcho` *coinciding* on a shared `x`; this lemma
-- says that for *any* `x`, decidability of `f x ≡ y` gives an actual
-- classification of `x` into one side or the other. Together they
-- exhibit `A` as the disjoint union of the Echo-side and the
-- AntiEcho-side parameterised by `y`.
--
-- The asymmetric joint statement `Echo f y → AntiEcho f y → ⊥`
-- (where the two sides carry *different* domain witnesses) is
-- genuinely *not* a theorem and is not what is landed here:
-- consider `f : Bool → Bool` with `f true = true` and
-- `f false = false`; both `Echo f true` (via `(true, refl)`) and
-- `AntiEcho f true` (via `(false, false≢true)`) are inhabited, so
-- the joint statement is refuted by the model. The correct content
-- of "obligation 5" is the per-element classification below.

antiecho-partition-dec :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  (x : A) → Dec (f x ≡ y) → Echo f y ⊎ AntiEcho f y
antiecho-partition-dec x (yes p) = inj₁ (x , p)
antiecho-partition-dec x (no  np) = inj₂ (x , np)

-- Codomain-decidability variant: when *every* `b ≡ y` is decidable
-- (typically because `B` has decidable equality), the classification
-- closes uniformly over `f x`.

antiecho-partition-codomain-dec :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B}
  → (∀ b → Dec (b ≡ y)) → (x : A) → Echo f y ⊎ AntiEcho f y
antiecho-partition-codomain-dec dec? x = antiecho-partition-dec x (dec? _)
