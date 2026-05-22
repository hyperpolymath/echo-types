{-# OPTIONS --safe --without-K #-}

-- AntiEcho × EchoTropical — the tropical decomposition.
--
-- Headline (this module). The tropical argmin carrier `TropEcho y`
-- from `EchoTropical.agda` decomposes definitionally into Echo
-- evidence and a Π-quantified complement bound:
--
--     TropEcho y  ↔  Echo score y × (∀ z → y ≤ score z)
--
-- Both round-trips are `refl` once the Σ-shape of `IsArgmin` is
-- unfolded — no decidability, no funext, no path algebra. This
-- cashes the headline claim from `/tmp/echo-types-exploration/coecho.md`
-- §3 ("Resolution of the EchoTropical tension") at the structural
-- level: `IsArgmin` is exactly Echo (positive provenance witness)
-- conjoined with a uniform negative bound over the codomain
-- complement — the structure that motivated naming `AntiEcho` in the
-- first place. See `coecho.md` §5 obligation 6
-- (`coecho-tropical-decompose`).
--
-- AntiEcho flavour of the optimality side. The Π-bound
-- `∀ z → y ≤ score z` is equivalent (on ℕ) to the AntiEcho-shaped
-- "no candidate produces a strict-below miss":
--
--     ∀ z → score z < y → ⊥
--
-- which reads "for every candidate `z`, the assumption that `z`
-- scores strictly below `y` is empty" — a Π of negative data over
-- the candidate set, exactly the AntiEcho idiom. The forward
-- direction (`≤ ⇒ ¬<`) is uniform and unconditional; the backward
-- direction (`¬< ⇒ ≤`) uses the decidable trichotomy on ℕ and so
-- ships as a separate lemma in the AntiEcho-flavour corollary.
--
-- Scope. New module, neither `AntiEcho.agda` nor `EchoTropical.agda`
-- is modified. Specialised to the concrete `Candidate → ℕ` setting
-- of `EchoTropical.agda`; the generic-codomain version lives in
-- `AntiEchoTropicalGeneric.agda`, parameterised by an abstract
-- `OrderedCodomain` interface (carrier `B`, `_≤_`, `_<_`, `≤⇒¬<`,
-- `¬<⇒≤`).

module AntiEchoTropical where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Echo using (Echo)
open import AntiEcho using (AntiEcho)
open import EchoTropical using (Candidate; score; IsArgmin; TropEcho)

----------------------------------------------------------------------
-- The headline decomposition: TropEcho ↔ Echo × Π-bound.
--
-- `TropEcho y` unfolds to
--     Σ Candidate (λ x → score x ≡ y × (∀ z → y ≤ score z))
-- and the inner second conjunct does not depend on `x`. So
-- Σ-currying / re-association gives the iso with
--     Echo score y × (∀ z → y ≤ score z)
-- on the nose: both round-trips are `refl`, no decidability needed.
--
-- This is the structural half of the
-- "Echo × Π AntiEcho ≃ IsArgmin" claim from `coecho.md` §3 — pure
-- product re-shape. The AntiEcho reading of the Π factor is the
-- corollary that follows.

antiecho-tropical-decompose-to :
  ∀ {y : ℕ} → TropEcho y → Echo score y × (∀ z → y ≤ score z)
antiecho-tropical-decompose-to (x , p , bnd) = (x , p) , bnd

antiecho-tropical-decompose-from :
  ∀ {y : ℕ} → Echo score y × (∀ z → y ≤ score z) → TropEcho y
antiecho-tropical-decompose-from ((x , p) , bnd) = x , p , bnd

antiecho-tropical-decompose-to-from :
  ∀ {y : ℕ} (r : Echo score y × (∀ z → y ≤ score z)) →
  antiecho-tropical-decompose-to (antiecho-tropical-decompose-from r) ≡ r
antiecho-tropical-decompose-to-from ((x , p) , bnd) = refl

antiecho-tropical-decompose-from-to :
  ∀ {y : ℕ} (t : TropEcho y) →
  antiecho-tropical-decompose-from (antiecho-tropical-decompose-to t) ≡ t
antiecho-tropical-decompose-from-to (x , p , bnd) = refl

-- Packaged as a stdlib `_↔_` (bijection / bi-invertible map),
-- matching the convention used for `Echo-comp-iso` and `cancel-iso`
-- in `Echo.agda`.
antiecho-tropical-decompose :
  ∀ (y : ℕ) → TropEcho y ↔ (Echo score y × (∀ z → y ≤ score z))
antiecho-tropical-decompose y =
  mk↔ₛ′
    (λ t → antiecho-tropical-decompose-to {y = y} t)
    (λ r → antiecho-tropical-decompose-from {y = y} r)
    (λ r → antiecho-tropical-decompose-to-from {y = y} r)
    (λ t → antiecho-tropical-decompose-from-to {y = y} t)

----------------------------------------------------------------------
-- `IsArgmin`-level restatement.
--
-- The decomposition above lives at the `TropEcho` level (the Σ over
-- candidates). The per-element version on `IsArgmin` is even more
-- trivial: `IsArgmin x y` IS the product `score x ≡ y × (∀ z → y ≤ score z)`
-- by definition, so the iso to the same product is the identity.
-- Pinned for use by callers who think in `IsArgmin`-shaped terms.

isargmin-decompose-to :
  ∀ {x : Candidate} {y : ℕ} →
  IsArgmin x y → (score x ≡ y) × (∀ z → y ≤ score z)
isargmin-decompose-to (p , bnd) = p , bnd

isargmin-decompose-from :
  ∀ {x : Candidate} {y : ℕ} →
  (score x ≡ y) × (∀ z → y ≤ score z) → IsArgmin x y
isargmin-decompose-from (p , bnd) = p , bnd

isargmin-decompose :
  ∀ (x : Candidate) (y : ℕ) →
  IsArgmin x y ↔ ((score x ≡ y) × (∀ z → y ≤ score z))
isargmin-decompose x y =
  mk↔ₛ′
    (λ a → isargmin-decompose-to   {x = x} {y = y} a)
    (λ r → isargmin-decompose-from {x = x} {y = y} r)
    (λ _ → refl)
    (λ _ → refl)

----------------------------------------------------------------------
-- AntiEcho-flavoured corollary: the Π-bound as a Π of negative data.
--
-- The optimality factor `∀ z → y ≤ score z` is equivalent on ℕ to
-- the AntiEcho-shaped statement
--
--     ∀ z → score z < y → ⊥
--
-- "every candidate, treated as a potential strict-below witness
-- against `y`, lands in the empty type" — a Π of AntiEcho-style
-- negative evidence over the candidate set. This makes the Π factor
-- of the decomposition syntactically AntiEcho-flavoured rather than
-- just structurally a Π.
--
-- Forward direction (`bound → no-strict-below-miss`) is uniform on
-- ℕ and unconditional. Backward direction (`no-strict-below-miss →
-- bound`) uses the decidable trichotomy on ℕ; both directions are
-- discharged here from the constructors of `_≤_` / `_<_` (no extra
-- imports needed because the candidate-side `score` lands in ℕ
-- explicitly, so we only need the two small order conversions
-- below).
--
-- Per `coecho.md` §3 closing remark, the *generic-codomain* backward
-- direction would need a decidable order on the codomain. Here we
-- avoid that hypothesis by working over ℕ concretely (the codomain
-- of `score`); decidable trichotomy on ℕ is pattern-matchable, so
-- the conversion is constructive.

-- y ≤ n → n < y → ⊥
≤⇒¬< : ∀ {y n : ℕ} → y ≤ n → n < y → ⊥
≤⇒¬< z≤n     ()
≤⇒¬< (s≤s p) (s≤s q) = ≤⇒¬< p q

-- ¬ (n < y) → y ≤ n
¬<⇒≤ : ∀ {y n : ℕ} → (n < y → ⊥) → y ≤ n
¬<⇒≤ {y = zero}  _    = z≤n
¬<⇒≤ {y = suc _} {n = zero}  ¬p = ⊥-elim (¬p (s≤s z≤n))
¬<⇒≤ {y = suc _} {n = suc _} ¬p = s≤s (¬<⇒≤ (λ q → ¬p (s≤s q)))

-- The optimality factor, in AntiEcho-shaped form. A Π over
-- candidates of a constructive miss-witness against any value
-- strictly below `y`.
optimality-as-antiecho-flavour-to :
  ∀ {y : ℕ} → (∀ z → y ≤ score z) → (∀ z → score z < y → ⊥)
optimality-as-antiecho-flavour-to bnd z lt = ≤⇒¬< (bnd z) lt

optimality-as-antiecho-flavour-from :
  ∀ {y : ℕ} → (∀ z → score z < y → ⊥) → (∀ z → y ≤ score z)
optimality-as-antiecho-flavour-from no-miss z = ¬<⇒≤ (no-miss z)

----------------------------------------------------------------------
-- Composite: TropEcho ↔ Echo × (Π-of-AntiEcho-flavoured-misses).
--
-- The forward direction is the cleanest landing of the headline:
-- TropEcho data yields Echo evidence + a Π of negative data of
-- AntiEcho shape over the candidate set. The backward direction
-- ships via `¬<⇒≤` on ℕ (decidable codomain hypothesis discharged
-- concretely, not assumed abstractly).

tropdecomp-antiecho-to :
  ∀ {y : ℕ} → TropEcho y →
  Echo score y × (∀ z → score z < y → ⊥)
tropdecomp-antiecho-to t with antiecho-tropical-decompose-to t
... | (e , bnd) = e , optimality-as-antiecho-flavour-to bnd

tropdecomp-antiecho-from :
  ∀ {y : ℕ} →
  Echo score y × (∀ z → score z < y → ⊥) →
  TropEcho y
tropdecomp-antiecho-from (e , no-miss) =
  antiecho-tropical-decompose-from
    (e , optimality-as-antiecho-flavour-from no-miss)

----------------------------------------------------------------------
-- Note on the AntiEcho carrier appearance.
--
-- The Π factor `∀ z → score z < y → ⊥` does not name `AntiEcho`
-- directly because `AntiEcho score y'` for a *specific* `y'` is
-- "some candidate misses `y'`" — a Σ. The dual statement we need
-- here is "no candidate witnesses a value strictly below `y`",
-- which is a Π of *negations* of `score z ≡ y'` for `y' < y`.
-- That is the *Π-form* AntiEcho variant (`coecho.md` §1(c),
-- catalogued as `AntiEcho_Π = ¬ Echo`), specialised to the
-- strict-below stratum. The Σ-form `AntiEcho` from `AntiEcho.agda`
-- is the witness-recording primitive; the Π-form above is the
-- exhaustive global statement. The headline of this module is the
-- structural decomposition (TropEcho ↔ Echo × Π-bound); the
-- AntiEcho-flavoured restatement is the syntactic bridge.
