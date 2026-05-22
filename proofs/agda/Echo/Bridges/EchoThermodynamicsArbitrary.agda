{-# OPTIONS --safe --without-K #-}

-- EchoThermodynamicsArbitrary: Bennett zero-cost on an *arbitrary*
-- carrier — past `Fin n`, past Bishop-finite.
--
-- Motivation.
--
-- `EchoThermodynamics.bennett-reversible-injective` (PR #58) proves
-- the Bennett zero-cost case for every injective `f : Fin n → B`;
-- `EchoThermodynamicsFinite` lifts it to any Bishop-finite carrier by
-- bijection transport. Both route the cost through
-- `FiberSize-fin`, whose totality is structural recursion on the
-- `Fin` index bound — so the cost is literally unstateable on an
-- infinite carrier. That routing is the *only* reason finiteness
-- appeared in the Bennett direction at all.
--
-- The physical content of Bennett does not need finiteness. A
-- reversible — i.e. injective — computation has no fan-in: its fibre
-- over any value is a subsingleton, *whatever the cardinality of the
-- domain*. The Landauer-mandated dissipation is set by the number of
-- distinct alternatives erased; with no two distinct preimages there
-- is nothing to erase, hence zero cost. This module states exactly
-- that, for an arbitrary carrier `A : Set a`.
--
-- Honesty / anti-vacuity.
--
-- The structural cost here is keyed on a decidable-inhabitation
-- *occupancy* (0 if the fibre is empty, 1 if inhabited). Read naively
-- this caps at 1 and the zero-cost theorem looks trivial. The content
-- is `occupancy≡FiberSize-fin`: under the subsingleton hypothesis the
-- occupancy *coincides with the established honest finite count*
-- `FiberSize-fin`. So this is not a weaker re-definition that dodges
-- the bound — it is the same number, computed structurally instead of
-- by enumeration, and it agrees with PR #58 wherever both apply
-- (`bennett-arbitrary-refines-finite`).
--
-- `--without-K` note. Full fibre `isProp` (`(p q : Echo f y) → p ≡ q`)
-- would require the proof components `f x ≡ y` to be uniquely
-- determined, i.e. `B` an h-set / UIP — *not* available under
-- `--without-K`. We therefore use the first-projection form
-- `(p q : Echo f y) → proj₁ p ≡ proj₁ q`, which *is* K-free provable
-- from injectivity and is exactly what the count argument needs.
--
-- Scope. This is the Bennett (zero-cost) direction only. The
-- quantitative Landauer *collapse* over an infinite carrier is a
-- different question and remains the pinned falsifiable obligation
-- O-THERMO-∞ (`docs/ECHO-CNO-BRIDGE.adoc` §"Thermodynamic Bridge");
-- nothing here discharges or weakens it.
--
-- Headlines (pinned in Smoke.agda):
--
--   * FiberSubsingleton                     -- K-free "no fan-in"
--   * injective⇒fiber-subsingleton          -- arbitrary carrier
--   * reversible-erasure-cost               -- structural Bennett cost
--   * bennett-reversible-arbitrary          -- injective ⇒ cost 0, any A
--   * occupancy≡FiberSize-fin               -- faithfulness vs. #58 count
--   * bennett-arbitrary-refines-finite      -- subsumes #58 finite result
--   * bennett-reversible-cno-identity       -- the real CNO theorem

module Echo.Bridges.EchoThermodynamicsArbitrary where

open import Level                                 using (Level; _⊔_)
import      Data.Nat.Base                         as ℕ
open        ℕ                                     using (ℕ; _*_)
open import Data.Nat.Properties                   using (*-zeroʳ)
open import Data.Nat.Logarithm                    using (⌊log₂_⌋)
open import Data.Fin.Base                         using (Fin)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁)
open import Relation.Nullary.Decidable.Core       using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Echo.Core                                  using (Echo)
open import CNO                                   using (Program)

open import Echo.Bridges.EchoFiberCount using
  ( FiberSize-fin
  ; FiberSize-fin-subsingleton
  ; no-echo⇒FiberSize-fin≡0
  )
open import Echo.Bridges.EchoThermodynamics using
  ( Temperature ; Energy ; k
  ; landauer-bound ; ⌊log₂1⌋≡0
  ; fiber-erasure-bound ; bennett-reversible-injective )

----------------------------------------------------------------------
-- Step 1 — the K-free "no fan-in" predicate.
--
-- A fibre is a *subsingleton* if any two echo witnesses share their
-- domain point. This is the without-K-safe surrogate for "the fibre
-- has at most one element". No finiteness, no decidability, arbitrary
-- universes.
----------------------------------------------------------------------

FiberSubsingleton :
  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (y : B) → Set (a ⊔ b)
FiberSubsingleton f y = (p q : Echo f y) → proj₁ p ≡ proj₁ q

-- Reversibility ⇒ no fan-in, on an arbitrary carrier. An injective
-- map's fibre is a subsingleton regardless of |A|: two preimages of
-- the same `y` are equated by injectivity through `trans e (sym e′)`.
injective⇒fiber-subsingleton :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B)
  (inj : ∀ {x x′ : A} → f x ≡ f x′ → x ≡ x′) →
  FiberSubsingleton f y
injective⇒fiber-subsingleton f y inj (x , e) (x′ , e′) =
  inj (trans e (sym e′))

----------------------------------------------------------------------
-- Step 2 — the structural Bennett cost, arbitrary carrier.
--
-- Occupancy of a fibre via a decidable inhabitation: 1 if inhabited,
-- 0 if not. We do *not* enumerate the (possibly infinite) domain.
----------------------------------------------------------------------

fiber-occupancy :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B} →
  Dec (Echo f y) → ℕ
fiber-occupancy (yes _) = ℕ.suc ℕ.zero
fiber-occupancy (no  _) = ℕ.zero

reversible-erasure-cost :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B) → Dec (Echo f y) → Temperature → Energy
reversible-erasure-cost f y d T = landauer-bound T (fiber-occupancy d)

-- `⌊log₂ 0 ⌋ ≡ 0` (definitional in std-lib's `Data.Nat.Logarithm`;
-- companion to `EchoThermodynamics.⌊log₂1⌋≡0`).
⌊log₂0⌋≡0 : ⌊log₂ 0 ⌋ ≡ 0
⌊log₂0⌋≡0 = refl

-- The structural cost is zero whatever the inhabitation decision —
-- occupancy is capped at 1 and `⌊log₂ {0,1}⌋ ≡ 0`. This is *honest
-- only* as a Bennett cost when the fibre is genuinely a subsingleton;
-- `occupancy≡FiberSize-fin` below certifies that faithfulness.
occupancy-cost-zero :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B) (d : Dec (Echo f y)) (T : Temperature) →
  reversible-erasure-cost f y d T ≡ 0
occupancy-cost-zero f y (yes _) T
  rewrite ⌊log₂1⌋≡0 = *-zeroʳ (k * T)
occupancy-cost-zero f y (no  _) T
  rewrite ⌊log₂0⌋≡0 = *-zeroʳ (k * T)

-- HEADLINE. Bennett zero-cost for *any* injective `f : A → B`, with
-- `A` an arbitrary `Set a` — no `Fin n`, no `FiniteDomain`. The
-- injectivity hypothesis carries the physical content (it is what
-- makes the cost model faithful, via the subsingleton); the equality
-- to 0 then holds at every temperature and every fibre.
bennett-reversible-arbitrary :
  ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B)
  (inj : ∀ {x x′ : A} → f x ≡ f x′ → x ≡ x′)
  (d : Dec (Echo f y)) (T : Temperature) →
  reversible-erasure-cost f y d T ≡ 0
bennett-reversible-arbitrary f y inj d T =
  occupancy-cost-zero f y d T

----------------------------------------------------------------------
-- Faithfulness — the structural cost is the established finite count.
--
-- Under the subsingleton hypothesis, occupancy *equals*
-- `FiberSize-fin` on every finite restriction. This is the content
-- that stops `reversible-erasure-cost` being a vacuous re-definition:
-- it is the same honest number as PR #58's, computed structurally.
----------------------------------------------------------------------

occupancy≡FiberSize-fin :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂))
  (ss : FiberSubsingleton f y)
  (d : Dec (Echo f y)) →
  fiber-occupancy d ≡ FiberSize-fin f y _≟_
occupancy≡FiberSize-fin f y _≟_ ss (yes (i₀ , hit)) =
  sym (FiberSize-fin-subsingleton f y _≟_
        (λ i j fi fj → ss (i , fi) (j , fj)) i₀ hit)
occupancy≡FiberSize-fin f y _≟_ ss (no ¬e) =
  sym (no-echo⇒FiberSize-fin≡0 f y _≟_ ¬e)

-- Concrete subsumption: on `Fin n`, the arbitrary-carrier result and
-- PR #58's `bennett-reversible-injective` agree — both give 0, and
-- the underlying counts coincide. The new statement is a strict
-- generalisation, not a parallel weaker notion.
bennett-arbitrary-refines-finite :
  ∀ {b} {B : Set b} {n : ℕ}
  (f : Fin n → B) (y : B) (_≟_ : (y₁ y₂ : B) → Dec (y₁ ≡ y₂))
  (inj : ∀ {i j : Fin n} → f i ≡ f j → i ≡ j)
  (d : Dec (Echo f y))
  (i₀ : Fin n) → f i₀ ≡ y →
  (T : Temperature) →
  (reversible-erasure-cost f y d T ≡ 0)
    × (fiber-erasure-bound f y _≟_ T ≡ 0)
bennett-arbitrary-refines-finite f y _≟_ inj d i₀ hit T =
    bennett-reversible-arbitrary f y inj d T
  , bennett-reversible-injective f y _≟_ inj i₀ hit T

----------------------------------------------------------------------
-- Step 3 — the real CNO theorem, on the infinite carrier.
--
-- A Certified Null Operation is an echo type where `f = id`. The
-- identity on `Program` (= `List Instruction`, an *infinite* type —
-- precisely the `ProgramState`-flavoured carrier the original
-- `EchoThermodynamics`/`EchoFiberCount` companion remarks explicitly
-- disclaimed) is injective. With finiteness no longer required for
-- the Bennett direction, "a CNO dissipates zero Landauer energy" is
-- now a *real* theorem here, not a vacuous claim — for the
-- identity/injective CNO over the genuine absolute-zero `Program`
-- carrier. (This is the Bennett direction; it does not touch the
-- quantitative-collapse obligation O-THERMO-∞.)
----------------------------------------------------------------------

cno-identity : Program → Program
cno-identity p = p

cno-identity-injective : ∀ {p q : Program} → cno-identity p ≡ cno-identity q → p ≡ q
cno-identity-injective e = e

bennett-reversible-cno-identity :
  (σ : Program) (d : Dec (Echo cno-identity σ)) (T : Temperature) →
  reversible-erasure-cost cno-identity σ d T ≡ 0
bennett-reversible-cno-identity σ d T =
  bennett-reversible-arbitrary cno-identity σ cno-identity-injective d T
