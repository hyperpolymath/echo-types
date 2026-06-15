{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL — R4 deliverable (CONTENT-FAITHFUL CARRIER).
-- The variant carrier named in GradedComonad §7: a finite layer carries a
-- REAL copy of the payload A, not the inert ⊤. This is the carrier on which
-- the variance obstruction becomes a LIVE type error (predicted), and the
-- substrate for the F_r ⊣ U_r adjunction attempt in GradedAdjunction.agda.
--
-- FIREWALL (W2): imports Grade (+ stdlib) only. Does NOT depend on the
-- inert-carrier monad/comonad law proofs (GradedMonad / GradedComonad), nor
-- on the inert GradedCarrier. Different carrier; the firewall must hold so the
-- R4 finding is not contaminated by the R3 (vacuous) discharge.
--
-- INVARIANTS (W3/W4): --safe --without-K, ZERO postulates, ZERO holes.
-- An undischargeable coherence is an -- OBLIGATION comment; this file still
-- typechecks clean. NOT imported by any shipped module (W5/W6).

module experimental.echo-additive.GradedCarrierFaithful where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import experimental.echo-additive.Grade
  using (Grade; fin; inf; _+g_)

----------------------------------------------------------------------
-- R4 §1 — The content-faithful carrier Dc : Grade → Set → Set
--
-- Endpoints UNCHANGED from the inert carrier (the variance question must be
-- isolated to the finite-layer content, not the endpoints):
--   Dc (fin 0)       A = A      (Id / no loss)
--   Dc inf           A = ⊤      (total collapse)
-- The ONE change — and the whole point of R4:
--   Dc (fin (suc n)) A = Σ A (λ _ → Dc (fin n) A)   -- a REAL copy of A
--
-- So Dc (fin n) A is the (n+1)-fold product Aⁿ⁺¹ (an A at each of the n+1
-- "layers"). Contrast the inert tower D (fin n) A ≅ A: there every finite
-- layer was a payload-independent ⊤ factor. Here each finite layer GENUINELY
-- carries the payload, so the carrier TRACKS the content the grade counts.
--
-- This is exactly the carrier GradedComonad §7 names as the one on which δ's
-- fin/inf case becomes the total map ⊤ → Σ A (…), UNINHABITED for generic A.

Dc-fin : ℕ → Set → Set
Dc-fin zero    A = A
Dc-fin (suc n) A = Σ A (λ _ → Dc-fin n A)

Dc : Grade → Set → Set
Dc (fin n) A = Dc-fin n A
Dc inf     A = ⊤

----------------------------------------------------------------------
-- R4 §2 — Endpoint sanity (all refl, definitional)

Dc-fin0-Id : ∀ {A} → Dc (fin 0) A ≡ A
Dc-fin0-Id = refl

Dc-inf-Top : ∀ {A} → Dc inf A ≡ ⊤
Dc-inf-Top = refl

-- The fin 0 ≅ Id coercion, named (definitional, both refl).
Dc-fin0-coe : ∀ {A} → Dc (fin 0) A → A
Dc-fin0-coe x = x

Dc-fin0-coe-inv : ∀ {A} → A → Dc (fin 0) A
Dc-fin0-coe-inv x = x

-- The Dc inf ≅ ⊤ collapse, named.
Dc-inf-collapse : ∀ {A} → Dc inf A → ⊤
Dc-inf-collapse _ = tt

----------------------------------------------------------------------
-- R4 §3 — The carrier functor (Dc-fin-map / Dc-map)
--
-- On the content-faithful tower, the functor action maps f over EVERY layer
-- (every copy of A), not just the innermost. This is a genuine functorial
-- action and its identity / composition laws hold by induction.

Dc-fin-map : ∀ {A B : Set} (f : A → B) (n : ℕ) → Dc-fin n A → Dc-fin n B
Dc-fin-map f zero    x        = f x
Dc-fin-map f (suc n) (a , xs) = f a , Dc-fin-map f n xs

Dc-map : ∀ {A B : Set} (f : A → B) (r : Grade) → Dc r A → Dc r B
Dc-map f (fin n) x = Dc-fin-map f n x
Dc-map f inf     _ = tt

-- Functor identity law.
Dc-fin-map-id : ∀ {A : Set} (n : ℕ) (x : Dc-fin n A) →
                Dc-fin-map (λ a → a) n x ≡ x
Dc-fin-map-id zero    x        = refl
Dc-fin-map-id (suc n) (a , xs) = cong (λ z → a , z) (Dc-fin-map-id n xs)

Dc-map-id : ∀ {A : Set} (r : Grade) (x : Dc r A) → Dc-map (λ a → a) r x ≡ x
Dc-map-id (fin n) x = Dc-fin-map-id n x
Dc-map-id inf     _ = refl

-- Functor composition law.
Dc-fin-map-∘ : ∀ {A B C : Set} (g : B → C) (f : A → B) (n : ℕ) (x : Dc-fin n A) →
               Dc-fin-map (λ a → g (f a)) n x ≡ Dc-fin-map g n (Dc-fin-map f n x)
Dc-fin-map-∘ g f zero    x        = refl
Dc-fin-map-∘ g f (suc n) (a , xs) = cong (λ z → g (f a) , z) (Dc-fin-map-∘ g f n xs)

Dc-map-∘ : ∀ {A B C : Set} (g : B → C) (f : A → B) (r : Grade) (x : Dc r A) →
           Dc-map (λ a → g (f a)) r x ≡ Dc-map g r (Dc-map f r x)
Dc-map-∘ g f (fin n) x = Dc-fin-map-∘ g f n x
Dc-map-∘ g f inf     _ = refl

----------------------------------------------------------------------
-- R4 §4 — The DECISIVE inhabitedness facts (the variance witnesses)
--
-- These are the content-faithful analogues of the inert carrier's
-- D-fin-⊤-pt / D-fin-⊤-contr. Their FAILURE is the finding.

-- (a) The monadic combine direction's substrate is FINE: from a real
--     payload we can build a 0-layer carrier (it IS the payload). No
--     invention needed; the payload is given.
Dc-fin0-from-payload : ∀ {A} → A → Dc-fin 0 A
Dc-fin0-from-payload a = a

-- (b) THE OBSTRUCTION SUBSTRATE. On the inert tower, D-fin m ⊤ was inhabited
--     (D-fin-⊤-pt m) for every m, so δ's fin/inf case ⊤ → D-fin m ⊤ was total.
--     Here, Dc-fin (suc n) A = Σ A (…) requires a payload A to inhabit. There
--     is NO generic point: a total map  ⊤ → Dc-fin (suc n) A  would have to
--     PRODUCE an A out of nothing. This is exactly the uninhabited shape the
--     §7 OBLIGATION names. We do NOT define it here (it has no K-free total
--     term); the obstruction is exercised live in GradedAdjunction.agda.
--
-- OBLIGATION (content-faithful invention — the R4 live obstruction):
--   no-generic-point : ∀ {A} n → ⊤ → Dc-fin (suc n) A
--   -- = ⊤ → Σ A (…), UNINHABITED for generic A. NO total K-free term.
--   -- This is the substrate; the adjunction file shows precisely which
--   -- coherence forces a term of this shape.

----------------------------------------------------------------------
-- R4 §5 — Note on the additive split (CONTRAST with the inert carrier)
--
-- On the inert carrier the keystone D-fin-+-split m n was DEFINITIONAL:
--   D-fin (m+n) A ≡ D-fin m (D-fin n A)   (a ⊤-tower of height m+n vs m over n).
-- On the content-faithful carrier this split does NOT hold definitionally:
--   Dc-fin (m+n) A = A^(m+n+1)  but  Dc-fin m (Dc-fin n A) = (A^(n+1))^(m+1)
--                                                          = A^((m+1)(n+1)).
-- m+n+1 ≠ (m+1)(n+1) in general (e.g. m=n=1: 3 ≠ 4). This is the SAME
-- non-fusion GradedCarrier §1 recorded as the reason the content-bearing layer
-- was REJECTED for the monad/comonad law lines. R4 keeps the content-faithful
-- carrier precisely to make the adjunction's comonad half hit this wall.
-- The φ/δ transport-along-D-fin-+-split machinery therefore does NOT port;
-- the adjunction must be stated WITHOUT a nested-composition iso (it is built
-- from unit/counit + the functor action, which is exactly the standard route).
