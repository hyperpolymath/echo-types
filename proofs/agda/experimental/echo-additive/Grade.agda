{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL — R0 deliverable.
-- ℕ ∪ {∞} grade semiring for the echo-types additive tower.
-- Session gated by R-2026-05-18 (do-not-reopen); see docs/retractions.adoc.
--
-- What this file IS:
--   The grade semiring (Grade, ⊓g, +g) with the keystone lemmas
--   establishing that finite grades are non-idempotent under + and inf
--   is idempotent (the cap = the absorbing element).
--
-- What this file IS NOT:
--   It does not claim a graded comonad. It does not prove D_r ∘ D_s ≅ D_{r+s}.
--   It does not touch EchoGraded, EchoGradedComonad, or any shipped module.
--
-- INVARIANTS (session-level, non-negotiable):
--   (1) --safe --without-K, no postulates, no holes past R0.
--   (2) Existing shipped modules are READ-ONLY (not edited, not re-exported).
--   (3) This module is not imported by any existing shipped module.
--   (4) R-2026-05-18 is a do-not-reopen marker; unmet obligations park here,
--       never as postulates.

module experimental.echo-additive.Grade where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_; _⊓_; _≤_; s≤s; z≤n; _<_)
open import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
import EchoGraded as Old

----------------------------------------------------------------------
-- Grade: ℕ ∪ {∞}
--
-- fin n = loss of n "units"; fin 0 = no loss (corresponds to Old.keep)
-- inf   = total collapse; the cap (corresponds to Old.forget)

data Grade : Set where
  fin : ℕ → Grade
  inf : Grade

private
  fin-injective : ∀ {m n} → fin m ≡ fin n → m ≡ n
  fin-injective refl = refl

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

----------------------------------------------------------------------
-- Operations

-- _+g_ : additive composition (loss accumulates; inf absorbs).
-- This is the semiring's "multiplication" — path concatenation in min-plus.
infixl 6 _+g_
_+g_ : Grade → Grade → Grade
fin m +g fin n = fin (m + n)
fin _ +g inf   = inf
inf   +g _     = inf

-- _⊓g_ : min (tropical addition; the semiring's "join").
-- inf is the identity: min with ∞ gives the other operand (no constraint).
-- Corresponds to the semilattice join: the cheaper/less-lossy option wins.
infixl 5 _⊓g_
_⊓g_ : Grade → Grade → Grade
fin m ⊓g fin n = fin (m ⊓ n)
fin m ⊓g inf   = fin m
inf   ⊓g g     = g

-- _⊔g_ : max (dual operation; needed to embed the old join Old._⊔g_).
-- inf absorbs; this is the "higher cost" or "more lossy" join.
infixl 5 _⊔g_
_⊔g_ : Grade → Grade → Grade
fin m ⊔g fin n = fin (m ⊔ n)
fin _ ⊔g inf   = inf
inf   ⊔g _     = inf

----------------------------------------------------------------------
-- +g is a commutative monoid with identity fin 0

+g-assoc : ∀ g h k → (g +g h) +g k ≡ g +g (h +g k)
+g-assoc (fin m) (fin n) (fin p) = cong fin (Nat.+-assoc m n p)
+g-assoc (fin _) (fin _) inf     = refl
+g-assoc (fin _) inf     _       = refl
+g-assoc inf     _       _       = refl

+g-identityˡ : ∀ g → fin 0 +g g ≡ g
+g-identityˡ (fin n) = refl   -- 0 + n = n definitionally in Data.Nat.Base
+g-identityˡ inf     = refl

+g-identityʳ : ∀ g → g +g fin 0 ≡ g
+g-identityʳ (fin n) = cong fin (Nat.+-identityʳ n)
+g-identityʳ inf     = refl

+g-comm : ∀ g h → g +g h ≡ h +g g
+g-comm (fin m) (fin n) = cong fin (Nat.+-comm m n)
+g-comm (fin _) inf     = refl
+g-comm inf     (fin _) = refl
+g-comm inf     inf     = refl

----------------------------------------------------------------------
-- inf is absorbing for +g

+g-absorbˡ : ∀ g → inf +g g ≡ inf
+g-absorbˡ _ = refl

+g-absorbʳ : ∀ g → g +g inf ≡ inf
+g-absorbʳ (fin _) = refl
+g-absorbʳ inf     = refl

----------------------------------------------------------------------
-- ⊓g is a commutative idempotent semilattice with identity inf

⊓g-assoc : ∀ g h k → (g ⊓g h) ⊓g k ≡ g ⊓g (h ⊓g k)
⊓g-assoc (fin m) (fin n) (fin p) = cong fin (Nat.⊓-assoc m n p)
⊓g-assoc (fin _) (fin _) inf     = refl
⊓g-assoc (fin _) inf     _       = refl
⊓g-assoc inf     _       _       = refl

⊓g-comm : ∀ g h → g ⊓g h ≡ h ⊓g g
⊓g-comm (fin m) (fin n) = cong fin (Nat.⊓-comm m n)
⊓g-comm (fin _) inf     = refl
⊓g-comm inf     (fin _) = refl
⊓g-comm inf     inf     = refl

⊓g-idem : ∀ g → g ⊓g g ≡ g
⊓g-idem (fin n) = cong fin (Nat.⊓-idem n)
⊓g-idem inf     = refl

⊓g-identityˡ : ∀ g → inf ⊓g g ≡ g
⊓g-identityˡ _ = refl

⊓g-identityʳ : ∀ g → g ⊓g inf ≡ g
⊓g-identityʳ (fin _) = refl
⊓g-identityʳ inf     = refl

----------------------------------------------------------------------
-- +g distributes over ⊓g — making (Grade, ⊓g, +g) a semiring.
-- (This is the min-plus / tropical semiring structure.)

+g-distribˡ-⊓g : ∀ g h k → g +g (h ⊓g k) ≡ (g +g h) ⊓g (g +g k)
+g-distribˡ-⊓g (fin m) (fin n) (fin p) =
  cong fin (Nat.+-distribˡ-⊓ m n p)
  -- OBLIGATION (stdlib name check): this calls
  --   Nat.+-distribˡ-⊓ : ∀ m n p → m + (n ⊓ p) ≡ (m + n) ⊓ (m + p)
  -- from Data.Nat.Properties. Verify this name exists in the local stdlib 2.3.
  -- If absent, prove inline by induction on m (~12 lines, base and step cases
  -- split on whether n ≤ p or p ≤ n via Nat.⊓-sel or Nat.≤-total).
+g-distribˡ-⊓g (fin _) (fin _) inf     = refl
+g-distribˡ-⊓g (fin _) inf     _       = refl
+g-distribˡ-⊓g inf     _       _       = refl

+g-distribʳ-⊓g : ∀ g h k → (h ⊓g k) +g g ≡ (h +g g) ⊓g (k +g g)
+g-distribʳ-⊓g (fin p) (fin m) (fin n) =
  cong fin (Nat.+-distribʳ-⊓ p m n)
  -- OBLIGATION (stdlib name check): this calls
  --   Nat.+-distribʳ-⊓ : ∀ p m n → (m ⊓ n) + p ≡ (m + p) ⊓ (n + p)
  -- from Data.Nat.Properties. Same caveat as above.
+g-distribʳ-⊓g inf     (fin _) (fin _) = refl
+g-distribʳ-⊓g (fin _) (fin _) inf     = refl
+g-distribʳ-⊓g inf     (fin _) inf     = refl
+g-distribʳ-⊓g (fin _) inf     _       = refl
+g-distribʳ-⊓g inf     inf     _       = refl

----------------------------------------------------------------------
-- Keystone lemmas
--
-- The architectural keystone (held, not yet proven at rung R3):
--   In (Grade, ⊓g, +g), ∞ is idempotent under +g and absorbing.
--   Every fin (suc n) is NON-idempotent under +g.
--   Therefore: a non-idempotent additive tower terminated by an
--   idempotent cap — the cap IS the absorbing element, not a
--   separate gadget.

-- inf is +g-idempotent (definitionally):
+g-inf-idem : inf +g inf ≡ inf
+g-inf-idem = refl

-- fin 0 is +g-idempotent too (0 + 0 = 0), as expected for the monoidal unit:
+g-zero-idem : fin 0 +g fin 0 ≡ fin 0
+g-zero-idem = refl

-- Every POSITIVE finite grade is NOT +g-idempotent.
-- Proof: fin(suc n) + fin(suc n) = fin(suc n + suc n) = fin(suc(n + suc n))
--        = fin(suc(suc(n + n)))  [by Nat.+-suc]
-- From the hypothesised equality, by suc-injectivity twice:
--        suc(n + n) = n
-- But n ≤ n + n [Nat.m≤m+n], so n < suc(n + n), contradicting suc(n+n) = n.
+g-suc-not-idempotent : ∀ n → fin (suc n) +g fin (suc n) ≢ fin (suc n)
+g-suc-not-idempotent n eq =
  Nat.<-irrefl (sym step3) (s≤s (Nat.m≤m+n n n))
  where
    -- fin (suc n) +g fin (suc n)
    --   = fin (suc n + suc n)          [by _+g_ definition]
    --   = fin (suc (n + suc n))        [suc n + suc n = suc (n + suc n) definitionally]
    step1 : suc n + suc n ≡ suc n
    step1 = fin-injective eq
    step2 : n + suc n ≡ n
    step2 = suc-inj step1
    -- Nat.+-suc n n : n + suc n ≡ suc (n + n)
    step3 : suc (n + n) ≡ n
    step3 = trans (sym (Nat.+-suc n n)) step2
    -- Now: n ≤ n + n   [Nat.m≤m+n n n]
    --      n < suc(n + n)  [Nat.s≤s of above]
    --      suc(n + n) ≡ n  [step3]
    --      n ≡ suc(n + n)  [sym step3]
    --  ⟹  ¬ (n < suc(n+n))  [Nat.<-irrefl (sym step3)]
    --  contradiction with  n < suc(n+n)  [Nat.s≤s (Nat.m≤m+n n n)]

----------------------------------------------------------------------
-- Embedding of the old 3-grade lattice into the new tower
--
-- The old Grade (EchoGraded.Grade = {keep, residue, forget}) embeds as:
--   keep    ↦ fin 0   (additive identity; no loss)
--   residue ↦ fin 1   (any suc n works; fin 1 is the minimal choice)
--   forget  ↦ inf     (absorbing element; total collapse)
--
-- This is the SEED of R7 conservativity: the finished ℕ∪{∞} object
-- must restrict on {fin 0, fin 1, inf} to the surviving thin-poset
-- action of present-day echo-types — NOT to the retracted comonad.
-- Full R7 is out of scope; these lemmas establish that the embedding
-- exists and typechecks.

embed : Old.Grade → Grade
embed Old.keep    = fin 0
embed Old.residue = fin 1
embed Old.forget  = inf

-- Identity-element correspondence:
embed-keep-is-+g-identity : embed Old.keep ≡ fin 0
embed-keep-is-+g-identity = refl

-- Absorber correspondence:
embed-forget-is-+g-absorber : embed Old.forget ≡ inf
embed-forget-is-+g-absorber = refl

-- Join-preservation: the old join (max in loss order) embeds as the new ⊔g.
-- All 9 cases are refl by computation.
embed-preserves-join : ∀ g h → embed (Old._⊔g_ g h) ≡ embed g ⊔g embed h
embed-preserves-join Old.keep    Old.keep    = refl
embed-preserves-join Old.keep    Old.residue = refl
embed-preserves-join Old.keep    Old.forget  = refl
embed-preserves-join Old.residue Old.keep    = refl
embed-preserves-join Old.residue Old.residue = refl
embed-preserves-join Old.residue Old.forget  = refl
embed-preserves-join Old.forget  Old.keep    = refl
embed-preserves-join Old.forget  Old.residue = refl
embed-preserves-join Old.forget  Old.forget  = refl

-- OBLIGATION (R7): prove embed is order-monotone and a semiring-fragment
-- morphism from (Old.Grade, Old._≤g_) into (Grade, ≤g-new).
-- Specifically:
--   ∀ g h → Old._≤g_ g h → embed g ≤g-new embed h
-- where ≤g-new is the ℕ-order extended to ℕ∪{∞}.
-- Deferred to rung R7. Park here; do not postulate.
