{-# OPTIONS --safe --without-K #-}

-- Gate F1 feasibility spike (docs/echo-types/earn-back-plan.adoc).
--
-- MAKE-OR-BREAK: a *genuine* graded comonad — monoid-graded, with a
-- NESTED comultiplication δ : D (m + n) ⇒ D m (D n), the graded
-- comonad laws, --safe --without-K, ZERO postulates, with Echo as
-- the grade-unit object and D r NOT collapsing to ⊤.
--
-- Candidate: the monoid-graded iterated-residue comonad.
--   * Grade monoid (ℕ, +, 0); comonad unit grade = 0.
--   * R X = X × Bool  — an INFORMATIVE residue layer (not ⊤).
--   * D r = r nested residue layers.  D 0 = Id, so D 0 (Echo f y)
--     IS the bare echo: Echo is the grade-unit object.
--   * δ = iterated-functor coherence; ε = unit-grade identity
--     (legitimate; content is D r a real functor for r>0 + NESTED δ
--     + its laws).
--
-- Result of the spike: the laws close by INDUCTION ON THE GRADE with
-- two structural coe/subst lemmas — no Set-UIP, no funext, and ℕ-UIP
-- (available WITHOUT K via decidable equality / Hedberg) is needed
-- only to reconcile ℕ-equation proofs in coassociativity.  Zero
-- postulates.

module Echo.Bridges.EchoGradedComonadF1 where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)
import Data.Nat.Properties as ℕP
open import Data.Bool.Base using (Bool; true; false)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

----------------------------------------------------------------------
-- ℕ has UIP *without K* (decidable equality ⇒ h-set, Hedberg).
-- Used only in coassociativity, to identify two ℕ-equation proofs.

ℕ-uip : {m n : ℕ} (p q : m ≡ n) → p ≡ q
ℕ-uip = ℕP.≡-irrelevant

----------------------------------------------------------------------
-- The graded functor: r nested informative residue layers.

R : Set → Set
R X = X × Bool

D : ℕ → Set → Set
D zero    A = A
D (suc r) A = R (D r A)

----------------------------------------------------------------------
-- Functor action and laws (funext-free, K-free).

mapD : ∀ r {A B} → (A → B) → D r A → D r B
mapD zero    f x       = f x
mapD (suc r) f (d , b) = mapD r f d , b

mapD-id : ∀ r {A} (x : D r A) → mapD r id x ≡ x
mapD-id zero    x       = refl
mapD-id (suc r) (d , b) = cong (_, b) (mapD-id r d)

mapD-∘ : ∀ r {A B C} (g : B → C) (f : A → B) (x : D r A) →
         mapD r (g ∘ f) x ≡ mapD r g (mapD r f x)
mapD-∘ zero    g f x       = refl
mapD-∘ (suc r) g f (d , b) = cong (_, b) (mapD-∘ r g f d)

----------------------------------------------------------------------
-- Counit at the unit grade; iterated-functor identity; nested δ.

ε : ∀ {A} → D 0 A → A
ε x = x

D-+ : ∀ m n A → D (m + n) A ≡ D m (D n A)
D-+ zero    n A = refl
D-+ (suc m) n A = cong R (D-+ m n A)

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x

-- Comultiplication: NESTED.  δ : D (m + n) A → D m (D n A).
δ : ∀ m n {A} → D (m + n) A → D m (D n A)
δ m n {A} = coe (D-+ m n A)

----------------------------------------------------------------------
-- Non-triviality: D 2 is a real functor, not ⊤ / a proposition.

private
  w₀ w₁ : D 2 Bool
  w₀ = (true , true) , true
  w₁ = (true , true) , false

D2-nontrivial : w₀ ≡ w₁ → false ≡ true
D2-nontrivial p = cong proj₂ (sym p)

----------------------------------------------------------------------
-- Structural coe/subst lemmas (pattern-match on the proof; no UIP).

coe-cong-R : ∀ {X Y : Set} (p : X ≡ Y) (d : X) (b : Bool) →
             coe (cong R p) (d , b) ≡ (coe p d , b)
coe-cong-R refl d b = refl

subst-D-suc : ∀ {A} {j k : ℕ} (p : j ≡ k) (d : D j A) (b : Bool) →
              subst (λ i → D i A) (cong suc p) (d , b)
              ≡ (subst (λ i → D i A) p d , b)
subst-D-suc refl d b = refl

coe-coe : ∀ {A B C : Set} (p : A ≡ B) (q : B ≡ C) (x : A) →
          coe q (coe p x) ≡ coe (trans p q) x
coe-coe refl refl x = refl

coe-D-irr : ∀ {A} {j k : ℕ} (p q : D j A ≡ D k A) (x : D j A) →
            (e : j ≡ k) → p ≡ q → coe p x ≡ coe q x
coe-D-irr p .p x e refl = refl

-- δ-naturality over the R layer.  Peels the outermost R off both
-- sides of δ.  Direct corollary of `coe-cong-R` at p := D-+ m n A,
-- isolated as a lemma so the coassociativity proof can rewrite the
-- nested `δ` without re-deriving the coe push at every step.
δ-suc : ∀ m n {A} (x : D (m + n) A) (b : Bool) →
        δ (suc m) n {A} (x , b) ≡ (δ m n x , b)
δ-suc m n {A} x b = coe-cong-R (D-+ m n A) x b

----------------------------------------------------------------------
-- LAW 1 — counit-right.  e · r = 0 + r = r definitionally, so
-- δ 0 r = coe refl = id and ε is id: the law is definitional.

gc-counit-r : ∀ r {A} (x : D (0 + r) A) →
              ε (δ 0 r x) ≡ x
gc-counit-r r x = refl

----------------------------------------------------------------------
-- LAW 2 — counit-left.  r · e = r + 0; needs the index coercion
-- subst (λ k → D k A) (+-identityʳ r).  Proved by INDUCTION ON r
-- with the two structural lemmas — no Set-UIP, no ℕ-UIP, no funext.

gc-counit-l : ∀ r {A} (x : D (r + 0) A) →
              mapD r ε (δ r 0 x)
              ≡ subst (λ k → D k A) (+-identityʳ r) x
gc-counit-l zero        x       = refl
gc-counit-l (suc r) {A} (d , b) = begin
  mapD (suc r) ε (δ (suc r) 0 (d , b))
    ≡⟨ cong (mapD (suc r) ε) (coe-cong-R (D-+ r 0 A) d b) ⟩
  (mapD r ε (δ r 0 d) , b)
    ≡⟨ cong (_, b) (gc-counit-l r d) ⟩
  (subst (λ k → D k A) (+-identityʳ r) d , b)
    ≡⟨ sym (subst-D-suc (+-identityʳ r) d b) ⟩
  subst (λ k → D k A) (cong suc (+-identityʳ r)) (d , b)
    ≡⟨ cong (λ e → subst (λ k → D k A) e (d , b))
            (ℕ-uip (cong suc (+-identityʳ r)) (+-identityʳ (suc r))) ⟩
  subst (λ k → D k A) (+-identityʳ (suc r)) (d , b)
    ∎
  where open ≡-Reasoning

----------------------------------------------------------------------
-- LAW 3 — coassociativity.  δ associates the triple budget; both
-- nestings land in D m (D n (D p A)) after the index coercion along
-- +-assoc.  Stated in the index-coerced form; the two ℕ-equation
-- proofs are reconciled by ℕ-UIP (no K).
--
--   D ((m+n)+p) A --δ (m+n) p--> D (m+n) (D p A) --δ m n--> D m (D n (D p A))
--   D ((m+n)+p) A --subst +-assoc--> D (m+(n+p)) A --δ m (n+p)-->
--                  D m (D (n+p) A) --mapD m (δ n p)--> D m (D n (D p A))

-- LAW 3 — coassociativity.  Closed 2026-05-20.
--
-- The inductive step factors cleanly through `δ-suc` (δ-naturality
-- over the outer R layer) and `subst-D-suc` (subst commutes with the
-- outer R layer).  Stdlib's `+-assoc (suc m) n p` is *definitionally*
-- `cong suc (+-assoc m n p)` (recursion on left arg), so the
-- ℕ-equation proofs on the two sides are syntactically identical and
-- ℕ-UIP is *not* needed — only ℕ-equation transport along the
-- structural lemmas.  No K, no funext, no postulate.

gc-coassoc : ∀ m n p {A} (x : D ((m + n) + p) A) →
  δ m n (δ (m + n) p x)
  ≡ mapD m (δ n p)
      (δ m (n + p) (subst (λ k → D k A) (+-assoc m n p) x))
gc-coassoc zero    n p x       = refl
gc-coassoc (suc m) n p {A} (x , b) = begin
  δ (suc m) n (δ (suc m + n) p (x , b))
    ≡⟨ cong (δ (suc m) n) (δ-suc (m + n) p x b) ⟩
  δ (suc m) n (δ (m + n) p x , b)
    ≡⟨ δ-suc m n (δ (m + n) p x) b ⟩
  (δ m n (δ (m + n) p x) , b)
    ≡⟨ cong (_, b) (gc-coassoc m n p x) ⟩
  (mapD m (δ n p) (δ m (n + p) (subst (λ k → D k A) (+-assoc m n p) x)) , b)
    ≡⟨ sym (cong (mapD (suc m) (δ n p))
                 (δ-suc m (n + p)
                        (subst (λ k → D k A) (+-assoc m n p) x) b)) ⟩
  mapD (suc m) (δ n p)
    (δ (suc m) (n + p)
       (subst (λ k → D k A) (+-assoc m n p) x , b))
    ≡⟨ cong (λ z → mapD (suc m) (δ n p) (δ (suc m) (n + p) z))
            (sym (subst-D-suc (+-assoc m n p) x b)) ⟩
  mapD (suc m) (δ n p)
    (δ (suc m) (n + p)
       (subst (λ k → D k A) (+-assoc (suc m) n p) (x , b)))
    ∎
  where open ≡-Reasoning
