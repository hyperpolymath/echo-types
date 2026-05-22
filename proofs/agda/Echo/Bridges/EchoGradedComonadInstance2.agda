{-# OPTIONS --safe --without-K #-}

-- Gate F3 phase 2 — instance 2 of N.  GATE-CLOSING.
--
-- Packages a graded comonad on the FREE MONOID `(List Tag, ++, [])`
-- over a two-element `Tag` index, as an inhabitant of the
-- `EchoGradedComonadInterface.GradedComonadStructure` record.  Combined
-- with `EchoGradedComonadInstance1.nat-instance` at `(ℕ, +, 0)`, this
-- closes Gate F3 of the earn-back plan
-- (`docs/echo-types/earn-back-plan.adoc` §F3): two non-isomorphic
-- grade-monoid instances of the same abstract interface.
--
-- Why the two grade monoids are non-isomorphic.  `(ℕ, +, 0)` is
-- COMMUTATIVE (`m + n = n + m`); `(List Tag, ++, [])` is NOT
-- COMMUTATIVE (`[smol, big] ≠ [big, smol]`, witnessed below by
-- `tag-list-non-commutative`).  No monoid isomorphism between a
-- commutative monoid and a non-commutative one exists, so the two
-- instances cannot be encodings of each other.
--
-- Why the carrier is genuinely different.  The per-element residue
-- layer varies with the grade index (`R smol A = A × Bool`,
-- `R big A = A × ℕ`).  `D (smol ∷ big ∷ []) Bool` is
-- `(Bool × ℕ) × Bool`; `D (big ∷ smol ∷ []) Bool` is
-- `(Bool × Bool) × ℕ`.  These differ in the order of the layer types.
-- A `D r` for the ℕ-graded instance has uniform `A × Bool` layers all
-- the way down; it cannot reach the non-uniform shapes the List
-- instance produces.
--
-- F3 PASSES (provided the laws hold): see the `list-instance`
-- definition at the bottom.  `--safe --without-K`, zero postulates,
-- zero escape pragmas, no funext.  The interface itself
-- (`GradedComonadStructure`) carries no `⊑-prop`-equivalent field —
-- both instances inhabit it cleanly without one.

module Echo.Bridges.EchoGradedComonadInstance2 where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityˡ; ++-identityʳ; ++-assoc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)

open import Echo.Bridges.EchoGradedComonadInterface using (GradedComonadStructure)

----------------------------------------------------------------------
-- Two-element grade index.

data Tag : Set where
  smol big : Tag

----------------------------------------------------------------------
-- Non-isomorphism witness: the grade monoid `(List Tag, ++, [])` is
-- non-commutative; `(ℕ, +, 0)` is.

tag-list-non-commutative
  : (smol ∷ big ∷ []) ≡ (big ∷ smol ∷ []) → smol ≡ big
tag-list-non-commutative ()

----------------------------------------------------------------------
-- Per-element residue layer.  The two residue shapes differ in the
-- type of the second component.

R : Tag → Set → Set
R smol A = A × Bool
R big  A = A × ℕ

----------------------------------------------------------------------
-- The free-monoid-graded functor.

D : List Tag → Set → Set
D []        A = A
D (x ∷ xs)  A = R x (D xs A)

mapD : ∀ xs {A B} → (A → B) → D xs A → D xs B
mapD []          f x       = f x
mapD (smol ∷ xs) f (d , b) = mapD xs f d , b
mapD (big  ∷ xs) f (d , n) = mapD xs f d , n

----------------------------------------------------------------------
-- Functor laws.

mapD-id : ∀ xs {A} (x : D xs A) → mapD xs id x ≡ x
mapD-id []          x       = refl
mapD-id (smol ∷ xs) (d , b) = cong (_, b) (mapD-id xs d)
mapD-id (big  ∷ xs) (d , n) = cong (_, n) (mapD-id xs d)

mapD-∘ : ∀ xs {A B C} (f : B → C) (g : A → B) (x : D xs A) →
         mapD xs (f ∘ g) x ≡ mapD xs f (mapD xs g x)
mapD-∘ []          f g x       = refl
mapD-∘ (smol ∷ xs) f g (d , b) = cong (_, b) (mapD-∘ xs f g d)
mapD-∘ (big  ∷ xs) f g (d , n) = cong (_, n) (mapD-∘ xs f g d)

----------------------------------------------------------------------
-- ε at the unit grade; NESTED δ via an inductively proven type
-- equality (transport, never K).

ε : ∀ {A} → D [] A → A
ε x = x

D-++ : ∀ xs ys A → D (xs ++ ys) A ≡ D xs (D ys A)
D-++ []          ys A = refl
D-++ (smol ∷ xs) ys A = cong (λ T → T × Bool) (D-++ xs ys A)
D-++ (big  ∷ xs) ys A = cong (λ T → T × ℕ)    (D-++ xs ys A)

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x

δ : ∀ xs ys {A} → D (xs ++ ys) A → D xs (D ys A)
δ xs ys {A} = coe (D-++ xs ys A)

----------------------------------------------------------------------
-- Non-triviality witness.  Distinguishes two elements of
-- `D (smol ∷ big ∷ []) Bool` by their outermost Bool component.

private
  w₀ w₁ : D (smol ∷ big ∷ []) Bool
  w₀ = (true , 0) , true
  w₁ = (true , 0) , false

D-nontrivial : w₀ ≡ w₁ → false ≡ true
D-nontrivial p = cong proj₂ (sym p)

----------------------------------------------------------------------
-- Structural lemmas: coe-cong push through the residue layer
-- (per Tag), and subst commutes with the cons (per Tag).

coe-cong-R-smol :
  ∀ {X Y : Set} (p : X ≡ Y) (d : X) (b : Bool) →
  coe (cong (λ T → T × Bool) p) (d , b) ≡ (coe p d , b)
coe-cong-R-smol refl d b = refl

coe-cong-R-big :
  ∀ {X Y : Set} (p : X ≡ Y) (d : X) (n : ℕ) →
  coe (cong (λ T → T × ℕ) p) (d , n) ≡ (coe p d , n)
coe-cong-R-big refl d n = refl

δ-cons-smol :
  ∀ xs ys {A} (d : D (xs ++ ys) A) (b : Bool) →
  δ (smol ∷ xs) ys {A} (d , b) ≡ (δ xs ys d , b)
δ-cons-smol xs ys {A} d b = coe-cong-R-smol (D-++ xs ys A) d b

δ-cons-big :
  ∀ xs ys {A} (d : D (xs ++ ys) A) (n : ℕ) →
  δ (big ∷ xs) ys {A} (d , n) ≡ (δ xs ys d , n)
δ-cons-big xs ys {A} d n = coe-cong-R-big (D-++ xs ys A) d n

subst-D-cons-smol :
  ∀ {A} {js ks : List Tag} (p : js ≡ ks) (d : D js A) (b : Bool) →
  subst (λ ts → D ts A) (cong (smol ∷_) p) (d , b)
  ≡ (subst (λ ts → D ts A) p d , b)
subst-D-cons-smol refl d b = refl

subst-D-cons-big :
  ∀ {A} {js ks : List Tag} (p : js ≡ ks) (d : D js A) (n : ℕ) →
  subst (λ ts → D ts A) (cong (big ∷_) p) (d , n)
  ≡ (subst (λ ts → D ts A) p d , n)
subst-D-cons-big refl d n = refl

----------------------------------------------------------------------
-- LAW 1 — counit-right.  `[] ++ ys = ys` definitionally;
-- `++-identityˡ ys` is itself `refl` in stdlib (`++-identityˡ _ = refl`),
-- so the subst on the RHS reduces to the identity and both sides are
-- syntactically `x`.

gc-counit-r :
  ∀ ys {A} (x : D ([] ++ ys) A) →
  ε (δ [] ys x) ≡ subst (λ ts → D ts A) (++-identityˡ ys) x
gc-counit-r ys x = refl

----------------------------------------------------------------------
-- LAW 2 — counit-left.  Structural induction on `xs`; the cons step
-- splits on the head `Tag` (each constructor has its own residue
-- shape).  Mirrors `EchoGradedComonadF1.gc-counit-l` exactly modulo
-- the per-Tag duplication.

gc-counit-l :
  ∀ xs {A} (x : D (xs ++ []) A) →
  mapD xs ε (δ xs [] x) ≡ subst (λ ts → D ts A) (++-identityʳ xs) x
gc-counit-l []          x       = refl
gc-counit-l (smol ∷ xs) {A} (d , b) = begin
  mapD (smol ∷ xs) ε (δ (smol ∷ xs) [] (d , b))
    ≡⟨ cong (mapD (smol ∷ xs) ε) (δ-cons-smol xs [] d b) ⟩
  (mapD xs ε (δ xs [] d) , b)
    ≡⟨ cong (_, b) (gc-counit-l xs d) ⟩
  (subst (λ ts → D ts A) (++-identityʳ xs) d , b)
    ≡⟨ sym (subst-D-cons-smol (++-identityʳ xs) d b) ⟩
  subst (λ ts → D ts A) (cong (smol ∷_) (++-identityʳ xs)) (d , b)
    ∎
  where open ≡-Reasoning
gc-counit-l (big  ∷ xs) {A} (d , n) = begin
  mapD (big ∷ xs) ε (δ (big ∷ xs) [] (d , n))
    ≡⟨ cong (mapD (big ∷ xs) ε) (δ-cons-big xs [] d n) ⟩
  (mapD xs ε (δ xs [] d) , n)
    ≡⟨ cong (_, n) (gc-counit-l xs d) ⟩
  (subst (λ ts → D ts A) (++-identityʳ xs) d , n)
    ≡⟨ sym (subst-D-cons-big (++-identityʳ xs) d n) ⟩
  subst (λ ts → D ts A) (cong (big ∷_) (++-identityʳ xs)) (d , n)
    ∎
  where open ≡-Reasoning

----------------------------------------------------------------------
-- LAW 3 — coassociativity.  Structural induction on `xs`; cons step
-- splits on the head `Tag`.  Stdlib's `++-assoc (x ∷ xs) ys zs`
-- reduces *definitionally* to `cong (x ∷_) (++-assoc xs ys zs)` (the
-- same pattern as `+-assoc (suc m) n p` on ℕ), so the two
-- list-equation proofs at the chain ends are syntactically identical
-- and no List-UIP is needed.  Mirror of `EchoGradedComonadF1.gc-coassoc`
-- modulo per-Tag duplication.

gc-coassoc :
  ∀ xs ys zs {A} (x : D ((xs ++ ys) ++ zs) A) →
  δ xs ys (δ (xs ++ ys) zs x)
  ≡ mapD xs (δ ys zs)
      (δ xs (ys ++ zs) (subst (λ ts → D ts A) (++-assoc xs ys zs) x))
gc-coassoc []          ys zs x = refl
gc-coassoc (smol ∷ xs) ys zs {A} (d , b) = begin
  δ (smol ∷ xs) ys (δ ((smol ∷ xs) ++ ys) zs (d , b))
    ≡⟨ cong (δ (smol ∷ xs) ys) (δ-cons-smol (xs ++ ys) zs d b) ⟩
  δ (smol ∷ xs) ys (δ (xs ++ ys) zs d , b)
    ≡⟨ δ-cons-smol xs ys (δ (xs ++ ys) zs d) b ⟩
  (δ xs ys (δ (xs ++ ys) zs d) , b)
    ≡⟨ cong (_, b) (gc-coassoc xs ys zs d) ⟩
  (mapD xs (δ ys zs)
     (δ xs (ys ++ zs) (subst (λ ts → D ts A) (++-assoc xs ys zs) d)) , b)
    ≡⟨ sym (cong (mapD (smol ∷ xs) (δ ys zs))
                 (δ-cons-smol xs (ys ++ zs)
                              (subst (λ ts → D ts A) (++-assoc xs ys zs) d)
                              b)) ⟩
  mapD (smol ∷ xs) (δ ys zs)
    (δ (smol ∷ xs) (ys ++ zs)
       (subst (λ ts → D ts A) (++-assoc xs ys zs) d , b))
    ≡⟨ cong (λ z → mapD (smol ∷ xs) (δ ys zs) (δ (smol ∷ xs) (ys ++ zs) z))
            (sym (subst-D-cons-smol (++-assoc xs ys zs) d b)) ⟩
  mapD (smol ∷ xs) (δ ys zs)
    (δ (smol ∷ xs) (ys ++ zs)
       (subst (λ ts → D ts A)
              (cong (smol ∷_) (++-assoc xs ys zs))
              (d , b)))
    ∎
  where open ≡-Reasoning
gc-coassoc (big  ∷ xs) ys zs {A} (d , n) = begin
  δ (big ∷ xs) ys (δ ((big ∷ xs) ++ ys) zs (d , n))
    ≡⟨ cong (δ (big ∷ xs) ys) (δ-cons-big (xs ++ ys) zs d n) ⟩
  δ (big ∷ xs) ys (δ (xs ++ ys) zs d , n)
    ≡⟨ δ-cons-big xs ys (δ (xs ++ ys) zs d) n ⟩
  (δ xs ys (δ (xs ++ ys) zs d) , n)
    ≡⟨ cong (_, n) (gc-coassoc xs ys zs d) ⟩
  (mapD xs (δ ys zs)
     (δ xs (ys ++ zs) (subst (λ ts → D ts A) (++-assoc xs ys zs) d)) , n)
    ≡⟨ sym (cong (mapD (big ∷ xs) (δ ys zs))
                 (δ-cons-big xs (ys ++ zs)
                             (subst (λ ts → D ts A) (++-assoc xs ys zs) d)
                             n)) ⟩
  mapD (big ∷ xs) (δ ys zs)
    (δ (big ∷ xs) (ys ++ zs)
       (subst (λ ts → D ts A) (++-assoc xs ys zs) d , n))
    ≡⟨ cong (λ z → mapD (big ∷ xs) (δ ys zs) (δ (big ∷ xs) (ys ++ zs) z))
            (sym (subst-D-cons-big (++-assoc xs ys zs) d n)) ⟩
  mapD (big ∷ xs) (δ ys zs)
    (δ (big ∷ xs) (ys ++ zs)
       (subst (λ ts → D ts A)
              (cong (big ∷_) (++-assoc xs ys zs))
              (d , n)))
    ∎
  where open ≡-Reasoning

----------------------------------------------------------------------
-- Package as a `GradedComonadStructure` instance.

list-instance : GradedComonadStructure
list-instance = record
  { G            = List Tag
  ; 1G           = []
  ; _·G_         = _++_
  ; ·G-identityˡ = ++-identityˡ
  ; ·G-identityʳ = ++-identityʳ
  ; ·G-assoc     = ++-assoc

  ; D            = D
  ; mapD         = mapD
  ; mapD-id      = mapD-id
  ; mapD-∘       = mapD-∘

  ; ε            = ε
  ; δ            = δ

  ; gc-counit-r  = gc-counit-r
  ; gc-counit-l  = gc-counit-l
  ; gc-coassoc   = gc-coassoc
  }
