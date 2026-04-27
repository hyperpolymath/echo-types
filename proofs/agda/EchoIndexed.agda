{-# OPTIONS --safe --without-K #-}

module EchoIndexed where

open import Echo

open import Level using (Level; _⊔_)
open import Function.Base using (id)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (trans-assoc)

-- Phase A: role-indexed echoes.
Echoᵢ :
  ∀ {a b i} {A : Set a} {B : Set b} →
  (I : Set i) → (ι : A → I) → (f : A → B) → I → B → Set (a ⊔ b ⊔ i)
Echoᵢ {A = A} I ι f i y = Σ A (λ x → ι x ≡ i × f x ≡ y)

echoᵢ-intro :
  ∀ {a b i} {A : Set a} {B : Set b}
  (I : Set i) (ι : A → I) (f : A → B) (x : A) →
  Echoᵢ I ι f (ι x) (f x)
echoᵢ-intro I ι f x = x , refl , refl

forget-role :
  ∀ {a b i} {A : Set a} {B : Set b} {I : Set i}
  {ι : A → I} {f : A → B} {idx : I} {y : B} →
  Echoᵢ I ι f idx y → Echo f y
forget-role (x , _ , p) = x , p

role-sound :
  ∀ {a b i} {A : Set a} {B : Set b} {I : Set i}
  {ι : A → I} {f : A → B} {idx : I} {y : B}
  (e : Echoᵢ I ι f idx y) →
  ι (proj₁ e) ≡ idx
role-sound (_ , pᵢ , _) = pᵢ

map-role-indexed :
  ∀ {a a' b i i'}
  {A : Set a} {A' : Set a'} {B : Set b}
  {I : Set i} {I' : Set i'}
  (f : A → B) (f' : A' → B)
  (ι : A → I) (ι' : A' → I')
  (u : A → A') (ρ : I → I')
  (comm-f : ∀ x → f' (u x) ≡ f x)
  (comm-ι : ∀ x → ι' (u x) ≡ ρ (ι x))
  {idx : I} {y : B} →
  Echoᵢ I ι f idx y → Echoᵢ I' ι' f' (ρ idx) y
map-role-indexed f f' ι ι' u ρ comm-f comm-ι (x , pᵢ , p) =
  u x , trans (comm-ι x) (cong ρ pᵢ) , trans (comm-f x) p

cong-id :
  ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) →
  cong id p ≡ p
cong-id refl = refl

map-role-indexed-id :
  ∀ {a b i}
  {A : Set a} {B : Set b} {I : Set i}
  {f : A → B} {ι : A → I}
  {idx : I} {y : B}
  (e : Echoᵢ I ι f idx y) →
  map-role-indexed f f ι ι id id (λ _ → refl) (λ _ → refl) e ≡ e
map-role-indexed-id (x , pᵢ , p)
  rewrite cong-id pᵢ = refl

-- Auxiliaries: `cong` distributes over `trans`, and nested `cong`
-- factors through function composition. Both are standard
-- propositional-equality facts but kept local to keep this module
-- self-contained and aligned with the existing `cong-id` style.
cong-trans :
  ∀ {a b} {A : Set a} {B : Set b} (g : A → B) {x y z : A}
  (p : x ≡ y) (q : y ≡ z) →
  cong g (trans p q) ≡ trans (cong g p) (cong g q)
cong-trans g refl q = refl

cong-∘ :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (g : B → C) (f : A → B) {x y : A} (p : x ≡ y) →
  cong g (cong f p) ≡ cong (λ z → g (f z)) p
cong-∘ g f refl = refl

-- Per-decoration composition law: applying two decoration maps in
-- sequence gives the same result as applying their composite. This
-- is the role-indexed analogue of `map-over-comp` (Echo.agda) and the
-- `degrade-comp` step in the per-decoration composition rung
-- established in EchoGraded.agda.
--
-- The decoration here is the (role-index, role-projection) pair
-- (I, ι); a decoration arrow `(u, ρ, comm-f, comm-ι)` from
-- (A, I, ι, f) to (A', I', ι', f') sits over a fixed codomain B.
-- Composition of two such arrows is the obvious componentwise
-- composition (u' ∘ u, ρ' ∘ ρ) with the obligatory commutation
-- proofs glued by `trans` and `cong`. This lemma certifies that
-- gluing is functorial.
map-role-indexed-comp :
  ∀ {a a' a'' b i i' i''}
  {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
  {I : Set i} {I' : Set i'} {I'' : Set i''}
  (f : A → B) (f' : A' → B) (f'' : A'' → B)
  (ι : A → I) (ι' : A' → I') (ι'' : A'' → I'')
  (u : A → A') (u' : A' → A'')
  (ρ : I → I') (ρ' : I' → I'')
  (comm-f : ∀ x → f' (u x) ≡ f x)
  (comm-f' : ∀ x' → f'' (u' x') ≡ f' x')
  (comm-ι : ∀ x → ι' (u x) ≡ ρ (ι x))
  (comm-ι' : ∀ x' → ι'' (u' x') ≡ ρ' (ι' x'))
  {idx : I} {y : B}
  (e : Echoᵢ I ι f idx y) →
  map-role-indexed f' f'' ι' ι'' u' ρ' comm-f' comm-ι'
    (map-role-indexed f f' ι ι' u ρ comm-f comm-ι e)
  ≡ map-role-indexed f f'' ι ι'' (λ x → u' (u x)) (λ i → ρ' (ρ i))
      (λ x → trans (comm-f' (u x)) (comm-f x))
      (λ x → trans (comm-ι' (u x)) (cong ρ' (comm-ι x)))
      e
map-role-indexed-comp f f' f'' ι ι' ι'' u u' ρ ρ' comm-f comm-f' comm-ι comm-ι'
  (x , pᵢ , p)
  rewrite cong-trans ρ' (comm-ι x) (cong ρ pᵢ)
        | cong-∘ ρ' ρ pᵢ
        | trans-assoc (comm-ι' (u x)) {q = cong ρ' (comm-ι x)}
                                      {r = cong (λ z → ρ' (ρ z)) pᵢ}
        | trans-assoc (comm-f' (u x)) {q = comm-f x} {r = p}
        = refl

-- Forgetting the role index is natural with respect to decoration
-- maps: applying `forget-role` after a `map-role-indexed` is the
-- same as applying the underlying `map-over` after forgetting. This
-- says the role-indexed layer is a strict refinement of the bare
-- `Echo` story — no information is silently introduced or lost
-- when stripping the role.
forget-role-map-role-indexed :
  ∀ {a a' b i i'}
  {A : Set a} {A' : Set a'} {B : Set b}
  {I : Set i} {I' : Set i'}
  (f : A → B) (f' : A' → B)
  (ι : A → I) (ι' : A' → I')
  (u : A → A') (ρ : I → I')
  (comm-f : ∀ x → f' (u x) ≡ f x)
  (comm-ι : ∀ x → ι' (u x) ≡ ρ (ι x))
  {idx : I} {y : B}
  (e : Echoᵢ I ι f idx y) →
  forget-role (map-role-indexed f f' ι ι' u ρ comm-f comm-ι e)
  ≡ map-over (u , comm-f) (forget-role e)
forget-role-map-role-indexed f f' ι ι' u ρ comm-f comm-ι (x , pᵢ , p) = refl

-- Trace-level role-indexed example.
data Role : Set where
  user : Role
  auditor : Role

data Trace : Set where
  user-ok : Trace
  auditor-ok : Trace
  auditor-denied : Trace

trace-role : Trace → Role
trace-role user-ok = user
trace-role auditor-ok = auditor
trace-role auditor-denied = auditor

trace-visible : Trace → Bool
trace-visible user-ok = true
trace-visible auditor-ok = true
trace-visible auditor-denied = false

user-ok≢auditor-ok : user-ok ≢ auditor-ok
user-ok≢auditor-ok ()

echo-user-ok : Echoᵢ Role trace-role trace-visible user true
echo-user-ok = echoᵢ-intro Role trace-role trace-visible user-ok

echo-auditor-ok : Echoᵢ Role trace-role trace-visible auditor true
echo-auditor-ok = echoᵢ-intro Role trace-role trace-visible auditor-ok

echo-user-ok-unindexed : Echo trace-visible true
echo-user-ok-unindexed = forget-role echo-user-ok

echo-auditor-ok-unindexed : Echo trace-visible true
echo-auditor-ok-unindexed = forget-role echo-auditor-ok

echo-user-ok-unindexed≢echo-auditor-ok-unindexed :
  echo-user-ok-unindexed ≢ echo-auditor-ok-unindexed
echo-user-ok-unindexed≢echo-auditor-ok-unindexed p =
  user-ok≢auditor-ok (cong proj₁ p)

user-true-trace-unique :
  ∀ (e : Echoᵢ Role trace-role trace-visible user true) →
  proj₁ e ≡ user-ok
user-true-trace-unique (user-ok , refl , refl) = refl
user-true-trace-unique (auditor-ok , () , _)
user-true-trace-unique (auditor-denied , () , _)

no-user-false-trace :
  Echoᵢ Role trace-role trace-visible user false → ⊥
no-user-false-trace (user-ok , refl , ())
no-user-false-trace (auditor-ok , () , _)
no-user-false-trace (auditor-denied , () , _)
