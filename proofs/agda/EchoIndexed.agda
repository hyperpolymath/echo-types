{-# OPTIONS --safe --without-K #-}

module EchoIndexed where

open import Echo

open import Level using (Level; _⊔_)
open import Function.Base using (id)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)

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
