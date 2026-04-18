{-# OPTIONS --safe --without-K #-}

module EchoChoreo where

open import Echo

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

true≢false : true ≢ false
true≢false ()

data Role : Set where
  Client : Role
  Server : Role

Global : Set
Global = Bool × Bool

obs : Role → Global → Bool
obs Client g = proj₁ g
obs Server g = proj₂ g

RoleEcho : Role → Bool → Set
RoleEcho r y = Echo (obs r) y

role-constraint : ∀ {r : Role} {y : Bool} (e : RoleEcho r y) → obs r (proj₁ e) ≡ y
role-constraint (_ , p) = p

client-non-injective :
  Σ Global (λ g1 → Σ Global (λ g2 → g1 ≢ g2 × obs Client g1 ≡ obs Client g2))
client-non-injective =
  (true , true) , (true , false) ,
  (λ q → true≢false (cong proj₂ q)) , refl

server-non-injective :
  Σ Global (λ g1 → Σ Global (λ g2 → g1 ≢ g2 × obs Server g1 ≡ obs Server g2))
server-non-injective =
  (true , true) , (false , true) ,
  (λ q → true≢false (cong proj₁ q)) , refl

client-echo₁ : RoleEcho Client true
client-echo₁ = echo-intro (obs Client) (true , true)

client-echo₂ : RoleEcho Client true
client-echo₂ = echo-intro (obs Client) (true , false)

client-echo₁≢client-echo₂ : client-echo₁ ≢ client-echo₂
client-echo₁≢client-echo₂ q = true≢false (cong (λ e → proj₂ (proj₁ e)) q)

swap : Global → Global
swap (b1 , b2) = b2 , b1

swap-square : ∀ g → obs Server (swap g) ≡ obs Client g
swap-square (true , true) = refl
swap-square (true , false) = refl
swap-square (false , true) = refl
swap-square (false , false) = refl

-- Choreographic projection transport across a role-changing commuting square.
client-to-server :
  ∀ {y : Bool} → RoleEcho Client y → RoleEcho Server y
client-to-server = map-square (obs Client) (obs Server) swap id swap-square

scramble-server : Global → Global
scramble-server (c , s) = c , not s

scramble-client-square : ∀ g → obs Client (scramble-server g) ≡ obs Client g
scramble-client-square (true , true) = refl
scramble-client-square (true , false) = refl
scramble-client-square (false , true) = refl
scramble-client-square (false , false) = refl

-- A choreography step may change hidden remote state while preserving local observation.
client-stability :
  ∀ {y : Bool} → RoleEcho Client y → RoleEcho Client y
client-stability = map-square (obs Client) (obs Client) scramble-server id scramble-client-square

client-preimage-class :
  ∀ (e : RoleEcho Client true) →
  proj₁ (proj₁ e) ≡ true × (proj₂ (proj₁ e) ≡ true ⊎ proj₂ (proj₁ e) ≡ false)
client-preimage-class ((true , true) , refl) = refl , inj₁ refl
client-preimage-class ((true , false) , refl) = refl , inj₂ refl
