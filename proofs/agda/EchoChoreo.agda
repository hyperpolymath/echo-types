{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- RETRACTION 2026-05-18 (docs/retractions.adoc R-2026-05-18): comments
-- in this module that assert a "graded comonad", a "universal property
-- / terminal cone", "model-independence", or a "conservativity
-- metatheorem" are RETRACTED claims. The Agda is unchanged and correct;
-- read it as a loss-graded *reindexing modality* (thin-poset action;
-- no nested D_r D_s), a funext-relative *pointwise* mediator property,
-- and carrier-parametricity over a fixed grade poset. Authoritative
-- prose: docs/echo-types/paper.adoc §"Reframing note".

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

----------------------------------------------------------------------
-- Per-decoration composition rung.
--
-- The Choreo decoration is the choice of role: Client or Server.
-- The natural "decoration order" is choreographic reachability —
-- whether a one-way map-square lift takes a `RoleEcho r1 y` to a
-- `RoleEcho r2 y`. Restricting to the canonical lift `client-to-server`
-- (and the reflexive self-loops) gives a 2-element chain
-- `Client ⊑c Server` with three constructors. The reverse step
-- `server-to-client` exists too (swap is involutive), but is not
-- part of the canonical degradation — including it would make the
-- order an equivalence and collapse the rung.
--
-- This is the role/modal analogue of `EchoGraded.degrade-compose`,
-- `EchoLinear.degradeMode-compose`, `EchoIndexed.map-role-indexed-comp`
-- and `EchoEpistemic.knowledge-monotone-comp`. The standard recipe
-- — order, transitivity, propositionality, apply, apply-comp,
-- join, factoring-free compose, via-join restatement — runs
-- through with all proofs definitional once the propositional
-- order is in hand.
--
-- Headlines (pinned in Smoke.agda):
--
--   * _⊑c_                 -- choreographic reachability order
--   * ⊑c-trans             -- transitivity
--   * ⊑c-prop              -- the order is propositional
--   * applyChoreo          -- transport an echo along the order
--   * applyChoreo-comp     -- decomposition: trans equals nesting
--   * _⊔c_                 -- join (Server is top)
--   * ⊑c-⊔c-{left,right,univ}
--   * applyChoreo-compose  -- factoring-free composition law
--   * applyChoreo-via-join -- restated via the join

data _⊑c_ : Role → Role → Set where
  c⊑c : Client ⊑c Client
  c⊑s : Client ⊑c Server
  s⊑s : Server ⊑c Server

⊑c-trans : ∀ {r1 r2 r3 : Role} → r1 ⊑c r2 → r2 ⊑c r3 → r1 ⊑c r3
⊑c-trans c⊑c c⊑c = c⊑c
⊑c-trans c⊑c c⊑s = c⊑s
⊑c-trans c⊑s s⊑s = c⊑s
⊑c-trans s⊑s s⊑s = s⊑s

-- The order is propositional: any two proofs of `r1 ⊑c r2` agree.
-- A discharge clause per constructor is enough; there are no
-- shared-binder cases on this 3-constructor data type.
⊑c-prop : ∀ {r1 r2 : Role} (p1 p2 : r1 ⊑c r2) → p1 ≡ p2
⊑c-prop c⊑c c⊑c = refl
⊑c-prop c⊑s c⊑s = refl
⊑c-prop s⊑s s⊑s = refl

-- Transport an echo along the order. The reflexive cases are
-- definitional identities; the strict step `c⊑s` invokes the
-- existing `client-to-server` map-square lift.
applyChoreo :
  ∀ {r1 r2 : Role} → r1 ⊑c r2 →
  ∀ {y : Bool} → RoleEcho r1 y → RoleEcho r2 y
applyChoreo c⊑c e = e
applyChoreo c⊑s e = client-to-server e
applyChoreo s⊑s e = e

-- Decomposition: composing two ⊑c-steps via `⊑c-trans` and then
-- transporting agrees with transporting twice. Closes `refl` on
-- every reachable constructor pair (4 cases out of the 9 syntactic
-- pairings).
applyChoreo-comp :
  ∀ {r1 r2 r3 : Role}
  (p12 : r1 ⊑c r2) (p23 : r2 ⊑c r3)
  {y : Bool} (e : RoleEcho r1 y) →
  applyChoreo (⊑c-trans p12 p23) e ≡ applyChoreo p23 (applyChoreo p12 e)
applyChoreo-comp c⊑c c⊑c e = refl
applyChoreo-comp c⊑c c⊑s e = refl
applyChoreo-comp c⊑s s⊑s e = refl
applyChoreo-comp s⊑s s⊑s e = refl

-- Join structure: Server is the top role. The join is the role
-- with strictly more "view" — `Server` whenever either argument
-- is `Server`, otherwise `Client`.
_⊔c_ : Role → Role → Role
Client ⊔c Client = Client
Client ⊔c Server = Server
Server ⊔c Client = Server
Server ⊔c Server = Server

⊑c-⊔c-left : ∀ (r1 r2 : Role) → r1 ⊑c (r1 ⊔c r2)
⊑c-⊔c-left Client Client = c⊑c
⊑c-⊔c-left Client Server = c⊑s
⊑c-⊔c-left Server Client = s⊑s
⊑c-⊔c-left Server Server = s⊑s

⊑c-⊔c-right : ∀ (r1 r2 : Role) → r2 ⊑c (r1 ⊔c r2)
⊑c-⊔c-right Client Client = c⊑c
⊑c-⊔c-right Client Server = s⊑s
⊑c-⊔c-right Server Client = c⊑s
⊑c-⊔c-right Server Server = s⊑s

⊑c-⊔c-univ : ∀ {r1 r2 r3 : Role} → r1 ⊑c r3 → r2 ⊑c r3 → (r1 ⊔c r2) ⊑c r3
⊑c-⊔c-univ {Client} {Client} c⊑c c⊑c = c⊑c
⊑c-⊔c-univ {Client} {Client} c⊑s c⊑s = c⊑s
⊑c-⊔c-univ {Client} {Server} c⊑s s⊑s = s⊑s
⊑c-⊔c-univ {Server} {Client} s⊑s c⊑s = s⊑s
⊑c-⊔c-univ {Server} {Server} s⊑s s⊑s = s⊑s

-- Factoring-free composition: any direct r1 ⊑c r3 lift agrees
-- with any factoring r1 ⊑c r2 ⊑c r3, by `applyChoreo-comp` plus
-- `⊑c-prop` on `p13` vs `⊑c-trans p12 p23`. The role/modal
-- analogue of `EchoGraded.degrade-compose`.
applyChoreo-compose :
  ∀ {r1 r2 r3 : Role}
  (p12 : r1 ⊑c r2) (p23 : r2 ⊑c r3) (p13 : r1 ⊑c r3)
  {y : Bool} (e : RoleEcho r1 y) →
  applyChoreo p23 (applyChoreo p12 e) ≡ applyChoreo p13 e
applyChoreo-compose p12 p23 p13 e
  rewrite ⊑c-prop p13 (⊑c-trans p12 p23)
        = sym (applyChoreo-comp p12 p23 e)
  where open import Relation.Binary.PropositionalEquality using (sym)

-- Via-join restatement: for any two paths `p1, p2 : r1 ⊑c r3`,
-- transporting along `p1` agrees with going through the join
-- `r1 ⊔c r2` and then up to r3 via the universal property.
-- (When r2 = r1 the join is r1 and the LHS = RHS definitionally.)
applyChoreo-via-join :
  ∀ {r1 r3 : Role} (r2 : Role)
  (p1 : r1 ⊑c r3) (p2 : r2 ⊑c r3)
  {y : Bool} (e : RoleEcho r1 y) →
  applyChoreo p1 e
  ≡ applyChoreo (⊑c-⊔c-univ p1 p2) (applyChoreo (⊑c-⊔c-left r1 r2) e)
applyChoreo-via-join {Client} {Client} Client c⊑c c⊑c e = refl
applyChoreo-via-join {Client} {Server} Client c⊑s c⊑s e = refl
applyChoreo-via-join {Client} {Server} Server c⊑s s⊑s e = refl
applyChoreo-via-join {Server} {Server} Client s⊑s c⊑s e = refl
applyChoreo-via-join {Server} {Server} Server s⊑s s⊑s e = refl
