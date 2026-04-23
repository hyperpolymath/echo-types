{-# OPTIONS --safe --without-K #-}

-- Direct recursive same-binder closure over the current Buchholz core.
--
-- Unlike the blocked `SurfaceLiftInterface` route, this relation does
-- not ask a single wrapper to be self-stable. Instead each derivation
-- carries a finite same-binder depth, which can be extracted and
-- embedded into the iterated wrapper tower.

module Ordinal.Buchholz.RecursiveSurfaceOrder where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Nullary using (¬_)

open import Ordinal.Buchholz.Syntax using (BT; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_)
open import Ordinal.Buchholz.IteratedExtendedOrder using
  ( LiftedOrder
  ; SurfaceDepth
  ; surf-core
  ; surf-ψα
  ; surf-+2
  ; surface⇒lifted
  ; LiftedOrder-irreflexive
  )

infix 4 _<ᵇʳᶠ_

data _<ᵇʳᶠ_ : BT → BT → Set where
  <ᵇʳᶠ-core : ∀ {x y} → x <ᵇ y → x <ᵇʳᶠ y
  <ᵇʳᶠ-ψα   : ∀ {ν α β} → α <ᵇʳᶠ β → bpsi ν α <ᵇʳᶠ bpsi ν β
  <ᵇʳᶠ-+2   : ∀ {x y z} → y <ᵇʳᶠ z → bplus x y <ᵇʳᶠ bplus x z

<ᵇʳᶠ-depth : ∀ {x y} → x <ᵇʳᶠ y → ℕ
<ᵇʳᶠ-depth (<ᵇʳᶠ-core _) = zero
<ᵇʳᶠ-depth (<ᵇʳᶠ-ψα p)   = suc (<ᵇʳᶠ-depth p)
<ᵇʳᶠ-depth (<ᵇʳᶠ-+2 p)   = suc (<ᵇʳᶠ-depth p)

<ᵇʳᶠ⇒SurfaceDepth : ∀ {x y} (p : x <ᵇʳᶠ y) → SurfaceDepth (<ᵇʳᶠ-depth p) x y
<ᵇʳᶠ⇒SurfaceDepth (<ᵇʳᶠ-core x<y) = surf-core x<y
<ᵇʳᶠ⇒SurfaceDepth (<ᵇʳᶠ-ψα p)     = surf-ψα (<ᵇʳᶠ⇒SurfaceDepth p)
<ᵇʳᶠ⇒SurfaceDepth (<ᵇʳᶠ-+2 p)     = surf-+2 (<ᵇʳᶠ⇒SurfaceDepth p)

SurfaceDepth⇒<ᵇʳᶠ : ∀ {n x y} → SurfaceDepth n x y → x <ᵇʳᶠ y
SurfaceDepth⇒<ᵇʳᶠ (surf-core x<y) = <ᵇʳᶠ-core x<y
SurfaceDepth⇒<ᵇʳᶠ (surf-ψα p)     = <ᵇʳᶠ-ψα (SurfaceDepth⇒<ᵇʳᶠ p)
SurfaceDepth⇒<ᵇʳᶠ (surf-+2 p)     = <ᵇʳᶠ-+2 (SurfaceDepth⇒<ᵇʳᶠ p)

<ᵇʳᶠ-depth-witness : ∀ {x y} (p : x <ᵇʳᶠ y) → Σ ℕ (λ n → SurfaceDepth n x y)
<ᵇʳᶠ-depth-witness p = <ᵇʳᶠ-depth p , <ᵇʳᶠ⇒SurfaceDepth p

<ᵇʳᶠ⇒lifted : ∀ {x y} (p : x <ᵇʳᶠ y) → LiftedOrder (suc (<ᵇʳᶠ-depth p)) x y
<ᵇʳᶠ⇒lifted p = surface⇒lifted (<ᵇʳᶠ⇒SurfaceDepth p)

<ᵇʳᶠ-irreflexive : ∀ {x} → ¬ (x <ᵇʳᶠ x)
<ᵇʳᶠ-irreflexive {x} p = LiftedOrder-irreflexive (suc (<ᵇʳᶠ-depth p)) (<ᵇʳᶠ⇒lifted p)
