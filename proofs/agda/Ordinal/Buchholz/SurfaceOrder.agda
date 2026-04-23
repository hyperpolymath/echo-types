{-# OPTIONS --safe --without-K #-}

-- Direct-order candidate sitting between the current Buchholz core and
-- the comparison-induced wrapper `_<ᵇ⁺_`.
--
-- This relation keeps the current core packaged as one constructor and
-- adds the two historically blocked same-binder shapes as explicit
-- constructors whose premises are still stated in the current core.
--
-- It is not yet the final direct internalization of the full intended
-- order. Its purpose is narrower: give those shapes a direct inductive
-- surface and embed that surface into the already closed wrapper.

module Ordinal.Buchholz.SurfaceOrder where

open import Relation.Nullary using (¬_)
open import Relation.Binary.Core using (_⇒_)
open import Induction.WellFounded using (WellFounded; wf⇒asym; module Subrelation)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

open import Ordinal.OmegaMarkers using (Omega0; _<Ω_; <Ω-irrefl)
open import Ordinal.Buchholz.Syntax using (BT; bzero; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_; <ᵇ-irrefl; <ᵇ-0-+; <ᵇ-ψΩ)
  renaming (<ᵇ-+1 to plus1)
open import Ordinal.Buchholz.ExtendedOrder using (_<ᵇ⁺_; <ᵇ⇒<ᵇ⁺; <ᵇ⁺-ψα; <ᵇ⁺-+2; wf-<ᵇ⁺)
open import Ordinal.Buchholz.VeblenComparisonTarget using
  ( by-second
  ; ≈ᶜ-+
  ; by-payload-++
  ; _≈ᶜ_
  ; payload-psi
  ; _≺P_
  ; pPsiPsi
  )

infix 4 _<ᵇˢ_
infix 4 _<ᵇʳ_

data _<ᵇˢ_ : BT → BT → Set where
  <ᵇˢ-core : ∀ {x y} → x <ᵇ y → x <ᵇˢ y
  <ᵇˢ-ψα   : ∀ {ν α β} → α <ᵇ β → bpsi ν α <ᵇˢ bpsi ν β
  <ᵇˢ-+2   : ∀ {x y₂ z₂} → y₂ <ᵇ z₂ → bplus x y₂ <ᵇˢ bplus x z₂

<ᵇˢ⇒<ᵇ⁺ : _<ᵇˢ_ ⇒ _<ᵇ⁺_
<ᵇˢ⇒<ᵇ⁺ (<ᵇˢ-core x<y) = <ᵇ⇒<ᵇ⁺ x<y
<ᵇˢ⇒<ᵇ⁺ (<ᵇˢ-ψα α<β)   = <ᵇ⁺-ψα α<β
<ᵇˢ⇒<ᵇ⁺ (<ᵇˢ-+2 y<z)   = <ᵇ⁺-+2 y<z

wf-<ᵇˢ : WellFounded _<ᵇˢ_
wf-<ᵇˢ =
  let module SR = Subrelation <ᵇˢ⇒<ᵇ⁺
  in SR.wellFounded wf-<ᵇ⁺

<ᵇˢ-irreflexive : ∀ {x} → ¬ (x <ᵇˢ x)
<ᵇˢ-irreflexive {x} x<x = wf⇒asym wf-<ᵇˢ x<x x<x

-- Exact remaining interface for a recursive direct surface:
-- if the closed wrapper `_<ᵇ⁺_` can be shown stable under same-binder
-- descent with `_<ᵇ⁺_` premises, then the genuinely recursive surface
-- order below becomes available immediately.

record SurfaceLiftInterface : Set where
  field
    lift-ψα⁺ : ∀ {ν α β} → α <ᵇ⁺ β → bpsi ν α <ᵇ⁺ bpsi ν β
    lift-+2⁺ : ∀ {x y₂ z₂} → y₂ <ᵇ⁺ z₂ → bplus x y₂ <ᵇ⁺ bplus x z₂

open SurfaceLiftInterface

data _<ᵇʳ_ (L : SurfaceLiftInterface) : BT → BT → Set where
  <ᵇʳ-core : ∀ {x y} → x <ᵇ y → _<ᵇʳ_ L x y
  <ᵇʳ-ψα   : ∀ {ν α β} → _<ᵇʳ_ L α β → _<ᵇʳ_ L (bpsi ν α) (bpsi ν β)
  <ᵇʳ-+2   : ∀ {x y₂ z₂} → _<ᵇʳ_ L y₂ z₂ → _<ᵇʳ_ L (bplus x y₂) (bplus x z₂)

<ᵇʳ⇒<ᵇ⁺ : ∀ {L x y} → _<ᵇʳ_ L x y → x <ᵇ⁺ y
<ᵇʳ⇒<ᵇ⁺ {L} (<ᵇʳ-core x<y) = <ᵇ⇒<ᵇ⁺ x<y
<ᵇʳ⇒<ᵇ⁺ {L} (<ᵇʳ-ψα α<β)   = lift-ψα⁺ L (<ᵇʳ⇒<ᵇ⁺ α<β)
<ᵇʳ⇒<ᵇ⁺ {L} (<ᵇʳ-+2 y<z)   = lift-+2⁺ L (<ᵇʳ⇒<ᵇ⁺ y<z)

wf-<ᵇʳ : ∀ {L} → WellFounded (λ x y → _<ᵇʳ_ L x y)
wf-<ᵇʳ {L} =
  let module SR = Subrelation <ᵇʳ⇒<ᵇ⁺
  in SR.wellFounded wf-<ᵇ⁺

<ᵇʳ-irreflexive : ∀ {L x} → ¬ (_<ᵇʳ_ L x x)
<ᵇʳ-irreflexive {L} {x} x<x = wf⇒asym (wf-<ᵇʳ {L}) x<x x<x

-- The recursive frontier is not merely unfilled: the current wrapper
-- does not support the required same-binder lifting. A same-left plus
-- witness gives a concrete counterexample to `lift-ψα⁺`.

<ᵇ-same-left-plus-impossible : ∀ {x y z} → ¬ (bplus x y <ᵇ bplus x z)
<ᵇ-same-left-plus-impossible {x} {y} {z} p with p
... | plus1 x<x = <ᵇ-irrefl x<x

<ᵇ⁺-no-ψ-bzero-plus :
  ∀ {ν} →
  ¬ (bpsi ν (bplus bzero bzero) <ᵇ⁺ bpsi ν (bplus bzero (bplus bzero bzero)))
<ᵇ⁺-no-ψ-bzero-plus-helper :
  payload-psi (bplus bzero bzero) ≺P
  payload-psi (bplus bzero (bplus bzero bzero)) →
  ⊥
<ᵇ⁺-no-ψ-bzero-plus-helper (pPsiPsi y<z) = <ᵇ-same-left-plus-impossible y<z

<ᵇ⁺-no-ψ-bzero-plus p with p
... | inj₁ (<ᵇ-ψΩ ν<ν) = <Ω-irrefl ν<ν
... | inj₂ q = <ᵇ⁺-no-ψ-bzero-plus-helper (proj₂ q)

surfaceLiftPremise : bplus bzero bzero <ᵇ⁺ bplus bzero (bplus bzero bzero)
surfaceLiftPremise = by-second ≈ᶜ-+ (by-payload-++ <ᵇ-0-+)

surfaceLiftBlocked : ¬ SurfaceLiftInterface
surfaceLiftBlocked L =
  <ᵇ⁺-no-ψ-bzero-plus {ν = Omega0}
    (lift-ψα⁺ L {ν = Omega0} surfaceLiftPremise)
