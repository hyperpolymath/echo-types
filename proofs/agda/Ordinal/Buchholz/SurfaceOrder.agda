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

open import Ordinal.Buchholz.Syntax using (BT; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_)
open import Ordinal.Buchholz.ExtendedOrder using (_<ᵇ⁺_; <ᵇ⇒<ᵇ⁺; <ᵇ⁺-ψα; <ᵇ⁺-+2; wf-<ᵇ⁺)

infix 4 _<ᵇˢ_

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
