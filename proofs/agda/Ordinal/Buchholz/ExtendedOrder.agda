{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

-- Comparison-mediated extension of the current Buchholz core order.
--
-- This module does not replace `Ordinal.Buchholz.Order`. Instead it
-- packages the already-closed comparison model into a relation on
-- `BT` that:
--
--   * contains the current admitted core,
--   * exposes the historical same-binder principles as derived lemmas,
--   * is transitive and well-founded now.
--
-- The direct constructor presentation of the full intended Buchholz
-- order is still open; this is the smallest honest closed wrapper we
-- can land before that internalization is solved.

module Ordinal.Buchholz.ExtendedOrder where

open import Function.Base using (_on_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Construct.On as On using (wellFounded)
open import Induction.WellFounded using (WellFounded; wf⇒asym)

open import Ordinal.Buchholz.Syntax using (BT; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_)
open import Ordinal.Buchholz.VeblenInterface using (VeblenWFInterface)
open import Ordinal.Buchholz.VeblenComparisonTarget using (_≺C_; ≺C-trans; ≺C-wf)
open import Ordinal.Buchholz.VeblenComparisonModel using (cmp-measure; comparison-interface)

infix 4 _<ᵇ⁺_

_<ᵇ⁺_ : Rel BT _
_<ᵇ⁺_ = _≺C_ on cmp-measure

<ᵇ⇒<ᵇ⁺ : _<ᵇ_ ⇒ _<ᵇ⁺_
<ᵇ⇒<ᵇ⁺ = VeblenWFInterface.core-monotone comparison-interface

<ᵇ⁺-ψα : ∀ {ν α β} → α <ᵇ β → bpsi ν α <ᵇ⁺ bpsi ν β
<ᵇ⁺-ψα = VeblenWFInterface.dec-ψα comparison-interface

<ᵇ⁺-+2 : ∀ {x y₂ z₂} → y₂ <ᵇ z₂ → bplus x y₂ <ᵇ⁺ bplus x z₂
<ᵇ⁺-+2 = VeblenWFInterface.dec-+2 comparison-interface

<ᵇ⁺-trans : ∀ {x y z} → x <ᵇ⁺ y → y <ᵇ⁺ z → x <ᵇ⁺ z
<ᵇ⁺-trans = ≺C-trans

wf-<ᵇ⁺ : WellFounded _<ᵇ⁺_
wf-<ᵇ⁺ = On.wellFounded cmp-measure ≺C-wf

<ᵇ⁺-irreflexive : ∀ {x} → ¬ (x <ᵇ⁺ x)
<ᵇ⁺-irreflexive {x} x<x = wf⇒asym wf-<ᵇ⁺ x<x x<x
