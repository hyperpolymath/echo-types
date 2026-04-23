{-# OPTIONS --safe --without-K #-}

-- First concrete target carrier for the Veblen-route measure work.
--
-- This module only fixes the target order. The remaining Veblen work is
-- then about defining a measure into this carrier and proving the
-- deferred same-binder obligations there.

module Ordinal.Buchholz.VeblenMeasureTarget where

open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum.Base using (inj₁; inj₂)
open import Induction.WellFounded using (WellFounded)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Ordinal.OmegaMarkers using (OmegaIndex; _<Ω_)
open import Ordinal.Buchholz.Syntax using (BT)
open import Ordinal.Buchholz.Order using (_<ᵇ_)
open import Ordinal.Buchholz.WellFounded using (<Ω-wf; wf-<ᵇ)

Measure : Set
Measure = OmegaIndex × BT

infix 4 _≺M_

_≺M_ : Rel Measure _
_≺M_ = ×-Lex _≡_ _<Ω_ _<ᵇ_

by-index : ∀ {ν μ α β} → ν <Ω μ → (ν , α) ≺M (μ , β)
by-index = inj₁

by-term : ∀ {ν α β} → α <ᵇ β → (ν , α) ≺M (ν , β)
by-term α<β = inj₂ (refl , α<β)

≺M-wf : WellFounded _≺M_
≺M-wf = ×-wellFounded <Ω-wf wf-<ᵇ
