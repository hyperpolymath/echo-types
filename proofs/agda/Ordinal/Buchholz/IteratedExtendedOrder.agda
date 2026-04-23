{-# OPTIONS --safe --without-K #-}

-- Systematic finite iteration of the comparison-induced wrapper.
--
-- The self-lift theorem for `_<ᵇ⁺_` is false, but the wrapper pattern
-- itself survives finite iteration. This module packages that pattern
-- through an explicit step operator on closed wrappers and a finite
-- depth family of surface derivations embedding into the iterated
-- wrappers.

module Ordinal.Buchholz.IteratedExtendedOrder where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded; ×-wellFounded')
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_on_)
open import Induction.WellFounded using (WellFounded; wf⇒asym; module Subrelation)
open import Relation.Binary.Construct.On as On using (wellFounded)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Ordinal.Buchholz.Syntax using (BT; bzero; bplus; bpsi)
open import Ordinal.Buchholz.Order using (_<ᵇ_; <ᵇ-trans)
open import Ordinal.Buchholz.WellFounded using (wf-<ᵇ)
open import Ordinal.Buchholz.VeblenComparisonTarget using
  ( Payload
  ; payload-neutral
  ; payload-psi
  ; payload-plus
  ; _≈ᶜ_
  ; ≈ᶜ-+
  ; ≈ᶜ-ψ
  ; ≈ᶜ-trans
  ; <ᵇ-respʳ-≈ᶜ
  ; <ᵇ-chain-≈ᶜ
  )
open import Ordinal.Buchholz.VeblenComparisonModel using (cmp-measure)

record Wrapper : Set₁ where
  field
    rel   : Rel BT _
    wf    : WellFounded rel
    trans : Transitive rel

open Wrapper

coreWrapper : Wrapper
coreWrapper = record
  { rel   = _<ᵇ_
  ; wf    = wf-<ᵇ
  ; trans = <ᵇ-trans
  }

module Step (W : Wrapper) where
  open Wrapper W renaming (rel to _<W_; wf to wfW; trans to transW)

  data PayloadOrder : Payload → Payload → Set where
    pPsiPsi   : ∀ {α β} → α <W β → PayloadOrder (payload-psi α) (payload-psi β)
    pPsiPlus  : ∀ {α β y} → α <W β → PayloadOrder (payload-psi α) (payload-plus β y)
    pPlusPlus : ∀ {a y z} → y <W z → PayloadOrder (payload-plus a y) (payload-plus a z)

  payload-rank : Payload → BT × BT
  payload-rank payload-neutral    = bzero , bzero
  payload-rank (payload-psi α)    = α , bzero
  payload-rank (payload-plus a y) = a , y

  PayloadRankOrder : Rel (BT × BT) _
  PayloadRankOrder = ×-Lex _≡_ _<W_ _<W_

  payload-embed : PayloadOrder ⇒ (PayloadRankOrder on payload-rank)
  payload-embed (pPsiPsi α<β)   = inj₁ α<β
  payload-embed (pPsiPlus α<β)  = inj₁ α<β
  payload-embed (pPlusPlus y<z) = inj₂ (refl , y<z)

  payload-wf : WellFounded PayloadOrder
  payload-wf =
    let module SR = Subrelation payload-embed
    in SR.wellFounded (wellFounded payload-rank (×-wellFounded wfW wfW))

  payload-trans : Transitive PayloadOrder
  payload-trans (pPsiPsi α<β)   (pPsiPsi β<γ)   = pPsiPsi (transW α<β β<γ)
  payload-trans (pPsiPsi α<β)   (pPsiPlus β<γ)  = pPsiPlus (transW α<β β<γ)
  payload-trans (pPsiPlus α<β)  (pPlusPlus _)   = pPsiPlus α<β
  payload-trans (pPlusPlus y<z) (pPlusPlus z<w) = pPlusPlus (transW y<z z<w)

  ComparisonOrder : Rel (BT × Payload) _
  ComparisonOrder = ×-Lex _≈ᶜ_ _<ᵇ_ PayloadOrder

  comparison-trans : Transitive ComparisonOrder
  comparison-trans (inj₁ x<y)           (inj₁ y<z)            = inj₁ (<ᵇ-trans x<y y<z)
  comparison-trans (inj₁ x<y)           (inj₂ (y≈z , _))      = inj₁ (<ᵇ-respʳ-≈ᶜ y≈z x<y)
  comparison-trans (inj₂ (x≈y , _))     (inj₁ y<z)            = inj₁ (<ᵇ-chain-≈ᶜ x≈y y<z)
  comparison-trans (inj₂ (x≈y , px<qy)) (inj₂ (y≈z , qy<rz)) =
    inj₂ (≈ᶜ-trans x≈y y≈z , payload-trans px<qy qy<rz)

  comparison-wf : WellFounded ComparisonOrder
  comparison-wf = ×-wellFounded' ≈ᶜ-trans <ᵇ-respʳ-≈ᶜ wf-<ᵇ payload-wf

  _<step_ : Rel BT _
  _<step_ = ComparisonOrder on cmp-measure

  wf-step : WellFounded _<step_
  wf-step = On.wellFounded cmp-measure comparison-wf

  ψ-step : ∀ {ν α β} → α <W β → bpsi ν α <step bpsi ν β
  ψ-step α<β = inj₂ (≈ᶜ-ψ , pPsiPsi α<β)

  +2-step : ∀ {x y z} → y <W z → bplus x y <step bplus x z
  +2-step y<z = inj₂ (≈ᶜ-+ , pPlusPlus y<z)

stepWrapper : Wrapper → Wrapper
stepWrapper W =
  let module S = Step W
  in record
    { rel   = S._<step_
    ; wf    = S.wf-step
    ; trans = S.comparison-trans
    }

IterWrapper : ℕ → Wrapper
IterWrapper zero    = coreWrapper
IterWrapper (suc n) = stepWrapper (IterWrapper n)

LiftedOrder : ℕ → Rel BT _
LiftedOrder n = rel (IterWrapper n)

LiftedOrder-wf : (n : ℕ) → WellFounded (LiftedOrder n)
LiftedOrder-wf n = wf (IterWrapper n)

LiftedOrder-trans : (n : ℕ) → Transitive (LiftedOrder n)
LiftedOrder-trans n = trans (IterWrapper n)

mutual

  payload-lift
    : (n : ℕ)
    → ∀ {p q}
    → Step.PayloadOrder (IterWrapper n) p q
    → Step.PayloadOrder (IterWrapper (suc n)) p q
  payload-lift n (Step.pPsiPsi α<β)   = Step.pPsiPsi (LiftedOrder-lift n α<β)
  payload-lift n (Step.pPsiPlus α<β)  = Step.pPsiPlus (LiftedOrder-lift n α<β)
  payload-lift n (Step.pPlusPlus y<z) = Step.pPlusPlus (LiftedOrder-lift n y<z)

  LiftedOrder-lift : (n : ℕ) → LiftedOrder n ⇒ LiftedOrder (suc n)
  LiftedOrder-lift zero    x<y             = inj₁ x<y
  LiftedOrder-lift (suc n) (inj₁ x<y)      = inj₁ x<y
  LiftedOrder-lift (suc n) (inj₂ (x≈y , p)) = inj₂ (x≈y , payload-lift n p)

lift-ψα : (n : ℕ) → ∀ {ν α β} → LiftedOrder n α β → LiftedOrder (suc n) (bpsi ν α) (bpsi ν β)
lift-ψα n α<β =
  let module S = Step (IterWrapper n)
  in S.ψ-step α<β

lift-+2 : (n : ℕ) → ∀ {x y z} → LiftedOrder n y z → LiftedOrder (suc n) (bplus x y) (bplus x z)
lift-+2 n y<z =
  let module S = Step (IterWrapper n)
  in S.+2-step y<z

lift-ψ+2 : (n : ℕ) → ∀ {ν x y z} → LiftedOrder n y z → LiftedOrder (suc (suc n)) (bpsi ν (bplus x y)) (bpsi ν (bplus x z))
lift-ψ+2 n y<z = lift-ψα (suc n) (lift-+2 n y<z)

LiftedOrder-irreflexive : (n : ℕ) → ∀ {x} → ¬ (LiftedOrder n x x)
LiftedOrder-irreflexive n {x} x<x = wf⇒asym (LiftedOrder-wf n) x<x x<x

-- Exact same-binder depth, measured above the current Buchholz core.
data SurfaceDepth : ℕ → BT → BT → Set where
  surf-core : ∀ {x y} → x <ᵇ y → SurfaceDepth zero x y
  surf-ψα   : ∀ {n ν α β} → SurfaceDepth n α β → SurfaceDepth (suc n) (bpsi ν α) (bpsi ν β)
  surf-+2   : ∀ {n x y z} → SurfaceDepth n y z → SurfaceDepth (suc n) (bplus x y) (bplus x z)

surface⇒lifted : ∀ {n x y} → SurfaceDepth n x y → LiftedOrder (suc n) x y
surface⇒lifted (surf-core x<y) = LiftedOrder-lift zero x<y
surface⇒lifted {n = suc n} (surf-ψα p) = lift-ψα (suc n) (surface⇒lifted p)
surface⇒lifted {n = suc n} (surf-+2 p) = lift-+2 (suc n) (surface⇒lifted p)

SurfaceDepth-irreflexive : ∀ {n x} → ¬ (SurfaceDepth n x x)
SurfaceDepth-irreflexive {n} {x} p = LiftedOrder-irreflexive (suc n) (surface⇒lifted p)
