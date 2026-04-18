{-# OPTIONS --safe --without-K #-}

module EchoGraded where

open import Echo
open import EchoCharacteristic using (collapse)
open import EchoResidue using (EchoR; TrivialCert; collapse-to-residue)

open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Grade : Set where
  keep : Grade
  residue : Grade
  forget : Grade

_⊔g_ : Grade → Grade → Grade
keep ⊔g g = g
residue ⊔g keep = residue
residue ⊔g residue = residue
residue ⊔g forget = forget
forget ⊔g _ = forget

⊔g-assoc : ∀ g1 g2 g3 → (g1 ⊔g g2) ⊔g g3 ≡ g1 ⊔g (g2 ⊔g g3)
⊔g-assoc keep g2 g3 = refl
⊔g-assoc residue keep g3 = refl
⊔g-assoc residue residue keep = refl
⊔g-assoc residue residue residue = refl
⊔g-assoc residue residue forget = refl
⊔g-assoc residue forget g3 = refl
⊔g-assoc forget g2 g3 = refl

data _≤g_ : Grade → Grade → Set where
  keep≤keep : keep ≤g keep
  keep≤residue : keep ≤g residue
  keep≤forget : keep ≤g forget
  residue≤residue : residue ≤g residue
  residue≤forget : residue ≤g forget
  forget≤forget : forget ≤g forget

≤g-trans : ∀ {g1 g2 g3} → g1 ≤g g2 → g2 ≤g g3 → g1 ≤g g3
≤g-trans keep≤keep p23 = p23
≤g-trans keep≤residue residue≤residue = keep≤residue
≤g-trans keep≤residue residue≤forget = keep≤forget
≤g-trans keep≤forget forget≤forget = keep≤forget
≤g-trans residue≤residue residue≤residue = residue≤residue
≤g-trans residue≤residue residue≤forget = residue≤forget
≤g-trans residue≤forget forget≤forget = residue≤forget
≤g-trans forget≤forget forget≤forget = forget≤forget

GEcho : Grade → Set
GEcho keep = Echo collapse tt
GEcho residue = EchoR ⊤ TrivialCert tt
GEcho forget = ⊤

degrade : ∀ {g1 g2} → g1 ≤g g2 → GEcho g1 → GEcho g2
degrade keep≤keep e = e
degrade keep≤residue e = collapse-to-residue e
degrade keep≤forget _ = tt
degrade residue≤residue e = e
degrade residue≤forget _ = tt
degrade forget≤forget e = e

degrade-comp :
  ∀ {g1 g2 g3}
  (p12 : g1 ≤g g2)
  (p23 : g2 ≤g g3)
  (e : GEcho g1) →
  degrade p23 (degrade p12 e) ≡ degrade (≤g-trans p12 p23) e
degrade-comp keep≤keep p23 e = refl
degrade-comp keep≤residue residue≤residue e = refl
degrade-comp keep≤residue residue≤forget e = refl
degrade-comp keep≤forget forget≤forget e = refl
degrade-comp residue≤residue residue≤residue e = refl
degrade-comp residue≤residue residue≤forget e = refl
degrade-comp residue≤forget forget≤forget e = refl
degrade-comp forget≤forget forget≤forget e = refl
