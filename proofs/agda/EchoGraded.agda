{-# OPTIONS --safe --without-K #-}

module EchoGraded where

open import Echo
open import EchoCharacteristic using (collapse)
open import EchoResidue using (EchoR; TrivialCert; collapse-to-residue)

open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

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

-- Each constructor of `_≤g_` is pinned by both its source and target
-- grades, so the order is propositional: any two proofs of `g1 ≤g g2`
-- are equal. Pattern-matches go through under `--without-K` because
-- each (g1, g2) pair has exactly one inhabitant of `_≤g_`.
≤g-prop : ∀ {g1 g2} (p p' : g1 ≤g g2) → p ≡ p'
≤g-prop keep≤keep keep≤keep = refl
≤g-prop keep≤residue keep≤residue = refl
≤g-prop keep≤forget keep≤forget = refl
≤g-prop residue≤residue residue≤residue = refl
≤g-prop residue≤forget residue≤forget = refl
≤g-prop forget≤forget forget≤forget = refl

-- Join is an upper bound on its left summand.
≤g-⊔g-left : ∀ g1 g2 → g1 ≤g (g1 ⊔g g2)
≤g-⊔g-left keep keep = keep≤keep
≤g-⊔g-left keep residue = keep≤residue
≤g-⊔g-left keep forget = keep≤forget
≤g-⊔g-left residue keep = residue≤residue
≤g-⊔g-left residue residue = residue≤residue
≤g-⊔g-left residue forget = residue≤forget
≤g-⊔g-left forget keep = forget≤forget
≤g-⊔g-left forget residue = forget≤forget
≤g-⊔g-left forget forget = forget≤forget

-- Join is an upper bound on its right summand.
≤g-⊔g-right : ∀ g1 g2 → g2 ≤g (g1 ⊔g g2)
≤g-⊔g-right keep keep = keep≤keep
≤g-⊔g-right keep residue = residue≤residue
≤g-⊔g-right keep forget = forget≤forget
≤g-⊔g-right residue keep = keep≤residue
≤g-⊔g-right residue residue = residue≤residue
≤g-⊔g-right residue forget = forget≤forget
≤g-⊔g-right forget keep = keep≤forget
≤g-⊔g-right forget residue = residue≤forget
≤g-⊔g-right forget forget = forget≤forget

-- Universal property of join: anything dominated by both g1 and g2
-- is dominated by their join. Together with the two upper-bound
-- lemmas this exhibits `_⊔g_` as the categorical join in `_≤g_`.
≤g-⊔g-univ :
  ∀ {g1 g2 g} → g1 ≤g g → g2 ≤g g → (g1 ⊔g g2) ≤g g
≤g-⊔g-univ keep≤keep p2 = p2
≤g-⊔g-univ keep≤residue p2 = p2
≤g-⊔g-univ keep≤forget p2 = p2
≤g-⊔g-univ residue≤residue keep≤residue = residue≤residue
≤g-⊔g-univ residue≤residue residue≤residue = residue≤residue
≤g-⊔g-univ residue≤forget keep≤forget = residue≤forget
≤g-⊔g-univ residue≤forget residue≤forget = residue≤forget
≤g-⊔g-univ residue≤forget forget≤forget = forget≤forget
≤g-⊔g-univ forget≤forget keep≤forget = forget≤forget
≤g-⊔g-univ forget≤forget residue≤forget = forget≤forget
≤g-⊔g-univ forget≤forget forget≤forget = forget≤forget

-- Per-decoration composition. The grade decoration commutes with
-- composition: any factoring of a transition `g1 ≤g g3` through an
-- intermediate grade `g2` yields the same degraded echo, regardless of
-- which intermediate is chosen, and is moreover indistinguishable from
-- the direct degrade. This is the per-decoration analogue of pentagon
-- coherence — different paths through the decoration order collapse.
--
-- The proof is a corollary of `degrade-comp` (associativity along the
-- chosen factoring) and `≤g-prop` (any two paths through `_≤g_` agree),
-- so the per-decoration story rests cleanly on those two ingredients.
degrade-compose :
  ∀ {g1 g2 g3}
  (p12 : g1 ≤g g2) (p23 : g2 ≤g g3) (p13 : g1 ≤g g3)
  (e : GEcho g1) →
  degrade p23 (degrade p12 e) ≡ degrade p13 e
degrade-compose p12 p23 p13 e
  rewrite ≤g-prop p13 (≤g-trans p12 p23) = degrade-comp p12 p23 e

-- Join-action specialisation: degrading directly to a common upper
-- bound `g` agrees with degrading first to the join `g1 ⊔g g2` and
-- then onward via the universal arrow. This is the per-decoration
-- composition law restated through the join structure.
degrade-via-join :
  ∀ {g1 g2 g}
  (p1 : g1 ≤g g) (p2 : g2 ≤g g) (e : GEcho g1) →
  degrade p1 e
  ≡ degrade (≤g-⊔g-univ p1 p2) (degrade (≤g-⊔g-left g1 g2) e)
degrade-via-join {g1} {g2} p1 p2 e =
  sym (degrade-compose (≤g-⊔g-left g1 g2) (≤g-⊔g-univ p1 p2) p1 e)
