{-# OPTIONS --safe --without-K #-}

module Echo where

open import Level using (Level; _⊔_)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- Echo_f(y) := Σ (x : A) , (f x ≡ y)
Echo : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → B → Set (a ⊔ b)
Echo {A = A} f y = Σ A (λ x → f x ≡ y)

-- Introduction into own fiber.
echo-intro : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → Echo f (f x)
echo-intro f x = x , refl

-- Morphisms over a fixed codomain B.
MapOver :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b} →
  (f : A → B) → (f' : A' → B) → Set (a ⊔ a' ⊔ b)
MapOver {A = A} {A' = A'} f f' = Σ (A → A') (λ u → ∀ x → f' (u x) ≡ f x)

-- Action on fibers over fixed base B.
map-over :
  ∀ {a a' b} {A : Set a} {A' : Set a'} {B : Set b}
  {f : A → B} {f' : A' → B} →
  MapOver f f' → ∀ {y : B} → Echo f y → Echo f' y
map-over (u , commute) (x , p) = u x , trans (commute x) p

-- Identity law (pointwise on each fiber element).
map-over-id :
  ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {y : B} (e : Echo f y) →
  map-over (id , (λ x → refl)) e ≡ e
map-over-id (x , p) = refl

trans-assoc :
  ∀ {a} {A : Set a} {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) →
  trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl q r = refl

-- Composition law (pointwise on each fiber element).
map-over-comp :
  ∀ {a a' a'' b}
  {A : Set a} {A' : Set a'} {A'' : Set a''} {B : Set b}
  {f : A → B} {f' : A' → B} {f'' : A'' → B}
  (u1 : A → A') (c1 : ∀ x → f' (u1 x) ≡ f x)
  (u2 : A' → A'') (c2 : ∀ x → f'' (u2 x) ≡ f' x)
  {y : B} (e : Echo f y) →
  map-over {f = f} {f' = f''}
    (u2 ∘ u1 , (λ x → trans (c2 (u1 x)) (c1 x))) e
  ≡ map-over {f = f'} {f' = f''} (u2 , c2)
      (map-over {f = f} {f' = f'} (u1 , c1) e)
map-over-comp u1 c1 u2 c2 (x , p)
  rewrite trans-assoc (c2 (u1 x)) (c1 x) p = refl

-- Action along a commuting square: f' ∘ u = v ∘ f.
map-square :
  ∀ {a a' b b'}
  {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'}
  (f : A → B) (f' : A' → B') (u : A → A') (v : B → B')
  (square : ∀ x → f' (u x) ≡ v (f x)) {y : B} →
  Echo f y → Echo f' (v y)
map-square f f' u v square (x , p) = u x , trans (square x) (cong v p)

-- Composition isomorphism: the echo of g ∘ f at y is canonically
-- equivalent to a Σ over an intermediate b : B of (Echo f b × g b ≡ y).
-- This is the accumulation law from docs/echo-types/composition.md §1:
-- composition does not weaken the intensional core, it accumulates
-- witness structure. Both round-trips are definitional once the
-- refl pattern has pinned the intermediate b to f x.

Echo-comp-iso-to :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C} →
  Echo (g ∘ f) y → Σ B (λ b → Echo f b × (g b ≡ y))
Echo-comp-iso-to f g (x , p) = f x , (x , refl) , p

Echo-comp-iso-from :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C} →
  Σ B (λ b → Echo f b × (g b ≡ y)) → Echo (g ∘ f) y
Echo-comp-iso-from f g (b , (x , refl) , p) = x , p

Echo-comp-iso-from-to :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C} (e : Echo (g ∘ f) y) →
  Echo-comp-iso-from f g (Echo-comp-iso-to f g e) ≡ e
Echo-comp-iso-from-to f g (x , p) = refl

Echo-comp-iso-to-from :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) {y : C}
  (r : Σ B (λ b → Echo f b × (g b ≡ y))) →
  Echo-comp-iso-to f g (Echo-comp-iso-from f g r) ≡ r
Echo-comp-iso-to-from f g (b , (x , refl) , p) = refl

-- Pentagon coherence for three-fold composition. Given
-- f : A → B, g : B → C, h : C → D, the echo of (h ∘ g ∘ f)
-- admits two natural factorings via `Echo-comp-iso-to`:
--
--   outer-first : split at outer boundary (h) then at inner (g)
--       Echo (h ∘ (g ∘ f)) y
--     → Σ C (λ c → Echo (g ∘ f) c × (h c ≡ y))         [iso on (g∘f, h)]
--     → Σ C (λ c → Σ B (λ b → Echo f b × (g b ≡ c)) × (h c ≡ y))
--
--   inner-first : split at the inner boundary ((h∘g) as outer, f as inner)
--       Echo ((h ∘ g) ∘ f) y
--     → Σ B (λ b → Echo f b × ((h ∘ g) b ≡ y))         [iso on (f, h∘g)]
--
-- Both factorings project to the same `f x` at the B-component and
-- the same `x , refl` at the Echo-f witness. This is the minimal
-- pentagon-style coherence: the two natural applications of
-- Echo-comp-iso agree on the A-origin of the composite echo.

Echo-comp-iso-pent-B :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) {y : D}
  (e : Echo (h ∘ g ∘ f) y) →
  proj₁ (Echo-comp-iso-to f g
           (proj₁ (proj₂ (Echo-comp-iso-to (g ∘ f) h e))))
  ≡ proj₁ (Echo-comp-iso-to f (h ∘ g) e)
Echo-comp-iso-pent-B f g h (x , p) = refl

-- Stronger statement: same `(x , refl) : Echo f (f x)` on the
-- Echo-f component too.
Echo-comp-iso-pent-echo :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) {y : D}
  (e : Echo (h ∘ g ∘ f) y) →
  proj₁ (proj₂ (Echo-comp-iso-to f g
                  (proj₁ (proj₂ (Echo-comp-iso-to (g ∘ f) h e)))))
  ≡ proj₁ (proj₂ (Echo-comp-iso-to f (h ∘ g) e))
Echo-comp-iso-pent-echo f g h (x , p) = refl
