{-# OPTIONS --safe --without-K #-}

module Echo where

open import Level using (Level; _⊔_)
open import Function.Base using (_∘_; id)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Properties
  using (trans-assoc; trans-reflʳ; trans-symˡ; sym-cong; trans-cong; cong-∘)

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
  rewrite trans-assoc (c2 (u1 x)) {q = c1 x} {r = p} = refl

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

-- Cancellation corollary: when g is a bijection with inverse s
-- (both s-right : g ∘ s ≡ id and s-left : s ∘ g ≡ id, pointwise),
-- Echo (g ∘ f) y is equivalent to Echo f (s y). This is the
-- conjecture from composition.md, restated in the corrected form
-- (a bare section on g is not enough — you need both sides of the
-- iso to collapse the Σ-over-intermediate in the accumulation law).

cancel-iso-to :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) (s : C → B)
  (s-left : ∀ b → s (g b) ≡ b)
  {y : C} →
  Echo (g ∘ f) y → Echo f (s y)
cancel-iso-to f g s s-left (x , p) = x , trans (sym (s-left (f x))) (cong s p)

cancel-iso-from :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) (s : C → B)
  (s-right : ∀ y → g (s y) ≡ y)
  {y : C} →
  Echo f (s y) → Echo (g ∘ f) y
cancel-iso-from f g s s-right {y = y} (x , q) =
  x , trans (cong g q) (s-right y)

-- The two maps above witness that `Echo (g ∘ f) y` and `Echo f (s y)`
-- are *related* via g's section/retraction structure. The round-trips
-- below upgrade that to a full isomorphism. Under `--safe --without-K`,
-- the two pointwise laws `s-left` and `s-right` are not enough on their
-- own — a bare "both-way inverse" is weaker than an equivalence /
-- bijection in HoTT terms. We therefore parameterise each round-trip
-- by the relevant triangle-identity coherence:
--
--   * `cancel-iso-from-to` (round-trip on `Echo (g ∘ f) y`) requires
--     `triangle₁ : ∀ b → cong g (s-left b) ≡ s-right (g b)`.
--   * `cancel-iso-to-from` (round-trip on `Echo f (s y)`)   requires
--     `triangle₂ : ∀ y → cong s (s-right y) ≡ s-left (s y)`.
--
-- One triangle implies the other in HoTT (any quasi-inverse can be
-- adjusted to a half-adjoint equivalence), but the adjustment needs
-- non-trivial path algebra; we take both as explicit hypotheses to
-- keep the proofs first-order. Callers who already have an
-- `Inverse` record from `Function.Bundles` can derive the triangles
-- from that record's coherence fields.

-- Naturality of a homotopy `h : f ∼ id` along `p : x ≡ y`. The
-- single load-bearing path-algebra lemma for the cancel-iso round-trips.
hom-natural-id :
  ∀ {a} {A : Set a} (f : A → A) (h : ∀ z → f z ≡ z)
  {x y : A} (p : x ≡ y) →
  trans (cong f p) (h y) ≡ trans (h x) p
hom-natural-id f h refl = sym (trans-reflʳ (h _))

-- Round-trip on `Echo (g ∘ f) y`: `cancel-iso-from ∘ cancel-iso-to ≡ id`.
cancel-iso-from-to :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) (s : C → B)
  (s-left  : ∀ b → s (g b) ≡ b)
  (s-right : ∀ y → g (s y) ≡ y)
  (triangle₁ : ∀ b → cong g (s-left b) ≡ s-right (g b))
  {y : C} (e : Echo (g ∘ f) y) →
  cancel-iso-from f g s s-right (cancel-iso-to f g s s-left e) ≡ e
cancel-iso-from-to f g s s-left s-right triangle₁ {y = y} (x , p) =
  cong (λ q → x , q) lemma
  where
    open ≡-Reasoning
    lemma : trans (cong g (trans (sym (s-left (f x))) (cong s p))) (s-right y) ≡ p
    lemma = begin
      trans (cong g (trans (sym (s-left (f x))) (cong s p))) (s-right y)
        ≡⟨ cong (λ z → trans z (s-right y))
             (sym (trans-cong (sym (s-left (f x))))) ⟩
      trans (trans (cong g (sym (s-left (f x)))) (cong g (cong s p))) (s-right y)
        ≡⟨ cong (λ z → trans (trans z (cong g (cong s p))) (s-right y))
             (sym (sym-cong (s-left (f x)))) ⟩
      trans (trans (sym (cong g (s-left (f x)))) (cong g (cong s p))) (s-right y)
        ≡⟨ cong (λ z → trans (trans (sym z) (cong g (cong s p))) (s-right y))
             (triangle₁ (f x)) ⟩
      trans (trans (sym (s-right (g (f x)))) (cong g (cong s p))) (s-right y)
        ≡⟨ cong (λ z → trans (trans (sym (s-right (g (f x)))) z) (s-right y))
             (sym (cong-∘ p)) ⟩
      trans (trans (sym (s-right (g (f x)))) (cong (g ∘ s) p)) (s-right y)
        ≡⟨ trans-assoc (sym (s-right (g (f x)))) ⟩
      trans (sym (s-right (g (f x)))) (trans (cong (g ∘ s) p) (s-right y))
        ≡⟨ cong (trans (sym (s-right (g (f x)))))
             (hom-natural-id (g ∘ s) s-right p) ⟩
      trans (sym (s-right (g (f x)))) (trans (s-right (g (f x))) p)
        ≡⟨ sym (trans-assoc (sym (s-right (g (f x))))) ⟩
      trans (trans (sym (s-right (g (f x)))) (s-right (g (f x)))) p
        ≡⟨ cong (λ z → trans z p) (trans-symˡ (s-right (g (f x)))) ⟩
      trans refl p
        ≡⟨⟩
      p
        ∎

-- Round-trip on `Echo f (s y)`: `cancel-iso-to ∘ cancel-iso-from ≡ id`.
cancel-iso-to-from :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) (s : C → B)
  (s-left  : ∀ b → s (g b) ≡ b)
  (s-right : ∀ y → g (s y) ≡ y)
  (triangle₂ : ∀ y → cong s (s-right y) ≡ s-left (s y))
  {y : C} (e : Echo f (s y)) →
  cancel-iso-to f g s s-left (cancel-iso-from f g s s-right e) ≡ e
cancel-iso-to-from f g s s-left s-right triangle₂ {y = y} (x , q) =
  cong (λ r → x , r) lemma
  where
    open ≡-Reasoning
    lemma : trans (sym (s-left (f x))) (cong s (trans (cong g q) (s-right y))) ≡ q
    lemma = begin
      trans (sym (s-left (f x))) (cong s (trans (cong g q) (s-right y)))
        ≡⟨ cong (trans (sym (s-left (f x))))
             (sym (trans-cong (cong g q))) ⟩
      trans (sym (s-left (f x))) (trans (cong s (cong g q)) (cong s (s-right y)))
        ≡⟨ cong (λ z → trans (sym (s-left (f x))) (trans (cong s (cong g q)) z))
             (triangle₂ y) ⟩
      trans (sym (s-left (f x))) (trans (cong s (cong g q)) (s-left (s y)))
        ≡⟨ cong (λ z → trans (sym (s-left (f x))) (trans z (s-left (s y))))
             (sym (cong-∘ q)) ⟩
      trans (sym (s-left (f x))) (trans (cong (s ∘ g) q) (s-left (s y)))
        ≡⟨ cong (trans (sym (s-left (f x))))
             (hom-natural-id (s ∘ g) s-left q) ⟩
      trans (sym (s-left (f x))) (trans (s-left (f x)) q)
        ≡⟨ sym (trans-assoc (sym (s-left (f x)))) ⟩
      trans (trans (sym (s-left (f x))) (s-left (f x))) q
        ≡⟨ cong (λ z → trans z q) (trans-symˡ (s-left (f x))) ⟩
      trans refl q
        ≡⟨⟩
      q
        ∎

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

-- Pentagon Σ-associativity isomorphism. The two natural factorings of
-- `Echo (h ∘ g ∘ f) y` from the projection-pentagon lemmas above differ
-- only by Σ-associativity / unification of the intermediate base point:
--
--   outer : Σ C (λ c → Σ B (λ b → Echo f b × (g b ≡ c)) × (h c ≡ y))
--             — the "outer-first then inner" factoring, two nested splits
--   inner : Σ B (λ b → Echo f b × (h (g b) ≡ y))
--             — the "inner-first" factoring, a single split with (h ∘ g)
--
-- The forward map collapses `c` against the intermediate witness
-- `g b ≡ c`, transporting `h c ≡ y` to `h (g b) ≡ y`. The backward map
-- sets `c := g b` with `refl`, leaving the outer h-equation untouched.
-- Both round-trips reduce definitionally once the relevant `g b ≡ c`
-- has been pinned to `refl` by pattern matching, so this is a strict
-- iso (no transport coherence required) and lives comfortably inside
-- `--safe --without-K`.

Echo-comp-pent-Σ-assoc-to :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) {y : D} →
  Σ C (λ c → Σ B (λ b → Echo f b × (g b ≡ c)) × (h c ≡ y)) →
  Σ B (λ b → Echo f b × (h (g b) ≡ y))
Echo-comp-pent-Σ-assoc-to f g h (c , (b , ef , q) , p) =
  b , ef , trans (cong h q) p

Echo-comp-pent-Σ-assoc-from :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) {y : D} →
  Σ B (λ b → Echo f b × (h (g b) ≡ y)) →
  Σ C (λ c → Σ B (λ b → Echo f b × (g b ≡ c)) × (h c ≡ y))
Echo-comp-pent-Σ-assoc-from f g h (b , ef , p) =
  g b , (b , ef , refl) , p

Echo-comp-pent-Σ-assoc-from-to :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) {y : D}
  (r : Σ C (λ c → Σ B (λ b → Echo f b × (g b ≡ c)) × (h c ≡ y))) →
  Echo-comp-pent-Σ-assoc-from f g h
    (Echo-comp-pent-Σ-assoc-to f g h r) ≡ r
Echo-comp-pent-Σ-assoc-from-to f g h (c , (b , ef , refl) , p) = refl

Echo-comp-pent-Σ-assoc-to-from :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) {y : D}
  (r : Σ B (λ b → Echo f b × (h (g b) ≡ y))) →
  Echo-comp-pent-Σ-assoc-to f g h
    (Echo-comp-pent-Σ-assoc-from f g h r) ≡ r
Echo-comp-pent-Σ-assoc-to-from f g h (b , ef , p) = refl

----------------------------------------------------------------------
-- Equivalence-record packaging
--
-- The `cancel-iso-{to,from,from-to,to-from}` and
-- `Echo-comp-iso-{to,from,from-to,to-from}` quartets above each
-- pair into a stdlib `Function.Bundles._↔_` (bijection /
-- bi-invertible map). The `cancel-iso` packager takes the two
-- triangle-identity coherences as hypotheses (one per round-trip),
-- as the round-trip lemmas themselves require; the
-- `Echo-comp-iso` packager is unconditional (the round-trips
-- there are pure pattern-matching).
--
-- The `↔` record from `Function.Bundles` is the standard
-- categorical-equivalence object in stdlib v2: `to`, `from`,
-- congruences (trivial under `_≡_`), and the two strict-inverse
-- laws. Building this here gives downstream consumers a single
-- structured object instead of a quintuple of named lemmas, and
-- means the cancel-iso closes `composition.md` §4 ("Full
-- cancel-iso with round-trips") cleanly.

open import Function.Bundles using (_↔_; mk↔ₛ′)

-- Per-fiber Echo-comp iso, packaged as a ↔. The accumulation
-- iso is unconditional, so no extra hypotheses are needed.

Echo-comp-iso :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) (y : C) →
  Echo (g ∘ f) y ↔ Σ B (λ b → Echo f b × (g b ≡ y))
Echo-comp-iso f g y =
  mk↔ₛ′
    (λ e → Echo-comp-iso-to   f g {y = y} e)
    (λ r → Echo-comp-iso-from f g {y = y} r)
    (λ r → Echo-comp-iso-to-from f g r)
    (λ e → Echo-comp-iso-from-to f g e)

-- Per-fiber cancel iso, packaged as a ↔. Requires both triangle
-- identities; one triangle implies the other in HoTT but the
-- adjustment is non-trivial path algebra, so both are taken as
-- explicit hypotheses (matching `cancel-iso-from-to` and
-- `cancel-iso-to-from`).
--
-- Closes `docs/echo-types/composition.md` §4 ("Full cancel-iso
-- with round-trips") via the stdlib equivalence record.

cancel-iso :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : A → B) (g : B → C) (s : C → B)
  (s-left  : ∀ b → s (g b) ≡ b)
  (s-right : ∀ y → g (s y) ≡ y)
  (triangle₁ : ∀ b → cong g (s-left b) ≡ s-right (g b))
  (triangle₂ : ∀ y → cong s (s-right y) ≡ s-left (s y))
  (y : C) →
  Echo (g ∘ f) y ↔ Echo f (s y)
cancel-iso f g s s-left s-right triangle₁ triangle₂ y =
  mk↔ₛ′
    (λ e → cancel-iso-to   f g s s-left  {y = y} e)
    (λ e → cancel-iso-from f g s s-right {y = y} e)
    (λ e → cancel-iso-to-from f g s s-left s-right triangle₂ e)
    (λ e → cancel-iso-from-to f g s s-left s-right triangle₁ e)

-- Pentagon Σ-associativity iso, packaged as a ↔. The four
-- directional pieces (`Echo-comp-pent-Σ-assoc-{to, from, from-to,
-- to-from}`) form a strict iso under `--safe --without-K`; the
-- round-trips reduce definitionally once `g b ≡ c` has been pinned
-- to `refl`, so no extra hypotheses are needed.
--
-- Closes `docs/echo-types/composition.md` §A4 ("Pentagon
-- coherence — full Σ-associativity iso").

Echo-comp-pent-Σ-assoc :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → B) (g : B → C) (h : C → D) (y : D) →
  Σ C (λ c → Σ B (λ b → Echo f b × (g b ≡ c)) × (h c ≡ y)) ↔
  Σ B (λ b → Echo f b × (h (g b) ≡ y))
Echo-comp-pent-Σ-assoc f g h y =
  mk↔ₛ′
    (λ r → Echo-comp-pent-Σ-assoc-to      f g h {y = y} r)
    (λ r → Echo-comp-pent-Σ-assoc-from    f g h {y = y} r)
    (λ r → Echo-comp-pent-Σ-assoc-to-from f g h r)
    (λ r → Echo-comp-pent-Σ-assoc-from-to f g h r)
