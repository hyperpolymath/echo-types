{-# OPTIONS --safe --without-K #-}

-- Gate F3 phase 1 — the abstraction layer for the
-- monoid-graded comonad introduced in `EchoGradedComonadF1.agda`.
--
-- `GradedComonadStructure` packages: a grade monoid `(G, 1G, _·G_)`
-- with its three laws; a graded carrier `D : G → Set → Set` with
-- functorial action `mapD` and its two laws; counit `ε` at the unit
-- grade; nested comultiplication `δ : D (g ·G h) A → D g (D h A)`;
-- and the three graded-comonad laws (`gc-counit-l`, `gc-counit-r`,
-- `gc-coassoc`) stated against the monoid's propositional identities
-- via `subst` along `·G-identityʳ` / `·G-identityˡ` / `·G-assoc`.
--
-- F3 guardrail (earn-back-plan.adoc §F3): the record carries no
-- field equivalent to the retracted `⊑-prop` from `EchoGraded`. The
-- abstraction is structural and equational only — no order, no
-- propositionality-of-the-grade-relation hypothesis, nothing that
-- bakes in a single load-bearing thinness assumption. Inspection:
-- the field list below is exactly the structure, the monoid laws,
-- and the comonad laws — anything more would be over-claiming.
--
-- This module on its own does NOT pass F3; F3 passes when at least
-- two non-isomorphic-grade-monoid instances satisfy this record.
-- Instance 1 = `EchoGradedComonadInstance1.agda` (the F1
-- iterated-residue construction at `(ℕ, +, 0)`). Instance 2 (at e.g.
-- the free monoid `(List X, ++, [])` over a non-trivial `X`) is
-- phase 2, separate follow-up.

module Echo.Bridges.EchoGradedComonadInterface where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

----------------------------------------------------------------------
-- The interface record.
--
-- Universe-polymorphic over the grade type `G`. The carrier `D` is
-- `Set`-valued (matching F1) to keep the record proof-irrelevant
-- about universe choices for the wrapped types.

record GradedComonadStructure : Set₁ where
  field
    --------------------------------------------------------------
    -- Grade monoid.
    --------------------------------------------------------------
    G       : Set
    1G      : G
    _·G_    : G → G → G

    ·G-identityˡ : ∀ g → 1G ·G g ≡ g
    ·G-identityʳ : ∀ g → g ·G 1G ≡ g
    ·G-assoc     : ∀ g h k → (g ·G h) ·G k ≡ g ·G (h ·G k)

    --------------------------------------------------------------
    -- Graded carrier + functorial action.
    --------------------------------------------------------------
    D       : G → Set → Set
    mapD    : ∀ g {A B} → (A → B) → D g A → D g B

    mapD-id : ∀ g {A} (x : D g A) → mapD g (λ a → a) x ≡ x
    mapD-∘  : ∀ g {A B C} (f : B → C) (h : A → B) (x : D g A) →
              mapD g (λ a → f (h a)) x ≡ mapD g f (mapD g h x)

    --------------------------------------------------------------
    -- Counit (at the unit grade) and NESTED comultiplication.
    --------------------------------------------------------------
    ε       : ∀ {A} → D 1G A → A
    δ       : ∀ g h {A} → D (g ·G h) A → D g (D h A)

    --------------------------------------------------------------
    -- The three graded-comonad laws.
    --
    -- Stated against the monoid's PROPOSITIONAL identities via
    -- `subst` along the corresponding equation. For the ℕ instance
    -- this reduces (the equations are refl) and the substs vanish;
    -- for an arbitrary monoid (e.g. List concatenation), the
    -- propositional form is what is provable in general.
    --------------------------------------------------------------

    -- counit-right: extracting at the unit grade after δ at (1G, g)
    -- is the identity reindexing, modulo the propositional witness
    -- that `1G ·G g ≡ g`.
    gc-counit-r :
      ∀ g {A} (x : D (1G ·G g) A) →
      ε (δ 1G g x) ≡ subst (λ k → D k A) (·G-identityˡ g) x

    -- counit-left: mapping the counit into the inner factor after
    -- δ at (g, 1G) recovers the original observation, modulo the
    -- propositional witness that `g ·G 1G ≡ g`.
    gc-counit-l :
      ∀ g {A} (x : D (g ·G 1G) A) →
      mapD g ε (δ g 1G x) ≡ subst (λ k → D k A) (·G-identityʳ g) x

    -- coassociativity: the two ways of splitting a triple budget
    -- agree, modulo the propositional witness that
    -- `(g ·G h) ·G k ≡ g ·G (h ·G k)`.
    gc-coassoc :
      ∀ g h k {A} (x : D ((g ·G h) ·G k) A) →
      δ g h (δ (g ·G h) k x)
      ≡ mapD g (δ h k)
          (δ g (h ·G k) (subst (λ j → D j A) (·G-assoc g h k) x))
