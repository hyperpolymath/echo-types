{-# OPTIONS --safe --without-K #-}

-- Cost-indexed echoes over an ordered commutative-monoid cost algebra.
--
-- Axis 8 *quantitative* refinement (taxonomy.md §8, refinement 1: full
-- cost-tracking via an explicit cost algebra). Sits orthogonal to the
-- already-landed Axis 8 artefacts:
--
--   * `EchoDecidable.agda` — refinement 3, qualitative decidability layer
--   * `EchoFiberCount.agda` — quantitative fibre-count for finite domains
--   * `EchoAccess.agda`    — graded access modality (5-grade enum)
--
-- The cost-indexed echo names the *resource-budget* dimension of
-- Axis 8: not "is a witness produced?" (decidability) and not "how
-- many witnesses?" (fibre count), but "at what cost?". The cost
-- carrier is left abstract — callers supply an ordered commutative-
-- monoid-flavoured `CostAlgebra` at use sites.
--
--   EchoC cost c f y := Σ A (λ x → f x ≡ y × cost x ≤ c)
--
-- Headline lemmas:
--
--   * echo-cost-intro       -- strict echo at zero-budget when witness
--                              has zero cost (constructor analogue of
--                              `Echo.echo-intro`, refined by budget).
--   * echo-cost-relax       -- monotone in budget: c₁ ≤ c₂ ⇒ EchoC c₁ ⊑ EchoC c₂.
--   * echo-cost-forget      -- EchoC cost c f y → Echo f y; the projection
--                              down to the bare Axis-1 echo (the
--                              "shadow" obligation of every refinement).
--   * echo-cost-compose     -- additive composition: an `EchoC cost₁ c₁ f b`
--                              and `EchoC cost₂ c₂ g y` with `g b ≡ y` and
--                              a combiner `combine : A → A' → A''` with
--                              `f' (combine x₁ x₂) ≡ g (f x₁)` and a cost
--                              receipt `cost' (combine x₁ x₂) ≤ cost₁ x₁
--                              + cost₂ x₂` yield an `EchoC cost' (c₁ + c₂)
--                              f' y`. The compositional shape is
--                              first-order — no funext — exactly mirroring
--                              the additive-error shape of `EchoApprox`'s
--                              `echo-approx-compose`.
--
-- Composition shape (design call). The minimal first-order shape that
-- (a) avoids funext, (b) preserves the additive-cost story, and (c)
-- still composes across two distinct domains `A`/`A'` is to
-- parameterise by an explicit combiner that builds an `A''`-witness
-- from the two source witnesses with a controlled cost receipt and a
-- controlled image equation. This is strictly more general than
-- restricting to a single-domain endomorphic situation (the shape
-- `EchoApprox.echo-approx-compose` uses, `g : B → B`); the
-- single-domain corner falls out by taking `A := A'` and
-- `combine := proj₂`.
--
-- Parameterisation note. `EchoC` is parameterised over a
-- `CostAlgebra`, so per the CLAUDE.md "Working rules" invariant
-- (every headline pinned in `Smoke.agda` via `using`), the headline
-- lemmas are exposed top-level via `EchoCostInstance.agda`, a
-- trivial-on-⊤ instance — same recipe as `EchoApproxInstance.agda`.

module Echo.Bridges.EchoCost where

open import Level                                 using (Level; _⊔_; suc)
open import Function.Base                         using (_∘_; id)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; trans; cong)

open import Echo.Core                                  using (Echo)

----------------------------------------------------------------------
-- Cost algebra
----------------------------------------------------------------------

-- An ordered commutative-monoid-flavoured cost carrier. Just enough
-- structure to state additive composition with `zero` as a left
-- identity for the budget:
--
--   * reflexive, transitive `≤`,
--   * binary `+`,
--   * `+`-monotone on both sides simultaneously (`+-mono-≤`),
--   * left-identity `zero + c ≡ c` (the budget round-trip lever).
--
-- This is the smallest set of laws under which `echo-cost-intro` /
-- `echo-cost-relax` / `echo-cost-compose` close without funext, and
-- which the trivial-on-⊤ instance discharges by `tt` / `refl`. The
-- right-identity / associativity / commutativity laws are not needed
-- for the headlines here and are omitted on purpose (a real `ℕ`
-- instance would supply them via `Data.Nat.Properties`; they would
-- live on a separate `BalancedCostAlgebra` record if a downstream
-- proof needs them — same layering pattern as `BalancedTolerance` in
-- `EchoApprox.agda`).

record CostAlgebra ℓ : Set (suc ℓ) where
  infix 4 _≤_
  infixl 6 _+_
  field
    Cost        : Set ℓ
    zero        : Cost
    _+_         : Cost → Cost → Cost
    _≤_         : Cost → Cost → Set ℓ
    ≤-refl      : ∀ {c}             → c ≤ c
    ≤-trans     : ∀ {a b c}         → a ≤ b → b ≤ c → a ≤ c
    +-identityˡ : ∀ c               → (zero + c) ≡ c
    +-mono-≤    : ∀ {a b c d}       → a ≤ c → b ≤ d → (a + b) ≤ (c + d)

----------------------------------------------------------------------
-- Cost-indexed echo
----------------------------------------------------------------------

module Cost
  {ℓ} (K : CostAlgebra ℓ)
  where

  open CostAlgebra K

  -- `EchoC cost c f y`: a witness `x : A` whose image under `f` hits
  -- `y` exactly *and* whose ascribed cost is within budget `c`.
  --
  -- Two pieces of evidence in the second component:
  --   * `f x ≡ y`         : the bare-echo equation (Axis-1 content)
  --   * `cost x ≤ c`      : the budget receipt   (Axis-8 content)
  --
  -- The Σ-shape uses `_×_` rather than nested Σ for symmetry with
  -- `EchoApprox.EchoR`, which lets the `echo-cost-forget` projection
  -- to the bare `Echo` land by `(proj₁ , proj₁ ∘ proj₂)`.
  EchoC :
    ∀ {a b} {A : Set a} {B : Set b} →
    (cost : A → Cost) → (c : Cost) → (f : A → B) → B → Set (a ⊔ b ⊔ ℓ)
  EchoC {A = A} cost c f y =
    Σ A (λ x → (f x ≡ y) × (cost x ≤ c))

  ----------------------------------------------------------------------
  -- Headline 1: exact intro at zero-budget when the witness has zero cost.
  --
  -- The cost-indexed analogue of `Echo.echo-intro`: any `x : A` whose
  -- ascribed cost is ≤ zero (which by reflexivity holds whenever the
  -- cost *is* zero) lifts into its own fibre with zero budget. The
  -- bound proof is `≤-refl` at the cost of `x`, transported along the
  -- caller's premise `cost x ≤ zero`.
  --
  -- Two equivalent shapes:
  --   * a "you tell me the cost is ≤ zero" version (`echo-cost-intro-≤`)
  --   * a "the cost *is* zero" definitional version (`echo-cost-intro`)
  --
  -- The latter is the named headline; the former is the more general
  -- form callers reach for when they have a `cost x ≤ zero` proof in
  -- hand from elsewhere.
  ----------------------------------------------------------------------

  echo-cost-intro-≤ :
    ∀ {a b} {A : Set a} {B : Set b}
    (cost : A → Cost) (f : A → B) (x : A) →
    cost x ≤ zero →
    EchoC cost zero f (f x)
  echo-cost-intro-≤ cost f x cost-x≤0 =
    x , refl , cost-x≤0

  echo-cost-intro :
    ∀ {a b} {A : Set a} {B : Set b}
    (cost : A → Cost) (f : A → B) (x : A) →
    cost x ≡ zero →
    EchoC cost zero f (f x)
  echo-cost-intro cost f x cost-x≡0 =
    x , refl , subst (_≤ zero) (sym cost-x≡0) ≤-refl

  ----------------------------------------------------------------------
  -- Headline 2: budget is monotone — a tighter budget refines a looser
  -- one. One `≤-trans` step. The bare-echo equation `f x ≡ y` is
  -- untouched; only the receipt grows.
  ----------------------------------------------------------------------

  echo-cost-relax :
    ∀ {a b} {A : Set a} {B : Set b}
    {cost : A → Cost} {c₁ c₂ : Cost} {f : A → B} {y : B} →
    c₁ ≤ c₂ → EchoC cost c₁ f y → EchoC cost c₂ f y
  echo-cost-relax c₁≤c₂ (x , p , cost-x≤c₁) =
    x , p , ≤-trans cost-x≤c₁ c₁≤c₂

  ----------------------------------------------------------------------
  -- Headline 3: forget the cost receipt and recover the bare echo.
  --
  -- The Axis-8 → Axis-1 projection. `echo-cost-forget e := (proj₁ e ,
  -- proj₁ (proj₂ e))` — keep the A-witness and the bare-echo equation;
  -- drop the budget receipt. This is the *shadow* obligation of every
  -- Axis-8 refinement (same role as `echo-shadow-A` in `EchoApprox`):
  -- every move in the cost-indexed calculus that preserves
  -- `(x , f x ≡ y)` preserves the Axis-1 echo on the nose.
  ----------------------------------------------------------------------

  echo-cost-forget :
    ∀ {a b} {A : Set a} {B : Set b}
    {cost : A → Cost} {c : Cost} {f : A → B} {y : B} →
    EchoC cost c f y → Echo f y
  echo-cost-forget (x , p , _) = x , p

  ----------------------------------------------------------------------
  -- Headline 4: additive composition.
  --
  -- The cost-indexed analogue of `Echo-comp-iso` / `echo-approx-compose`.
  -- Form: given
  --
  --   * an EchoC at cost-budget `c₁` for `f : A → B` at intermediate `b`,
  --   * an EchoC at cost-budget `c₂` for `g : B → C` at target  `y`
  --     with `g b ≡ y`,
  --   * a target domain `A''` and a function `f' : A'' → C` taking
  --     the composite-witness shape,
  --   * a *combiner* `combine : A → A' → A''` that produces an `A''`-
  --     witness from the two source witnesses, together with two
  --     receipts:
  --       (i)  `image-eq` : `f' (combine x₁ x₂) ≡ g (f x₁)` —
  --                          the combined witness reaches the
  --                          same point in `C` as the composite,
  --       (ii) `cost-bound` : `cost' (combine x₁ x₂) ≤ cost₁ x₁ + cost₂ x₂`
  --                          — the combined cost stays inside
  --                          the additive budget,
  --
  -- produce an `EchoC cost' (c₁ + c₂) f' y`. The bound proof chains
  -- the combiner receipt through `+-mono-≤` and `≤-trans`; the
  -- image equation chains through `trans (image-eq) (cong g (proj₁
  -- (proj₂ e₁)))` and then through `proj₁ (proj₂ e₂)`.
  --
  -- Composition shape (design call). This is strictly more general
  -- than the EchoApprox-style "single-domain endomorphic g" shape: it
  -- compositionally combines two echoes whose A-witnesses may live in
  -- different types and whose `f'`-target need not equal `g ∘ f` on
  -- the nose. The natural specialisation `f' := g ∘ f` and `combine
  -- := λ x₁ _ → x₁` (drop the second witness) recovers the
  -- single-source story; we pin it as `echo-cost-compose-mono` below.
  --
  -- No funext used. The image equation is supplied by the caller (not
  -- derived from a pointwise homotopy on the carriers), and the cost
  -- bound chains through `+-mono-≤` / `≤-trans` — both first-order.
  ----------------------------------------------------------------------

  -- `cost₂` lives on `B`, not on `A'`, because the second echo
  -- `EchoC cost₂ c₂ g y` has `g : B → C` and so its A-witness is a
  -- `B`-point. The combiner takes the original `A`-witness from
  -- `e₁` together with the `B`-witness from `e₂` and produces an
  -- `A''`-witness for the composite target function `f' : A'' → C`.
  echo-cost-compose :
    ∀ {a a'' b c} {A : Set a} {A'' : Set a''} {B : Set b} {C : Set c}
    {cost₁ : A → Cost} {cost₂ : B → Cost} {cost' : A'' → Cost}
    {c₁ c₂ : Cost}
    (f  : A → B) (g  : B → C) (f' : A'' → C)
    (combine : A → B → A'') →
    ∀ {b'} {y : C}
    (e₁ : EchoC cost₁ c₁ f b')
    (e₂ : EchoC cost₂ c₂ g y) →
    g b' ≡ y →
    f' (combine (proj₁ e₁) (proj₁ e₂)) ≡ g (f (proj₁ e₁)) →
    cost' (combine (proj₁ e₁) (proj₁ e₂)) ≤
      ((cost₁ (proj₁ e₁)) + (cost₂ (proj₁ e₂))) →
    EchoC cost' (c₁ + c₂) f' y
  echo-cost-compose {cost₁ = cost₁} {cost₂ = cost₂} {cost' = cost'}
    {c₁ = c₁} {c₂ = c₂} f g f' combine {b' = b'} {y = y}
    (x₁ , fp₁ , cost₁-x≤c₁) (x₂ , gp₂ , cost₂-x≤c₂)
    gb'≡y combine-image combine-cost =
      combine x₁ x₂ , img , bnd
    where
      -- f' (combine x₁ x₂) = g (f x₁) by `combine-image`;
      -- = g b' by `cong g fp₁` (since `fp₁ : f x₁ ≡ b'`);
      -- = y by `gb'≡y`.
      img : f' (combine x₁ x₂) ≡ y
      img = trans combine-image (trans (cong g fp₁) gb'≡y)

      -- cost' (combine x₁ x₂) ≤ cost₁ x₁ + cost₂ x₂   (by combine-cost)
      -- cost₁ x₁ + cost₂ x₂ ≤ c₁ + c₂                 (by +-mono-≤)
      bnd : cost' (combine x₁ x₂) ≤ (c₁ + c₂)
      bnd = ≤-trans combine-cost (+-mono-≤ cost₁-x≤c₁ cost₂-x≤c₂)

  ----------------------------------------------------------------------
  -- Single-source specialisation of composition.
  --
  -- `echo-cost-compose-mono` is the corner of `echo-cost-compose` in
  -- which we drop the second source witness: `A'' := A`, `combine x₁
  -- _ := x₁`, and `cost' := cost₁`. The image and cost receipts then
  -- discharge to `refl` and `≤-refl` after `+-identityˡ`-style
  -- algebra in the caller's instance; we leave them as explicit
  -- hypotheses (matching the `EchoApprox` retract pattern) so that
  -- callers don't need to do `subst` gymnastics inside this module.
  --
  -- The caller-side discharge is trivial whenever `cost₂` is the
  -- constant-zero cost (a "free" outer leg `g`): then `cost₁ x₁ +
  -- cost₂ x₂ ≡ cost₁ x₁ + zero`, and a right-identity step closes
  -- it. The asymmetric "free outer leg" corner is one of the
  -- natural use sites for this shape.
  ----------------------------------------------------------------------

  echo-cost-compose-mono :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    {cost₁ : A → Cost} {cost₂ : B → Cost}
    {c₁ c₂ : Cost}
    (f : A → B) (g : B → C) →
    ∀ {b'} {y : C}
    (e₁ : EchoC cost₁ c₁ f b')
    (e₂ : EchoC cost₂ c₂ g y) →
    g b' ≡ y →
    cost₁ (proj₁ e₁) ≤ ((cost₁ (proj₁ e₁)) + (cost₂ (proj₁ e₂))) →
    EchoC cost₁ (c₁ + c₂) (g ∘ f) y
  echo-cost-compose-mono {cost₁ = cost₁} {cost₂ = cost₂}
    {c₁ = c₁} {c₂ = c₂} f g {b' = b'} {y = y}
    (x₁ , fp₁ , cost₁-x≤c₁) (x₂ , gp₂ , cost₂-x≤c₂)
    gb'≡y x₁-≤-sum =
      x₁ , img , bnd
    where
      img : g (f x₁) ≡ y
      img = trans (cong g fp₁) gb'≡y

      bnd : cost₁ x₁ ≤ (c₁ + c₂)
      bnd = ≤-trans x₁-≤-sum (+-mono-≤ cost₁-x≤c₁ cost₂-x≤c₂)

  ----------------------------------------------------------------------
  -- Forget-respects-compose (axis-1 shadow law for the composite).
  --
  -- The bare-echo projection of `echo-cost-compose-mono e₁ e₂ ...` is
  -- the bare composite echo at the A-witness of `e₁`. This is the
  -- compositional version of `echo-cost-forget` — composing in the
  -- cost-indexed calculus and then forgetting the receipt agrees
  -- with the bare-Axis-1 composite of the forgotten echoes on the
  -- A-component.
  ----------------------------------------------------------------------

  echo-cost-forget-compose-mono-A :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    {cost₁ : A → Cost} {cost₂ : B → Cost}
    {c₁ c₂ : Cost}
    (f : A → B) (g : B → C)
    {b' : B} {y : C}
    (e₁ : EchoC cost₁ c₁ f b')
    (e₂ : EchoC cost₂ c₂ g y)
    (gb'≡y : g b' ≡ y)
    (x₁-≤-sum :
       cost₁ (proj₁ e₁) ≤
         ((cost₁ (proj₁ e₁)) + (cost₂ (proj₁ e₂)))) →
    proj₁ (echo-cost-forget
             (echo-cost-compose-mono {cost₁ = cost₁} {cost₂ = cost₂}
                f g e₁ e₂ gb'≡y x₁-≤-sum))
    ≡ proj₁ (echo-cost-forget e₁)
  echo-cost-forget-compose-mono-A f g (x , _ , _) _ _ _ = refl

  ----------------------------------------------------------------------
  -- Budget-zero round-trip companion to `echo-cost-relax`.
  --
  -- `echo-cost-relax-zero`: relaxing from `zero` to `(zero + c)` is
  -- the same as relaxing to `c` (via `+-identityˡ`). The smallest
  -- statement that uses the `+-identityˡ` field of `CostAlgebra`,
  -- in the same spirit as `EchoApprox.echo-approx-comp-retract-budget`.
  ----------------------------------------------------------------------

  echo-cost-relax-zero :
    ∀ (c : Cost) → (zero + c) ≡ c
  echo-cost-relax-zero = +-identityˡ
