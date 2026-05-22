{-# OPTIONS --safe --without-K #-}

-- ε-indexed approximate echoes over a (pseudo-)metric codomain.
--
-- Axis-2 first artifact (`docs/echo-types/taxonomy.md` §2):
--
--   EchoR ε f y := Σ A (λ x → dist (f x) y ≤ ε)
--
-- where `dist` is a pseudo-metric on the codomain `B` and `ε` lives
-- in an ordered tolerance monoid. The exact echo `Echo f y = Σ A (λ x →
-- f x ≡ y)` lifts into `EchoR zero f y` via reflexivity of `dist`.
--
-- Headline lemmas:
--
--   * echo-approx-intro          -- exact own-fibre match is zero-tolerance
--   * echo-strict→approx         -- general strict ⇒ zero-tolerance (any y)
--   * echo-approx-relax          -- ε is monotone: ε₁ ≤ ε₂ ⇒ EchoR ε₁ ⊑ EchoR ε₂
--   * echo-approx-compose        -- non-expansive composition with additive
--                                   error, realising the taxonomy §2 conjecture
--   * echo-approx-comp-sound     -- repackages compose into the retract RHS-Σ
--                                   shape from `composition.md` §Q3 (§5 of the
--                                   axis-2 design note)
--   * echo-approx-comp-retract-to  -- canonical-split LHS → RHS section:
--                                     picks b := f x, ε₁ := zero, ε₂ := ε
--   * echo-approx-comp-retract-A   -- A-component round-trip (sound ∘ retract-to)
--                                     preserves the A-witness up to `refl`,
--                                     witnessing the retraction direction
--                                     definitionally
--   * BalancedTolerance              -- Tolerance with `+`-identityˡ/ʳ; the
--                                     layered record (option (b) of the
--                                     post-#74 design call) that unlocks the
--                                     B-component + budget round-trips
--   * echo-approx-comp-retract-B     -- B-component pin: the canonical-split
--                                     section picks `b := f x` definitionally
--                                     (refl; no `BalancedTolerance` needed —
--                                     pinned for symmetry with -A and the
--                                     round-trip suite)
--   * echo-approx-comp-retract-budget -- budget round-trip: under
--                                     `BalancedTolerance`, the tolerance
--                                     after `sound ∘ retract-to` is `zero + ε`
--                                     which equals the original `ε` on the nose
--   * echo-approx-comp-retract-from-to -- the budget-aligned A-component
--                                     round-trip: `proj₁ (subst _ (+-identityˡ ε)
--                                     (sound (retract-to e))) ≡ proj₁ e`;
--                                     the closest the approximate retract gets
--                                     to a strict `from-to` round-trip without
--                                     `≤`-propositionality on the bound
--   * Separated                    -- separation predicate on a pseudo-metric:
--                                     `dist b₁ b₂ ≤ zero → b₁ ≡ b₂`
--   * echo-approx-zero-collapses-strict -- §7 #7: under separation, an
--                                          ε≡zero approximate echo IS a
--                                          strict echo
--   * echo-shadow-A                -- §7 #8 axis-1 shadow: the underlying
--                                     A-witness of an approximate echo;
--                                     `echo-strict→approx` agrees with the
--                                     strict A-witness on the nose
--   * echo-shadow-iso-to / -from   -- §7 #8 trivial repackaging of `EchoR`
--                                     as an existential `Σ A (λ x → dist
--                                     (f x) y ≤ ε)` (definitional both ways)
--   * echo-strict→approx-shadow-A  -- the A-component of `echo-strict→approx`
--                                     equals the strict A-component (refl)
--
-- The non-expansiveness side condition on the outer leg is the
-- minimal hypothesis under which tolerances accumulate additively;
-- without it the conjecture has no general proof (an amplifying
-- second leg can blow ε₁ up arbitrarily on the way through).
--
-- Composition-track context (§5 of the axis-2 design note,
-- `/tmp/echo-types-exploration/axis2-approximate.md`). The approximate
-- analogue of `Echo-comp-iso` is a *retraction*, not a strict
-- isomorphism: the RHS Σ-shape admits multiple splits of the ε
-- budget and the chosen intermediate `b` is not pinned by the input.
-- This module ships soundness (#6), the canonical-split forward
-- section, the A-component round-trip witness, and (post-PR-#74) the
-- B-component pin + budget round-trip + budget-aligned A-component
-- round-trip via `BalancedTolerance` (option (b) of the design call:
-- a layered record on top of `Tolerance`, NOT a mutation of the base
-- interface — mirrors `Separated`/`PseudoMetric`). §7 obligations 7
-- (separated zero-collapse) and 8 (axis-1 shadow agreement) are
-- landed below. Rung D (Lipschitz `L_g ≠ 1`) is deferred — it requires
-- multiplication on `Tolerance`, another interface call.
--
-- The full LHS-element round-trip equality `sound (retract-to e) ≡ e`
-- (with the budget transported via `+-identityˡ`) is NOT discharged
-- here: it would require propositionality of the order `_≤_` on the
-- inner bound, which `Tolerance` deliberately does not assert.
-- `echo-approx-comp-retract-from-to` captures the strongest
-- A-component statement available without that extra hypothesis.

module EchoApprox where

open import Level                                 using (Level; _⊔_; suc)
open import Function.Base                         using (_∘_; id)
open import Data.Product.Base                     using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Echo                                  using (Echo)

----------------------------------------------------------------------
-- Tolerance carrier and pseudo-metric structure
----------------------------------------------------------------------

-- A tolerance carrier is an ordered commutative-monoid-flavoured type
-- with just enough structure to state additive composition:
-- transitive `≤`, reflexivity at every point, and a binary `+` that
-- is monotone on each side.

record Tolerance ℓ : Set (suc ℓ) where
  infix 4 _≤_
  infixl 6 _+_
  field
    Tol      : Set ℓ
    zero     : Tol
    _+_      : Tol → Tol → Tol
    _≤_      : Tol → Tol → Set ℓ
    ≤-refl   : ∀ {ε}             → ε ≤ ε
    ≤-trans  : ∀ {ε₁ ε₂ ε₃}      → ε₁ ≤ ε₂ → ε₂ ≤ ε₃ → ε₁ ≤ ε₃
    +-mono-≤ : ∀ {a b c d}       → a ≤ b → c ≤ d → (a + c) ≤ (b + d)

-- A pseudo-metric on `B` valued in a tolerance carrier `T`. Self-distance
-- is zero (definitionally) and the triangle inequality holds. We do not
-- demand symmetry or separation here; both can be added later if needed.

record PseudoMetric {b ℓ} (B : Set b) (T : Tolerance ℓ) : Set (b ⊔ ℓ) where
  open Tolerance T
  field
    dist      : B → B → Tol
    dist-self : ∀ y         → dist y y ≡ zero
    dist-tri  : ∀ b₁ b₂ b₃  → dist b₁ b₃ ≤ (dist b₁ b₂ + dist b₂ b₃)

----------------------------------------------------------------------
-- Balanced tolerance: a `Tolerance` that has additive identities.
--
-- Layered on `Tolerance` exactly as `Separated` is layered on
-- `PseudoMetric` — an *extra* predicate that callers opt into when
-- their tolerance carrier admits `zero` as a two-sided identity for
-- `+`, without forcing every `Tolerance` instance to carry the laws.
--
-- The base `Tolerance` interface deliberately stays minimal (transitive
-- `≤`, reflexivity, monotone `+`) so that lop-sided / fold-mode
-- tolerance carriers can still be instances. `BalancedTolerance`
-- captures the balanced-monoid corner of the design space where
-- `zero + ε ≡ ε` and `ε + zero ≡ ε` hold — exactly the structure
-- needed to state the full LHS→RHS→LHS round-trip of the
-- composition retract (the A-component already round-trips without
-- it; see `echo-approx-comp-retract-A`).
--
-- Design call (option (b) of the post-#74 PR-body decision): a
-- separate record on top of `Tolerance`, NOT a field of the base
-- record. Keeps the base interface untouched, mirrors the
-- `Separated`/`PseudoMetric` pattern, and lets every retract lemma
-- take an explicit `BalancedTolerance` hypothesis at the call site.
----------------------------------------------------------------------

record BalancedTolerance {ℓ} (T : Tolerance ℓ) : Set ℓ where
  open Tolerance T
  field
    +-identityˡ : ∀ ε → zero + ε ≡ ε
    +-identityʳ : ∀ ε → ε + zero ≡ ε

----------------------------------------------------------------------
-- Approximate echo
----------------------------------------------------------------------

module Approx
  {a b ℓ} {A : Set a} {B : Set b} {T : Tolerance ℓ}
  (M : PseudoMetric B T)
  where

  open Tolerance    T
  open PseudoMetric M

  -- EchoR ε f y: a witness x : A whose image f x lies within ε of y.
  EchoR : Tol → (A → B) → B → Set (a ⊔ ℓ)
  EchoR ε f y = Σ A (λ x → dist (f x) y ≤ ε)

  ----------------------------------------------------------------------
  -- Headline 1: exact match ⇒ zero-tolerance approximate match.
  --
  -- Lifts the constructor of `Echo` (`x , refl`) into the metric setting
  -- with no tolerance budget consumed. The proof rewrites `dist (f x)
  -- (f x)` to `zero` via `dist-self` and then uses `≤-refl` at zero.
  ----------------------------------------------------------------------

  echo-approx-intro : (f : A → B) (x : A) → EchoR zero f (f x)
  echo-approx-intro f x =
    x , subst (_≤ zero) (sym (dist-self (f x))) ≤-refl

  ----------------------------------------------------------------------
  -- Headline 1ʹ: general strict ⇒ zero-tolerance approximate.
  --
  -- Realises §7 obligation 2 of the axis-2 design note: every strict
  -- echo `Echo f y` lifts to a zero-tolerance approximate echo
  -- `EchoR zero f y` (any y, not just own-fibre points). When `y ≡ f x`
  -- with `p ≡ refl` this collapses to `echo-approx-intro`; otherwise
  -- the codomain equation `p : f x ≡ y` is used to transport the
  -- self-distance bound from `(f x, f x)` to `(f x, y)`.
  --
  -- This generalises `echo-approx-intro` from own-fibre points
  -- `(f x)` to arbitrary `y` reached via a strict echo. The cost of
  -- the generalisation is one extra `subst` along `p`.
  ----------------------------------------------------------------------

  echo-strict→approx :
    ∀ {f : A → B} {y : B} → Echo f y → EchoR zero f y
  echo-strict→approx {f = f} (x , p) =
    x , subst (λ z → dist (f x) z ≤ zero)
              p
              (subst (_≤ zero) (sym (dist-self (f x))) ≤-refl)

  ----------------------------------------------------------------------
  -- Headline 2: tolerance is monotone in `ε`. A tighter approximation
  -- is also a looser one. The proof is one transitivity step.
  ----------------------------------------------------------------------

  echo-approx-relax :
    ∀ {ε₁ ε₂ : Tol} {f : A → B} {y : B} →
    ε₁ ≤ ε₂ → EchoR ε₁ f y → EchoR ε₂ f y
  echo-approx-relax ε₁≤ε₂ (x , dfx≤ε₁) = x , ≤-trans dfx≤ε₁ ε₁≤ε₂

  ----------------------------------------------------------------------
  -- Headline 3: additive composition under non-expansiveness.
  --
  -- Realises the taxonomy §2 conjecture
  --   "ε₁-echo(f) + ε₂-echo(g) ⊑ (ε₁ + ε₂)-echo(g ∘ f)".
  --
  -- Form: an ε₁-echo of `f` at some intermediate `b`, plus a bound
  -- `dist (g b) y ≤ ε₂`, plus non-expansiveness of `g`, yields an
  -- (ε₁ + ε₂)-echo of `g ∘ f` at `y`.
  --
  -- Outer leg `g` is endomorphic (`B → B`) so that we stay inside the
  -- single supplied metric. A two-metric version is straightforward
  -- but adds bureaucracy without changing the argument.
  ----------------------------------------------------------------------

  NonExpansive : (B → B) → Set (b ⊔ ℓ)
  NonExpansive g = ∀ b₁ b₂ → dist (g b₁) (g b₂) ≤ dist b₁ b₂

  echo-approx-compose :
    ∀ {ε₁ ε₂ : Tol}
    (f : A → B) (g : B → B) →
    NonExpansive g →
    ∀ {b y : B} →
    EchoR ε₁ f b →
    dist (g b) y ≤ ε₂ →
    EchoR (ε₁ + ε₂) (g ∘ f) y
  echo-approx-compose {ε₁} {ε₂} f g g-nonexp {b} {y} (x , dfx≤ε₁) dgby≤ε₂ =
    x , bound
    where
    -- triangle: dist (g (f x)) y ≤ dist (g (f x)) (g b) + dist (g b) y
    leg : dist (g (f x)) y ≤ (dist (g (f x)) (g b) + dist (g b) y)
    leg = dist-tri (g (f x)) (g b) y

    -- non-expansiveness contracts the f-side residue, additive monotonicity
    -- carries it through the triangle bound.
    contract : (dist (g (f x)) (g b) + dist (g b) y) ≤ (ε₁ + ε₂)
    contract = +-mono-≤ (≤-trans (g-nonexp (f x) b) dfx≤ε₁) dgby≤ε₂

    bound : dist (g (f x)) y ≤ (ε₁ + ε₂)
    bound = ≤-trans leg contract

  ----------------------------------------------------------------------
  -- Retraction-shaped composition (composition.md §Q3 / design-note §5).
  --
  -- The approximate analogue of `Echo-comp-iso` is *retract-shaped*:
  --
  --   LHS  := EchoR ε (g ∘ f) y
  --   RHS  := Σ B (λ b → EchoR ε₁ f b × dist (g b) y ≤ ε₂)
  --
  -- with the budget split `ε = ε₁ + ε₂`. The RHS admits multiple
  -- splits of the budget and the chosen intermediate `b` is not
  -- pinned by the input, so a full iso fails by design. What does
  -- hold is a retraction: a forward section that picks a canonical
  -- representative on the RHS and a backward map (`echo-approx-comp-sound`,
  -- a thin repackaging of `echo-approx-compose`) that round-trips
  -- the A-witness definitionally.
  --
  -- This block lands: soundness (#6), the canonical-split forward
  -- section, the A-component round-trip, the B-component pin, the
  -- budget round-trip (via `BalancedTolerance`), and a budget-aligned
  -- A-component round-trip. The base `Tolerance` interface stays
  -- untouched; `+`-identity laws live on a separate `BalancedTolerance`
  -- record, taken as an explicit hypothesis at the call sites that
  -- need them.
  ----------------------------------------------------------------------

  -- §7 obligation 6: sound RHS-to-LHS direction.
  -- Unpacks the existential and calls `echo-approx-compose`.
  echo-approx-comp-sound :
    ∀ {ε₁ ε₂ : Tol}
    (f : A → B) (g : B → B) →
    NonExpansive g →
    ∀ {y : B} →
    Σ B (λ b → EchoR ε₁ f b × dist (g b) y ≤ ε₂) →
    EchoR (ε₁ + ε₂) (g ∘ f) y
  echo-approx-comp-sound f g g-nonexp (b , ef , dgby≤ε₂) =
    echo-approx-compose f g g-nonexp {b = b} ef dgby≤ε₂

  -- Canonical-split LHS-to-RHS section of the retract.
  --
  -- Given an `EchoR ε (g ∘ f) y` witness `(x , p : dist (g (f x)) y ≤ ε)`,
  -- produce the RHS Σ-shape at the canonical split `(ε₁, ε₂) := (zero, ε)`:
  --
  --   * intermediate `b := f x` (the canonical lift),
  --   * inner echo `EchoR zero f (f x)` via `echo-approx-intro`,
  --   * outer bound is just the original `p`.
  --
  -- This is the "section" half of the retract: a one-sided splitting
  -- of the §Q3 conjecture that always exists, with no extra hypothesis
  -- beyond what `EchoR ε (g ∘ f) y` already supplies. The "wrong"
  -- intermediates are not enumerable, which is precisely why the
  -- approximate analogue is a retract and not a full iso.
  echo-approx-comp-retract-to :
    ∀ {ε : Tol} (f : A → B) (g : B → B) {y : B} →
    EchoR ε (g ∘ f) y →
    Σ B (λ b → EchoR zero f b × dist (g b) y ≤ ε)
  echo-approx-comp-retract-to f g (x , dgfx≤ε) =
    f x , echo-approx-intro f x , dgfx≤ε

  -- A-component round-trip. Starting from an `EchoR ε (g ∘ f) y`,
  -- pushing through the canonical-split section then through
  -- soundness lands back on the *same A-witness `x`* (the tolerance
  -- budget weakens from `ε` to `zero + ε`, which is why this is a
  -- retraction in the A-component rather than a full equality of
  -- echoes). The proof is `refl` — the A-component is preserved
  -- definitionally because every step of the round-trip keeps
  -- `proj₁` pinned to the original `x`.
  --
  -- This pins the "retract direction holds definitionally" promise
  -- of the design note: the witness-on-A round-trips on the nose,
  -- even though the tolerance and intermediate-B components do not.
  echo-approx-comp-retract-A :
    ∀ {ε : Tol} (f : A → B) (g : B → B) (g-nonexp : NonExpansive g)
    {y : B} (e : EchoR ε (g ∘ f) y) →
    proj₁ (echo-approx-comp-sound f g g-nonexp
            (echo-approx-comp-retract-to f g e))
    ≡ proj₁ e
  echo-approx-comp-retract-A f g g-nonexp (x , _) = refl

  ----------------------------------------------------------------------
  -- B-component pin (post-PR-#74 Rung C, axis-2 design-note §7
  -- B-component obligation).
  --
  -- The canonical-split section `echo-approx-comp-retract-to` picks
  -- the intermediate `b := f x` definitionally — for every `EchoR ε
  -- (g ∘ f) y` witness `(x , _)`, the B-component of the resulting
  -- RHS-Σ shape is `f x = f (proj₁ e)`. The proof is `refl`; the
  -- B-witness round-trips on the nose through the section step,
  -- without any `BalancedTolerance` machinery. This pin sits in the
  -- round-trip suite for symmetry with `echo-approx-comp-retract-A`
  -- and to make the canonical-split discipline auditable in
  -- `Smoke.agda`.
  --
  -- Note. There is no "full" B-component round-trip — going LHS→RHS
  -- via the canonical split always lands on `b := f x` regardless of
  -- the original input, and the LHS has no B-component to compare
  -- to. The genuine RHS→LHS→RHS round-trip on B fails by design
  -- (the chosen `b` is forgotten — that is precisely why the
  -- approximate analogue is a retract, not an iso; design-note §5).
  ----------------------------------------------------------------------

  echo-approx-comp-retract-B :
    ∀ {ε : Tol} (f : A → B) (g : B → B)
    {y : B} (e : EchoR ε (g ∘ f) y) →
    proj₁ (echo-approx-comp-retract-to f g e) ≡ f (proj₁ e)
  echo-approx-comp-retract-B f g (x , _) = refl

  ----------------------------------------------------------------------
  -- Budget round-trip (post-PR-#74 Rung C, axis-2 design-note §7
  -- budget obligation).
  --
  -- The composition `sound ∘ retract-to` weakens the tolerance budget
  -- from `ε` (the input) to `zero + ε` (the output, because the
  -- canonical-split section uses `ε₁ := zero` and `ε₂ := ε` and
  -- `echo-approx-compose` reports the sum). Under
  -- `BalancedTolerance`, `zero + ε ≡ ε` holds on the nose, so the
  -- budget round-trips definitionally up to that identity law.
  --
  -- This is the smallest statement that uses the new
  -- `BalancedTolerance` hypothesis: the bare identity law, expressed
  -- in the same shape `(zero + ε) ≡ ε` that the
  -- `echo-approx-comp-retract-from-to` `subst` consumes below.
  ----------------------------------------------------------------------

  echo-approx-comp-retract-budget :
    (BT : BalancedTolerance T) →
    ∀ (ε : Tol) → (zero + ε) ≡ ε
  echo-approx-comp-retract-budget BT ε =
    BalancedTolerance.+-identityˡ BT ε

  ----------------------------------------------------------------------
  -- Budget-aligned A-component round-trip (post-PR-#74 Rung C, the
  -- closest the approximate retract gets to a strict `from-to`
  -- equality without `≤`-propositionality).
  --
  -- `sound (retract-to e)` lives in `EchoR (zero + ε) (g ∘ f) y`,
  -- not in `EchoR ε (g ∘ f) y`. The `subst` along `+-identityˡ`
  -- pulls the witness back to the original tolerance type, after
  -- which the A-component round-trips on the nose.
  --
  -- The full equality `subst _ (+-identityˡ ε) (sound (retract-to e))
  -- ≡ e` is NOT discharged here: that would require propositionality
  -- of the order `_≤_` on the inner bound (the bound proofs are
  -- constructed by different routes — `subst (_≤ zero) ...` inside
  -- `intro` + `+-mono-≤` inside `compose` — and identifying them
  -- needs more structure than `Tolerance` asserts). The A-component
  -- equality below is the strongest statement available without
  -- assuming the order is a proposition.
  --
  -- The `subst` reduces to identity on the A-component because the
  -- `subst (λ ε' → EchoR ε' f y) p` transport acts on the bound
  -- proof, not on the A-witness (`EchoR ε f y = Σ A (λ x → dist (f x)
  -- y ≤ ε)`; only the second component depends on `ε`). The proof
  -- chains this through pattern matching on `e` and then leans on
  -- `subst-A-invariant` to expose the definitional reduction.
  ----------------------------------------------------------------------

  -- Auxiliary: `subst` along an equation on the tolerance index does
  -- not touch the A-component. `Σ`'s first component is independent
  -- of the type-family transport over the second.
  subst-A-invariant :
    ∀ {ε₁ ε₂ : Tol} (p : ε₁ ≡ ε₂)
    {f : A → B} {y : B} (e : EchoR ε₁ f y) →
    proj₁ (subst (λ ε → EchoR ε f y) p e) ≡ proj₁ e
  subst-A-invariant refl _ = refl

  echo-approx-comp-retract-from-to :
    (BT : BalancedTolerance T) →
    ∀ {ε : Tol} (f : A → B) (g : B → B) (g-nonexp : NonExpansive g)
    {y : B} (e : EchoR ε (g ∘ f) y) →
    proj₁ (subst (λ ε' → EchoR ε' (g ∘ f) y)
                 (BalancedTolerance.+-identityˡ BT ε)
                 (echo-approx-comp-sound f g g-nonexp
                   (echo-approx-comp-retract-to f g e)))
    ≡ proj₁ e
  echo-approx-comp-retract-from-to BT {ε = ε} f g g-nonexp e =
    let
      rt = echo-approx-comp-sound f g g-nonexp
             (echo-approx-comp-retract-to f g e)
      eq = BalancedTolerance.+-identityˡ BT ε
    in subst-A-invariant eq rt

  ----------------------------------------------------------------------
  -- §7 obligation 7: separated zero-collapse.
  --
  -- A pseudo-metric is *separated* when zero distance implies
  -- propositional equality on the carrier. Pseudo-metrics in general
  -- only guarantee `dist y y ≡ zero`; the converse (a metric proper)
  -- is an extra hypothesis the `PseudoMetric` record deliberately
  -- does not bake in. Callers who need the converse supply a
  -- `Separated` witness explicitly at the lemma site.
  --
  -- Under that hypothesis, the strict-vs-approximate gap closes at
  -- ε = zero: any zero-tolerance approximate echo IS a strict echo,
  -- with the same A-witness on the nose. This realises §7 #7 of the
  -- axis-2 design note and the §4 "Approximate → strict (only when
  -- separated, at ε = 0)" statement.
  --
  -- Without separation the converse fails by design — multiple `x`s
  -- may share zero distance to `y` without `f x ≡ y` on the nose.
  -- That is the point of an approximate echo.
  ----------------------------------------------------------------------

  Separated : Set (b ⊔ ℓ)
  Separated = ∀ b₁ b₂ → dist b₁ b₂ ≤ zero → b₁ ≡ b₂

  echo-approx-zero-collapses-strict :
    Separated →
    ∀ {f : A → B} {y : B} → EchoR zero f y → Echo f y
  echo-approx-zero-collapses-strict sep {f = f} {y = y} (x , dfx≤0) =
    x , sep (f x) y dfx≤0

  ----------------------------------------------------------------------
  -- §7 obligation 8: axis-1 shadow agreement.
  --
  -- The "shadow" of an approximate echo is its underlying A-witness —
  -- the projection that forgets the metric-bound proof. Two flavours:
  --
  --   * `echo-shadow-A`            — extracts the A-witness from an
  --                                  approximate echo (definitional,
  --                                  the existing `proj₁`).
  --
  --   * `echo-shadow-iso-{to,from}` — the trivial repackaging of
  --                                   `EchoR ε f y` as the existential
  --                                   `Σ A (λ x → dist (f x) y ≤ ε)`.
  --                                   Both directions are `id` because
  --                                   the two shapes are definitionally
  --                                   equal; the iso lemma here pins
  --                                   the §7 #8 obligation explicitly.
  --
  --   * `echo-strict→approx-shadow-A` — axis-1 / axis-2 cross-check:
  --                                     `echo-strict→approx` preserves
  --                                     the A-component on the nose
  --                                     (`refl`).  This is the
  --                                     definitional version of "the
  --                                     strict→approx inclusion and the
  --                                     A-shadow projection cohere"
  --                                     from the user-prompt framing.
  --
  -- Together these say: the A-component is a genuine axis-1 invariant
  -- of approximate echoes — every move in the axis-2 calculus that
  -- keeps the A-witness fixed (intro, strict→approx, relax,
  -- canonical-split retract section) preserves the axis-1 shadow
  -- definitionally.
  ----------------------------------------------------------------------

  echo-shadow-A :
    ∀ {ε : Tol} {f : A → B} {y : B} → EchoR ε f y → A
  echo-shadow-A = proj₁

  -- Forward: an approximate echo IS an existential with metric bound.
  -- Definitionally `id`; the lemma pins the axis-1 shadow obligation.
  echo-shadow-iso-to :
    ∀ {ε : Tol} {f : A → B} {y : B} →
    EchoR ε f y → Σ A (λ x → dist (f x) y ≤ ε)
  echo-shadow-iso-to e = e

  echo-shadow-iso-from :
    ∀ {ε : Tol} {f : A → B} {y : B} →
    Σ A (λ x → dist (f x) y ≤ ε) → EchoR ε f y
  echo-shadow-iso-from e = e

  -- A-component of `echo-strict→approx` agrees with the strict
  -- A-component on the nose. The transport in `echo-strict→approx`
  -- only touches the bound proof, never the A-witness.
  echo-strict→approx-shadow-A :
    ∀ {f : A → B} {y : B} (e : Echo f y) →
    echo-shadow-A (echo-strict→approx e) ≡ proj₁ e
  echo-strict→approx-shadow-A (x , _) = refl

  -- Round-trip: under separation, `echo-approx-zero-collapses-strict`
  -- and `echo-strict→approx` are mutually A-inverse at ε = zero,
  -- definitionally on the A-component. This closes the §4 statement
  -- "Approximate → strict (only when separated, at ε = 0)" with a
  -- definitional witness on the axis-1 shadow.
  echo-strict→approx-collapse-shadow-A :
    (sep : Separated) →
    ∀ {f : A → B} {y : B} (e : Echo f y) →
    proj₁ (echo-approx-zero-collapses-strict sep
            (echo-strict→approx e))
    ≡ proj₁ e
  echo-strict→approx-collapse-shadow-A sep (x , _) = refl
