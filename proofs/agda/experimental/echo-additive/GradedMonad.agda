{-# OPTIONS --safe --without-K #-}

-- EXPERIMENTAL — R3 PRIMARY LINE: the graded monad multiplication φ.
-- AUTHOR-GATED comparative variance protocol (R2/R3). NOT merged to main (W6).
--
-- PRIMARY line of the comparison (VarianceGate.agda §3):
--   φ_{r,s}(A) : D r (D s A) → D (r +g s) A
-- the MONADIC multiplication (μ-direction), the additive shadow of
-- Echo.Echo-comp-iso-FROM (the "combining"/"from" direction, Echo.agda:79-83):
--   Echo-comp-iso-from : Σ B (λ b → Echo f b × g b ≡ y) → Echo (g ∘ f) y
-- which FUSES two accumulated layers into one. On GradedCarrier.D the additive
-- shadow of that fusion is the carrier split
--   D-fin-+-split m n : D-fin (m + n) A ≡ D-fin m (D-fin n A);
-- φ reads it RIGHT-to-LEFT (combine), i.e. transports along its sym.
--
-- FIREWALL (W2): imports GradedCarrier + Grade + (read-only) Echo. Does NOT
-- import GradedComonad (the δ line). ZERO POSTULATES (W3): undischargeable laws
-- park as -- OBLIGATION comments; the file typechecks with NO holes, NO postulate.
--
-- Variance finding (VarianceGate.agda:120-123): the MONADIC line is the natural
-- fit since φ comes from Echo-comp-iso-FROM, the combining direction.

module experimental.echo-additive.GradedMonad where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.Properties
  using (sym-cong)
open import Function.Base using (id; _∘_)

open import experimental.echo-additive.Grade
  using (Grade; fin; inf; _+g_; +g-assoc; +g-identityˡ; +g-identityʳ)
open import experimental.echo-additive.GradedCarrier
  using (D; D-fin; D-fin-+-split)

-- (Echo is imported READ-ONLY to anchor provenance. D-fin-+-split IS the additive
--  image of Echo-comp-iso; φ uses its sym = the combine/from direction.)
open import Echo using (Echo-comp-iso-from)

----------------------------------------------------------------------
-- φ : the graded multiplication  D r (D s A) → D (r +g s) A
--   (fin n,fin m): combine via sym (D-fin-+-split n m) (the from/μ reshuffle).
--                  D-fin-+-split n m : D-fin (n+m) A ≡ D-fin n (D-fin m A); its sym
--                  is D-fin n (D-fin m A) ≡ D-fin (n+m) A — exactly φ's direction.
--   (inf , _)    : D inf (D s A) = ⊤ and inf +g s = inf, so ⊤ → ⊤ = id.
--   (fin n,inf)  : D (fin n)(D inf A) = D-fin n ⊤ and fin n +g inf = inf, → tt.

φ : ∀ (r s : Grade) (A : Set) → D r (D s A) → D (r +g s) A
φ (fin n) (fin m) A x = subst id (sym (D-fin-+-split n m)) x
φ (fin n) inf     A _ = tt
φ inf     s       A x = x      -- D inf (D s A) = ⊤ = D (inf +g s) A

----------------------------------------------------------------------
-- The functorial action of D (to state D_r(φ_{s,t}) in the pentagon).
-- D-fin n is a functor: map over the innermost A, leaving the trivial ⊤ layers.

D-fin-map : ∀ {A B : Set} (f : A → B) (n : ℕ) → D-fin n A → D-fin n B
D-fin-map f zero    x        = f x
D-fin-map f (suc n) (tt , y) = tt , D-fin-map f n y

D-map : ∀ {A B : Set} (f : A → B) (r : Grade) → D r A → D r B
D-map f (fin n) x = D-fin-map f n x
D-map f inf     _ = tt

----------------------------------------------------------------------
-- η : the graded unit  A → D (fin 0) A  (= A, definitionally).
η : ∀ (A : Set) → A → D (fin 0) A
η A a = a

----------------------------------------------------------------------
-- LAW GOALS (VarianceGate.agda:125-133), stated EXACTLY, then discharged.

----------------------------------------------------------------------
-- LEFT UNIT (VarianceGate.agda:129-130):
--   D (fin 0)(D r A) → D (fin 0 +g r) A = D r A  reduces to the D (fin 0)(−) ≅ Id
--   coercion. Stated with the (refl-valued) +g-identityˡ coercion on the LHS so it
--   is well-typed for ABSTRACT r. Both clauses close by refl ⇒ φ (fin 0) r = Id-coercion.
left-unit : ∀ (r : Grade) (A : Set) (x : D (fin 0) (D r A)) →
            subst (λ g → D g A) (+g-identityˡ r) (φ (fin 0) r A x) ≡ x
left-unit (fin m) A x = refl   -- subst _ refl (subst id (sym (D-fin-+-split 0 m)) x) = x
left-unit inf     A x = refl   -- φ (fin 0) inf A _ = tt ; coercion refl ; x : ⊤

----------------------------------------------------------------------
-- RIGHT UNIT (VarianceGate.agda:131-133):
--   D r (D (fin 0) A) → D (r +g fin 0) A = D r A  reduces to D r of the
--   D (fin 0)(−) ≅ Id iso. NOT refl on the finite case: n + 0 ≡ n is +-identityʳ.

-- KEY PROOF-EQUALITY LEMMA (UIP-free): the carrier split at n = 0 (RHS index) IS
-- the canonical ℕ-coercion proof. D-fin-+-split n 0 : D-fin (n+0) A ≡ D-fin n (D-fin 0 A)
-- and D-fin 0 A = A, so endpoints D-fin (n+0) A ≡ D-fin n A, matching
-- cong (D-fin•A) (+-identityʳ n). Both are cong-towers over the same recursion
-- (D-fin-+-split by cong (λ T → ⊤ × T); +-identityʳ by cong suc).
split0-is-coercion-proof :
  ∀ n (A : Set) →
  D-fin-+-split n 0 {A} ≡ cong (λ k → D-fin k A) (+-identityʳ n)
split0-is-coercion-proof zero    A = refl
split0-is-coercion-proof (suc n) A =
  trans (cong (cong (λ T → ⊤ × T)) (split0-is-coercion-proof n A))
        (cong-∘-suc n A)
  where
    cong-∘-suc : ∀ n (A : Set) →
      cong (λ T → ⊤ × T) (cong (λ k → D-fin k A) (+-identityʳ n))
      ≡ cong (λ k → D-fin k A) (+-identityʳ (suc n))
    cong-∘-suc n A = cong-∘-lemma (+-identityʳ n)
      where
        -- cong (λ T → ⊤ × T) (cong (λ k → D-fin k A) p)
        --   = cong (λ k → D-fin (suc k) A) p = cong (λ k → D-fin k A) (cong suc p),
        -- and +-identityʳ (suc n) = cong suc (+-identityʳ n) definitionally.
        cong-∘-lemma : ∀ {a b : ℕ} (p : a ≡ b) →
          cong (λ T → ⊤ × T) (cong (λ k → D-fin k A) p)
          ≡ cong (λ k → D-fin k A) (cong suc p)
        cong-∘-lemma refl = refl

-- RIGHT UNIT, finite case (ℕ/D-fin level). φ uses sym (D-fin-+-split n 0).
right-unit-fin : ∀ n (A : Set) (x : D (fin n) (D (fin 0) A)) →
                 φ (fin n) (fin 0) A x
                 ≡ subst (λ k → D-fin k A) (sym (+-identityʳ n)) x
right-unit-fin n A x =
  trans (cong (λ p → subst id (sym p) x) (split0-is-coercion-proof n A))
        (subst-cong-id n A x)
  where
    subst-cong-id : ∀ n (A : Set) (x : D-fin n (D-fin 0 A)) →
      subst id (sym (cong (λ k → D-fin k A) (+-identityʳ n))) x
      ≡ subst (λ k → D-fin k A) (sym (+-identityʳ n)) x
    subst-cong-id n A x = subst-cong-id-lemma (+-identityʳ n) x
      where
        subst-cong-id-lemma : ∀ {a b : ℕ} (p : a ≡ b) (z : D-fin b A) →
          subst id (sym (cong (λ k → D-fin k A) p)) z
          ≡ subst (λ k → D-fin k A) (sym p) z
        subst-cong-id-lemma refl z = refl

-- RIGHT UNIT, infinite case: φ inf (fin 0) A x = x.
right-unit-inf : ∀ (A : Set) (x : D inf (D (fin 0) A)) →
                 φ inf (fin 0) A x ≡ x
right-unit-inf A x = refl

-- RIGHT UNIT, uniform grade-level form (VarianceGate.agda:131-133 EXACT shape).
-- FULLY DISCHARGED (no postulate, no hole).
right-unit : ∀ (r : Grade) (A : Set) (x : D r (D (fin 0) A)) →
             φ r (fin 0) A x ≡ subst (λ g → D g A) (sym (+g-identityʳ r)) x
right-unit (fin n) A x =
  trans (right-unit-fin n A x) (lift-to-grade n A x)
  where
    -- +g-identityʳ (fin n) = cong fin (+-identityʳ n) (Grade.agda:91); sym-cong +
    -- subst-∘ through `fin`. Both UIP-free.
    lift-to-grade : ∀ n (A : Set) (x : D-fin n (D-fin 0 A)) →
      subst (λ k → D-fin k A) (sym (+-identityʳ n)) x
      ≡ subst (λ g → D g A) (sym (+g-identityʳ (fin n))) x
    lift-to-grade n A x =
      trans (lift-lemma (sym (+-identityʳ n)) x)
            (cong (λ e → subst (λ g → D g A) e x) (sym (sym-cong {f = fin} (+-identityʳ n))))
      where
        lift-lemma : ∀ {a b : ℕ} (q : a ≡ b) (z : D-fin a A) →
          subst (λ k → D-fin k A) q z
          ≡ subst (λ g → D g A) (cong fin q) z
        lift-lemma refl z = refl
right-unit inf A x = right-unit-inf A x

----------------------------------------------------------------------
-- PENTAGON / ASSOCIATIVITY (VarianceGate.agda:127, EXACT shape):
--   φ_{r,s+t} ∘ D_r(φ_{s,t})  =  φ_{r+s,t} ∘ φ_{r,s}(D_t(-))
-- LHS : D r (D s (D t A)) → D (r +g (s +g t)) A
-- RHS : D r (D s (D t A)) → D ((r +g s) +g t) A,  coerced via +-assoc (ℕ level).
--
-- FINITE diagonal at ℕ/D-fin level. RHS lands in D-fin ((a+b)+c) A, coerced into
-- D-fin (a+(b+c)) A via +-assoc a b c. FULLY DISCHARGED by induction on a,
-- peeling the outer trivial ⊤-layer on both sides.
pentagon-fin :
  ∀ a b c (A : Set) (x : D-fin a (D-fin b (D-fin c A))) →
  φ (fin a) (fin b +g fin c) A (D-map (φ (fin b) (fin c) A) (fin a) x)
  ≡ subst (λ k → D-fin k A) (+-assoc a b c)
      (φ (fin (a + b)) (fin c) A (φ (fin a) (fin b) (D-fin c A) x))
pentagon-fin zero b c A x = refl
  -- a = 0: D-map _ (fin 0) x = φ (fin b)(fin c) A x; outer φ (fin 0) _ and
  -- φ (fin 0)(fin b) use sym (D-fin-+-split 0 _) = sym refl = refl; +-assoc 0 b c = refl.
pentagon-fin (suc a) b c A (tt , y) =
  trans (peel-LHS a b c A y)
        (trans (cong (λ z → tt , z) (pentagon-fin a b c A y))
               (sym (peel-RHS a b c A y)))
  where
    open ≡-Reasoning
    -- subst id along a ⊤×- layer cong commutes with the layer.
    -- (p : S ≡ T; sym (cong (⊤×) p) : ⊤×T ≡ ⊤×S, so it transports (tt , y : ⊤×T).)
    layer-subst : ∀ {S T : Set} (p : S ≡ T) (y : T) →
      subst id (sym (cong (λ U → ⊤ × U) p)) (tt , y)
      ≡ (tt , subst id (sym p) y)
    layer-subst refl y = refl
    -- subst (D-fin•A) along cong suc commutes with the layer.
    suc-subst : ∀ (A : Set) {a' b' : ℕ} (q : a' ≡ b') (y : D-fin a' A) →
      subst (λ k → D-fin k A) (cong suc q) (tt , y)
      ≡ (tt , subst (λ k → D-fin k A) q y)
    suc-subst A refl y = refl

    peel-LHS : ∀ a b c (A : Set) (y : D-fin a (D-fin b (D-fin c A))) →
      φ (fin (suc a)) (fin b +g fin c) A
        (D-map (φ (fin b) (fin c) A) (fin (suc a)) (tt , y))
      ≡ (tt , φ (fin a) (fin b +g fin c) A (D-map (φ (fin b) (fin c) A) (fin a) y))
    peel-LHS a b c A y =
      layer-subst (D-fin-+-split a (b + c)) (D-fin-map (φ (fin b) (fin c) A) a y)

    peel-RHS : ∀ a b c (A : Set) (y : D-fin a (D-fin b (D-fin c A))) →
      subst (λ k → D-fin k A) (+-assoc (suc a) b c)
        (φ (fin (suc a + b)) (fin c) A (φ (fin (suc a)) (fin b) (D-fin c A) (tt , y)))
      ≡ (tt , subst (λ k → D-fin k A) (+-assoc a b c)
              (φ (fin (a + b)) (fin c) A (φ (fin a) (fin b) (D-fin c A) y)))
    peel-RHS a b c A y =
      begin
        subst (λ k → D-fin k A) (+-assoc (suc a) b c)
          (φ (fin (suc a + b)) (fin c) A (φ (fin (suc a)) (fin b) (D-fin c A) (tt , y)))
      ≡⟨ cong (λ w → subst (λ k → D-fin k A) (+-assoc (suc a) b c)
                      (φ (fin (suc a + b)) (fin c) A w))
              (layer-subst (D-fin-+-split a b) y) ⟩
        subst (λ k → D-fin k A) (+-assoc (suc a) b c)
          (φ (fin (suc a + b)) (fin c) A (tt , φ (fin a) (fin b) (D-fin c A) y))
      ≡⟨ cong (subst (λ k → D-fin k A) (+-assoc (suc a) b c))
              (layer-subst (D-fin-+-split (a + b) c)
                           (φ (fin a) (fin b) (D-fin c A) y)) ⟩
        subst (λ k → D-fin k A) (+-assoc (suc a) b c)
          (tt , φ (fin (a + b)) (fin c) A (φ (fin a) (fin b) (D-fin c A) y))
      ≡⟨ suc-subst A (+-assoc a b c)
                   (φ (fin (a + b)) (fin c) A (φ (fin a) (fin b) (D-fin c A) y)) ⟩
        (tt , subst (λ k → D-fin k A) (+-assoc a b c)
              (φ (fin (a + b)) (fin c) A (φ (fin a) (fin b) (D-fin c A) y)))
      ∎

----------------------------------------------------------------------
-- PENTAGON, ∞-cases. r = inf forces D (… inf …) = ⊤ and inf +g … = inf, so both
-- composites land in ⊤ and agree by ⊤-η. (s = inf / t = inf are analogous.)
pentagon-inf-r :
  ∀ (s t : Grade) (A : Set) (x : D inf (D s (D t A))) →
  φ inf (s +g t) A (D-map (φ s t A) inf x)
  ≡ subst (λ g → D g A) (+g-assoc inf s t)
      (φ inf t A (φ inf s (D t A) x))
pentagon-inf-r s t A x = refl
