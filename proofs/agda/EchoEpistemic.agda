{-# OPTIONS --safe --without-K #-}

module EchoEpistemic where

open import EchoChoreo

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

-- Epistemic indistinguishability from a role-local observation.
Indist : Role → Global → Global → Set
Indist r g g' = obs r g ≡ obs r g'

indist-refl : ∀ {r : Role} {g : Global} → Indist r g g
indist-refl = refl

indist-sym : ∀ {r : Role} {g g' : Global} → Indist r g g' → Indist r g' g
indist-sym = sym

indist-trans :
  ∀ {r : Role} {g1 g2 g3 : Global} →
  Indist r g1 g2 → Indist r g2 g3 → Indist r g1 g3
indist-trans = trans

-- Knowledge at visible value y: P holds for every witness compatible with y.
-- Spelt out as `(e : RoleEcho r y) → ...` rather than `∀ e → ... ∋ e` so
-- Agda 2.8.0's unifier can see the role and value parameters through
-- downstream lemmas (knowledge-monotone-comp etc.) without a
-- type-ascription indirection.
Knows : Role → (Global → Set) → Bool → Set
Knows r P y = (e : RoleEcho r y) → P (proj₁ e)

knows-from-preimage :
  ∀ {r : Role} {y : Bool} {P : Global → Set} →
  (∀ g → obs r g ≡ y → P g) →
  Knows r P y
knows-from-preimage pre (g , p) = pre g p

knowledge-monotone :
  ∀ {r : Role} {y : Bool} {P Q : Global → Set} →
  (∀ g → P g → Q g) →
  Knows r P y →
  Knows r Q y
knowledge-monotone pq k e = pq (proj₁ e) (k e)

-- Per-decoration composition law for the modal layer. Two successive
-- monotonicity steps `P ⊆ Q` then `Q ⊆ R` agree pointwise with the
-- single composite `P ⊆ R` (composed predicate transformer).
--
-- This is the modal analogue of `EchoGraded.degrade-compose`,
-- `EchoLinear.degradeMode-comp`, and `EchoIndexed.map-role-indexed-comp`.
-- Stated pointwise on each predicate-witness `e : RoleEcho r y` so the
-- equation lives inside `--safe --without-K` without function
-- extensionality. Both sides reduce to `qr (proj₁ e) (pq (proj₁ e)
-- (k e))` definitionally.
-- Implicit args to `knowledge-monotone` are annotated explicitly at every
-- call site. Under Agda 2.8.0 the unifier won't infer the implicit role
-- `r` from `obs _r x = obs r x` (obs isn't injective), so the
-- decoration's role+value+predicate parameters must be supplied directly.
knowledge-monotone-comp :
  ∀ {r : Role} {y : Bool} {P Q R : Global → Set}
  (pq : ∀ g → P g → Q g)
  (qr : ∀ g → Q g → R g)
  (k  : Knows r P y) →
  (e : RoleEcho r y) →
    knowledge-monotone {r = r} {y = y} {P = Q} {Q = R} qr
      (knowledge-monotone {r = r} {y = y} {P = P} {Q = Q} pq k) e
  ≡ knowledge-monotone {r = r} {y = y} {P = P} {Q = R}
      (λ g p → qr g (pq g p)) k e
knowledge-monotone-comp pq qr k e = refl

-- Identity-step corollary: monotonicity along the identity predicate
-- transformer leaves knowledge unchanged. Useful when chaining with
-- the composition lemma above to peel off no-op steps.
knowledge-monotone-id :
  ∀ {r : Role} {y : Bool} {P : Global → Set}
  (k : Knows r P y) →
  (e : RoleEcho r y) →
    knowledge-monotone {r = r} {y = y} {P = P} {Q = P} (λ _ p → p) k e
  ≡ k e
knowledge-monotone-id k e = refl

ServerIsTrue : Global → Set
ServerIsTrue g = proj₂ g ≡ true

ServerIsFalse : Global → Set
ServerIsFalse g = proj₂ g ≡ false

-- Client observing `true` does not determine the hidden server bit.
not-knows-server-true-at-client-true : ¬ Knows Client ServerIsTrue true
not-knows-server-true-at-client-true k =
  true≢false (sym (k ((true , false) , refl)))

not-knows-server-false-at-client-true : ¬ Knows Client ServerIsFalse true
not-knows-server-false-at-client-true k =
  true≢false (k ((true , true) , refl))

-- If two globals are indistinguishable, they share a common visible echo value.
shared-echo-from-indist :
  ∀ {r : Role} {g g' : Global} →
  Indist r g g' →
  Σ Bool (λ y → RoleEcho r y × RoleEcho r y)
shared-echo-from-indist {r} {g} {g'} p =
  obs r g , (g , refl) , (g' , sym p)

-- Any two echoes at the same visible value induce indistinguishable states.
indist-from-two-echoes :
  ∀ {r : Role} {y : Bool} →
  (e1 e2 : RoleEcho r y) →
  Indist r (proj₁ e1) (proj₁ e2)
indist-from-two-echoes (g1 , p1) (g2 , p2) = trans p1 (sym p2)

-- Knowledge transport through choreography steps that preserve client visibility.
knowledge-along-client-stability :
  ∀ {y : Bool} {P : Global → Set} →
  (∀ g → P g → P (scramble-server g)) →
  Knows Client P y →
  ∀ e → P (proj₁ (client-stability e))
knowledge-along-client-stability inv k (g , p) = inv g (k (g , p))
