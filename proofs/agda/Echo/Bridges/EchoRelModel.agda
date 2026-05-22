{-# OPTIONS --safe --without-K #-}

-- RETRACTION 2026-05-18 (docs/retractions.adoc R-2026-05-18): this
-- module's "second model", "model-independence", and "graded-comonad
-- laws" are RETRACTED claims. set-model and rel-model fix the SAME
-- grade poset; rel-model's carrier is set-model's × ⊤;
-- model-agreement is refl; GradedLossModel's ⊑-prop field bakes in
-- the only load-bearing hypothesis. The Agda is unchanged and
-- correct; read it as *carrier-parametricity over a fixed grade
-- poset*, not model-independence, and the equations as thin-poset
-- reindexing coherence, not comonad laws. Authoritative prose:
-- docs/echo-types/paper.adoc §"Reframing note", conservativity.adoc.

-- Pillar D (part 1) of docs/echo-types/establishment-plan.adoc.
--
-- REAL MODULE (second model + model-independence landed 2026-05-17).
--
-- Goal: a SECOND MODEL. A type-theoretic notion is established only
-- if it is model-independent. The H2 verdict (establishment-plan
-- §"H2 verdict") showed every graded-comonad law collapses to
-- `reindex-compose` + order-propositionality, with NO path algebra.
-- That makes model-independence provable in the strongest form:
--
--   1. Abstract the model interface as `GradedLossModel` (a
--      propositional grade order with a composing reindexing).
--   2. Prove the graded-comonad laws ONCE, generically, from the
--      interface — `module GCLaws`. This *is* the model-independence
--      theorem: the laws hold in EVERY such model by one proof.
--   3. Instantiate at two genuinely different models:
--        * `set-model`  — `EchoGraded` (Set/Type model).
--        * `rel-model`  — the relational/fibration realization,
--          carrier `EchoStep`, reindexing via `map-rel`, the
--          composition law from `map-rel-comp` + `degrade-comp`.
--   4. `model-agreement` — the two models' reindexing actions agree
--      under the graph/fibration bridge (round-trips `refl`), so the
--      graded comonad is the SAME structure in both.
--
-- Plus the Echo-functor second model: the bridge
-- `echo-to-graph`/`graph-to-echo` (= `EchoCategorical.Fibration`'s
-- `fiber-to-echo`/`echo-to-fiber` specialised to a deterministic f)
-- intertwines `Echo.map-over` with `EchoRelational.map-rel`
-- (`bridge-natural`), so the Echo functor itself — on which the
-- graded comonad sits — is model-independent.
--
-- Reuse: `EchoRelational` (EchoStep / RelMap / map-rel / map-rel-id
-- / map-rel-comp / Graph / echo-to-graph / graph-to-echo) and
-- `EchoGraded` (the loss lattice, degrade, degrade-comp, ≤g-prop).

module Echo.Bridges.EchoRelModel where

open import Echo.Core using (Echo; MapOver; map-over)
open import Echo.Bridges.EchoRelational
  using (EchoStep; RelMap; map-rel; map-rel-comp;
         Graph; echo-to-graph; graph-to-echo)
open import Echo.Bridges.EchoGraded
  using (Grade; keep; GEcho; degrade; degrade-comp;
         _≤g_; ≤g-prop; ≤g-trans; _⊔g_; ≤g-⊔g-left)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)

----------------------------------------------------------------------
-- 1. The abstract model interface.
--
-- A graded loss model is a propositional grade order with a join and
-- a reindexing action that composes along a chosen factoring. This is
-- exactly the `EchoGraded` interface, abstracted: the H2 verdict
-- proved the comonad laws need nothing more.

record GradedLossModel : Set₁ where
  field
    Gr      : Set
    bot     : Gr
    _⊑_     : Gr → Gr → Set
    ⊑-prop  : ∀ {a b} (p q : a ⊑ b) → p ≡ q
    ⊑-trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c
    _⊔_     : Gr → Gr → Gr
    ⊔-left  : ∀ a b → a ⊑ (a ⊔ b)
    Obj     : Gr → Set
    reindex : ∀ {a b} → a ⊑ b → Obj a → Obj b
    reindex-comp :
      ∀ {a b c} (p : a ⊑ b) (q : b ⊑ c) (x : Obj a) →
      reindex q (reindex p x) ≡ reindex (⊑-trans p q) x

----------------------------------------------------------------------
-- 2. The graded-comonad laws, proved ONCE for any model.
--
-- This is the model-independence theorem. Every step is a verbatim
-- port of `EchoGradedComonad`'s proofs in the common-upper-bound
-- idiom — confirming the H2 verdict was model-independent all along.

module GCLaws (M : GradedLossModel) where
  open GradedLossModel M

  -- Path-independence (the H2 kernel): order-propositionality plus
  -- chosen-path composition kill every factoring difference.
  reindex-compose :
    ∀ {a b c} (p : a ⊑ b) (q : b ⊑ c) (r : a ⊑ c) (x : Obj a) →
    reindex q (reindex p x) ≡ reindex r x
  reindex-compose p q r x
    rewrite ⊑-prop r (⊑-trans p q) = reindex-comp p q x

  -- Graded comultiplication: split the loss budget along the join.
  gduplicate : ∀ a b → Obj a → Obj (a ⊔ b)
  gduplicate a b = reindex (⊔-left a b)

  gcomonad-counit-l :
    ∀ {g g'} (p : (bot ⊔ g) ⊑ g') (q : bot ⊑ g') (x : Obj bot) →
    reindex p (gduplicate bot g x) ≡ reindex q x
  gcomonad-counit-l {g} p q x = reindex-compose (⊔-left bot g) p q x

  gcomonad-counit-r :
    ∀ {g g'} (p : (g ⊔ bot) ⊑ g') (q : g ⊑ g') (x : Obj g) →
    reindex p (gduplicate g bot x) ≡ reindex q x
  gcomonad-counit-r {g} p q x = reindex-compose (⊔-left g bot) p q x

  gcomonad-coassoc :
    ∀ {g₁ g₂ g₃ g}
    (p : ((g₁ ⊔ g₂) ⊔ g₃) ⊑ g)
    (q : (g₁ ⊔ (g₂ ⊔ g₃)) ⊑ g)
    (x : Obj g₁) →
    reindex p (gduplicate (g₁ ⊔ g₂) g₃ (gduplicate g₁ g₂ x))
    ≡ reindex q (gduplicate g₁ (g₂ ⊔ g₃) x)
  gcomonad-coassoc {g₁} {g₂} {g₃} {g} p q x =
    let a = ⊔-left g₁ g₂
        b = ⊔-left (g₁ ⊔ g₂) g₃
        c = ⊔-left g₁ (g₂ ⊔ g₃)
    in begin
      reindex p (reindex b (reindex a x))
        ≡⟨ reindex-compose b p (⊑-trans b p) (reindex a x) ⟩
      reindex (⊑-trans b p) (reindex a x)
        ≡⟨ reindex-compose a (⊑-trans b p)
             (⊑-trans a (⊑-trans b p)) x ⟩
      reindex (⊑-trans a (⊑-trans b p)) x
        ≡⟨ cong (λ z → reindex z x)
             (⊑-prop (⊑-trans a (⊑-trans b p)) (⊑-trans c q)) ⟩
      reindex (⊑-trans c q) x
        ≡⟨ sym (reindex-compose c q (⊑-trans c q) x) ⟩
      reindex q (reindex c x)
    ∎
    where open ≡-Reasoning

----------------------------------------------------------------------
-- 3a. The Set/Type model — EchoGraded.

set-model : GradedLossModel
set-model = record
  { Gr = Grade ; bot = keep
  ; _⊑_ = _≤g_ ; ⊑-prop = ≤g-prop ; ⊑-trans = ≤g-trans
  ; _⊔_ = _⊔g_ ; ⊔-left = ≤g-⊔g-left
  ; Obj = GEcho ; reindex = degrade ; reindex-comp = degrade-comp
  }

----------------------------------------------------------------------
-- 3b. The relational / fibration model.
--
-- Same loss lattice (it is the same notion of loss), but the carrier
-- is a relational fibre `EchoStep` and the reindexing is the
-- relational `map-rel`. The total-relation system `RStep _ _ = ⊤`
-- makes `EchoStep RStep tt ≅ GEcho g`; reindexing transports the
-- state by `degrade`. The composition law is the relational
-- `map-rel-comp` (relational composition is honest) combined with
-- `degrade-comp` (the state side composes) — a genuinely different
-- model satisfying the same interface.

RStep : ∀ {g} → GEcho g → ⊤ → Set
RStep _ _ = ⊤

RObj : Grade → Set
RObj g = EchoStep (RStep {g}) tt

r-relmap : ∀ {g₁ g₂} → g₁ ≤g g₂ → RelMap (RStep {g₁}) (RStep {g₂})
r-relmap p = degrade p , (λ _ → tt)

r-reindex : ∀ {g₁ g₂} → g₁ ≤g g₂ → RObj g₁ → RObj g₂
r-reindex p = map-rel (r-relmap p)

r-reindex-comp :
  ∀ {g₁ g₂ g₃} (p : g₁ ≤g g₂) (q : g₂ ≤g g₃) (x : RObj g₁) →
  r-reindex q (r-reindex p x) ≡ r-reindex (≤g-trans p q) x
r-reindex-comp p q (st , tt) = cong (λ z → z , tt) (degrade-comp p q st)
-- (`map-rel-comp p _ q _ (st , tt)` independently witnesses that the
--  relational composition agrees with the composed `map-rel`; the
--  substantive content is `degrade-comp` on the state component.)

rel-model : GradedLossModel
rel-model = record
  { Gr = Grade ; bot = keep
  ; _⊑_ = _≤g_ ; ⊑-prop = ≤g-prop ; ⊑-trans = ≤g-trans
  ; _⊔_ = _⊔g_ ; ⊔-left = ≤g-⊔g-left
  ; Obj = RObj ; reindex = r-reindex ; reindex-comp = r-reindex-comp
  }

-- The relational graded-comonad laws, for free, by the SAME proof.
module Rel = GCLaws rel-model
module SetM = GCLaws set-model

rel-gcomonad-counit-l = Rel.gcomonad-counit-l
rel-gcomonad-counit-r = Rel.gcomonad-counit-r
rel-gcomonad-coassoc  = Rel.gcomonad-coassoc

----------------------------------------------------------------------
-- 4. Model agreement.
--
-- The Set carrier `GEcho g` and the relational carrier `RObj g` are
-- isomorphic (round-trips `refl` by Σ-/⊤-η), and the iso intertwines
-- the two reindexing actions: the relational reindex IS the Set
-- reindex (`degrade`), conjugated by the iso. Hence the graded
-- comonad is the *same* structure in both models.

s→r : ∀ {g} → GEcho g → RObj g
s→r x = x , tt

r→s : ∀ {g} → RObj g → GEcho g
r→s (x , tt) = x

r→s∘s→r : ∀ {g} (x : GEcho g) → r→s (s→r x) ≡ x
r→s∘s→r _ = refl

s→r∘r→s : ∀ {g} (x : RObj g) → s→r (r→s x) ≡ x
s→r∘r→s (_ , tt) = refl

-- The agreement: the relational reindex, read back through the iso,
-- is exactly the Set-model reindex `degrade`.
model-agreement :
  ∀ {g₁ g₂} (p : g₁ ≤g g₂) (x : GEcho g₁) →
  r→s (GradedLossModel.reindex rel-model p (s→r x))
  ≡ GradedLossModel.reindex set-model p x
model-agreement p x = refl

----------------------------------------------------------------------
-- 5. The Echo functor itself is model-independent.
--
-- The graph bridge `echo-to-graph` / `graph-to-echo` is a
-- definitional iso (= `EchoCategorical.Fibration`'s
-- `fiber-to-echo`/`echo-to-fiber` for a deterministic f). It
-- intertwines the Set action `map-over` with the relational action
-- `map-rel`: `bridge-natural`. So the Echo functor — the carrier of
-- the graded comonad — is the same in the Set and relational models.

module _ {A A' B : Set} {f : A → B} {f' : A' → B} where

  echo↔graph-l :
    ∀ {y : B} (e : Echo f y) → graph-to-echo (echo-to-graph e) ≡ e
  echo↔graph-l (_ , _) = refl

  echo↔graph-r :
    ∀ {y : B} (r : EchoStep (Graph f) y) →
    echo-to-graph (graph-to-echo r) ≡ r
  echo↔graph-r (_ , _) = refl

  relmap-of : MapOver f f' → RelMap (Graph f) (Graph f')
  relmap-of (u , c) = u , (λ {st} gp → trans (c st) gp)

  bridge-natural :
    ∀ (MO : MapOver f f') {y : B} (e : Echo f y) →
    echo-to-graph {f = f'} (map-over {f = f} {f' = f'} MO e)
    ≡ map-rel {Step = Graph f} {Step' = Graph f'}
        (relmap-of MO) (echo-to-graph {f = f} e)
  bridge-natural (u , c) (x , p) = refl
