{-# OPTIONS --safe --without-K #-}

-- Gate F2 feasibility spike (docs/echo-types/earn-back-plan.adoc §"Gate
-- F2 — A real second model of the *bare* Echo functor").
--
-- The R-2026-05-18 retraction noted that `EchoRelModel`'s "second
-- model" is not genuinely independent: its relational instance is the
-- Set model's carrier `× ⊤`, its step relation is the *total* relation
-- `RStep _ _ = ⊤` (a disguised graph), and `model-agreement` is `refl`.
-- The one R2 item rated "fixable with bounded work" was: give a model
-- that genuinely uses a NON-deterministic step relation that is *not*
-- the graph of a function, with the Echo-functor laws holding and an
-- agreement with the deterministic model that has real content (not
-- `refl`, not Σ-η on `× ⊤`), and that does NOT degenerate by
-- collapsing the relation back to a graph.
--
-- This spike uses `EchoRelational.StepND` — a genuinely
-- non-deterministic relation (state `false` reaches BOTH `false` and
-- `true`). It delivers:
--
--   1. `EchoFunctorModel` — the interface the deterministic Echo
--      model satisfies (carrier + functorial reindex + id/comp laws),
--      instantiated at the deterministic graph model AND at the
--      `StepND` model: the functor laws hold for both, by the same
--      generic proofs (`map-rel-id` / `map-rel-comp`).
--   2. `nd-not-graph` — a CHECKED proof (`true ≢ false`) that `StepND`
--      is NOT the graph of any function, under any state relabelling.
--      So the model cannot be obtained by trivialising the relation
--      back to a graph: the gate's failure clause is positively
--      excluded, not merely avoided.
--   3. `det→nd` — a relational morphism from the deterministic model
--      INTO the `StepND` model whose witness-preservation is genuine
--      constructor case analysis (emits different `StepND`
--      constructors per branch): a non-`refl`, non-Σ-η obligation.
--   4. `nd-fibre-is-sum` — the agreement with content: the `StepND`
--      echo-fibre over `true` is the disjoint sum of its two branch
--      fibres, established by case analysis on the `StepND`
--      constructors (a real bijection, not `refl`, not graph-collapse:
--      a non-deterministic relation IS a sum of deterministic
--      branches, and that decomposition is the honest agreement).
--
-- --safe --without-K, ZERO postulates. Not wired into `All.agda` /
-- `Smoke.agda` until Gate F2 is recorded passed.

module Echo.Bridges.EchoStepNDModelF2 where

open import Echo.Bridges.EchoRelational
  using (EchoStep; RelMap; map-rel; map-rel-id; map-rel-comp;
         Graph; StepND; stay-true; stay-false; flip-to-true)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Function.Base using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; trans; sym)

----------------------------------------------------------------------
-- 1. The interface the deterministic Echo model satisfies.
--
-- An Echo-functor model over a fixed output type is a step relation
-- together with the carrier `EchoStep` and the functorial reindexing
-- `map-rel` satisfying the identity and composition laws. The
-- deterministic model takes `Step = Graph g`; the F2 model takes
-- `Step = StepND`. The laws are the SAME generic proofs in both.

-- Functoriality is the identity law plus the composition law for the
-- model's own (endo) reindexings. Quantifying the composition law over
-- the model's *own* relation `Step` (not free `Step'`/`Step''`) is the
-- faithful "functor laws hold" statement and keeps every relation
-- determined — the generic `map-rel-id` / `map-rel-comp` discharge it.

record EchoFunctorModel (S O : Set) : Set₁ where
  field
    Step : S → O → Set
    reindex-id :
      ∀ {o} (e : EchoStep Step o) →
      map-rel {Step = Step} {Step' = Step} (id , λ p → p) e ≡ e
    reindex-comp :
      (u₁ u₂ : S → S)
      (c₁ : ∀ {st o} → Step st o → Step (u₁ st) o)
      (c₂ : ∀ {st o} → Step st o → Step (u₂ st) o)
      {o : O} (e : EchoStep Step o) →
      map-rel {Step = Step} {Step' = Step}
        (u₂ ∘ u₁ , λ p → c₂ (c₁ p)) e
      ≡ map-rel {Step = Step} {Step' = Step} (u₂ , c₂)
          (map-rel {Step = Step} {Step' = Step} (u₁ , c₁) e)

  Fib : O → Set
  Fib = EchoStep Step

-- The deterministic model: any function's graph. The functor laws are
-- exactly the generic `EchoRelational` lemmas.
det-model : (g : Bool → Bool) → EchoFunctorModel Bool Bool
det-model g = record
  { Step = Graph g
  ; reindex-id = λ {o} e → map-rel-id {Step = Graph g} {out = o} e
  ; reindex-comp = λ u₁ u₂ c₁ c₂ e →
      map-rel-comp {Step = Graph g} {Step' = Graph g} {Step'' = Graph g}
        u₁ c₁ u₂ c₂ e
  }

-- The F2 model: the genuinely non-deterministic `StepND`. SAME
-- interface, SAME generic functor-law proofs — yet (section 2) its
-- relation is provably not any function's graph.
nd-model : EchoFunctorModel Bool Bool
nd-model = record
  { Step = StepND
  ; reindex-id = λ {o} e → map-rel-id {Step = StepND} {out = o} e
  ; reindex-comp = λ u₁ u₂ c₁ c₂ e →
      map-rel-comp {Step = StepND} {Step' = StepND} {Step'' = StepND}
        u₁ c₁ u₂ c₂ e
  }

----------------------------------------------------------------------
-- 2. `StepND` is NOT the graph of any function (under any state
-- relabelling). State `false` reaches both `false` (`stay-false`) and
-- `true` (`flip-to-true`); a graph forces one output per state. So no
-- output-faithful relational map `StepND ⇒ Graph k` exists. This is
-- the checked guarantee that the model is genuinely non-deterministic
-- and the agreement below is NOT a disguised graph-collapse.

true≢false : true ≢ false
true≢false ()

GraphPresentation : Set
GraphPresentation =
  Σ (Bool → Bool) (λ u →
  Σ (Bool → Bool) (λ k →
    ∀ {st out} → StepND st out → k (u st) ≡ out))

nd-not-graph : ¬ GraphPresentation
nd-not-graph (u , k , pres) =
  -- k (u false) ≡ true   (from flip-to-true)
  -- k (u false) ≡ false  (from stay-false)  ⇒  true ≡ false
  true≢false
    (trans (sym (pres {false} {true} flip-to-true))
           (pres {false} {false} stay-false))

----------------------------------------------------------------------
-- 3. A relational morphism det → nd with content-bearing witness
-- preservation. `Graph id st out` is `id st ≡ out`, i.e. `st ≡ out`;
-- the preservation must PRODUCE a `StepND` constructor by case
-- analysis on the state — `stay-true` vs `stay-false`. This is not
-- `refl` and not Σ-η: it emits different constructors per branch.

det→nd-pres : ∀ {st out} → Graph id st out → StepND st out
det→nd-pres {true}  refl = stay-true
det→nd-pres {false} refl = stay-false

det→nd : RelMap (Graph id) StepND
det→nd = id , det→nd-pres

-- Functorial transport along det→nd, in the SHARED interface.
det→nd-reindex :
  ∀ {o} → EchoStep (Graph id) o → EchoStep StepND o
det→nd-reindex = map-rel det→nd

----------------------------------------------------------------------
-- 4. The agreement, WITH CONTENT. A non-deterministic relation is, at
-- each output, a SUM of deterministic branches. The `StepND`
-- echo-fibre over `true` is exactly the disjoint sum of its two
-- branch fibres — the `stay-true` branch (state `true`) and the
-- `flip-to-true` branch (state `false`). The bijection is established
-- by CASE ANALYSIS on the `StepND` constructors, not by `refl`/Σ-η,
-- and not by collapsing to a graph (which §2 proved impossible). This
-- IS the honest agreement of the nd model with deterministic data:
-- not "nd = some graph" but "nd = a structured sum of graphs".

NDBranch : Set
NDBranch = ⊤ ⊎ ⊤        -- inj₁ = stay-true branch ; inj₂ = flip branch

to-sum : EchoStep StepND true → NDBranch
to-sum (true  , stay-true)    = inj₁ tt
to-sum (false , flip-to-true) = inj₂ tt

from-sum : NDBranch → EchoStep StepND true
from-sum (inj₁ tt) = true  , stay-true
from-sum (inj₂ tt) = false , flip-to-true

-- Round-trips. Each is genuine constructor case analysis: a single
-- `refl` does NOT inhabit either ∀-statement (the fibre has two
-- structurally distinct inhabitants).
nd-sum-fromto : ∀ e → from-sum (to-sum e) ≡ e
nd-sum-fromto (true  , stay-true)    = refl
nd-sum-fromto (false , flip-to-true) = refl

nd-sum-tofrom : ∀ b → to-sum (from-sum b) ≡ b
nd-sum-tofrom (inj₁ tt) = refl
nd-sum-tofrom (inj₂ tt) = refl

-- The two branch inhabitants are genuinely distinct (the fibre is not
-- a proposition — exactly what no single deterministic graph fibre
-- over a point can be): content the `× ⊤` pseudo-model cannot express.
nd-fibre-not-prop :
  Σ (EchoStep StepND true) (λ a →
  Σ (EchoStep StepND true) (λ b → a ≢ b))
nd-fibre-not-prop =
  (true , stay-true)
  , (false , flip-to-true)
  , λ p → true≢false (cong proj₁ p)
