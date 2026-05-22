{-# OPTIONS --safe --without-K #-}

-- A concrete `CostAlgebra` instance for `EchoCost.Cost`, whose sole
-- purpose is to give `Smoke.agda` a typeable identifier per headline
-- lemma of the parameterised `EchoCost.Cost` module.
--
-- Repo invariant (`CLAUDE.md`, "Working rules"):
--
--     "Every headline theorem must be pinned in `Smoke.agda` via
--      `using` clause."
--
-- Lemmas living inside the parameterised submodule `EchoCost.Cost`
-- cannot be named in `Smoke.agda` until *some* `CostAlgebra` is
-- supplied, so the invariant is silently violated for every
-- `echo-cost-*` lemma. This module closes that gap, in exactly the
-- same shape as `EchoApproxInstance.agda` does for `EchoApprox.Approx`.
--
-- Design call: the trivial / collapse-to-strict cost algebra on `⊤`.
--
--   * `Cost`        := `⊤`
--   * `zero`        := `tt`
--   * `_+_`         := `λ _ _ → tt`
--   * `_≤_`         := `λ _ _ → ⊤`
--   * `+-identityˡ` := `λ _ → refl` (`tt ≡ tt` is `refl`)
--   * all order / monotonicity / triangle obligations discharge to `tt`.
--
-- Every cost-indexed echo
--   `EchoC cost c f y = Σ A (λ x → f x ≡ y × cost x ≤ c)`
-- collapses to
--   `Σ A (λ x → f x ≡ y × ⊤)`,
-- so each pinned lemma here is a trivial sanity check that the
-- parameterised module's term is well-typed at *some* instance. That
-- is exactly the hygiene contract the invariant asks for — proof-of-
-- life, not new content.
--
-- We choose `A := ⊤` and `B := ⊤` so each pinned name resolves to a
-- single top-level identifier with no remaining type parameters,
-- which lets `Smoke.agda` enumerate them in a `using` clause
-- one-for-one (`EchoApproxInstance.agda` pattern).
--
-- A non-trivial cost carrier (e.g. `ℕ` with `_+_` / `_≤_` from
-- `Data.Nat`) would also work, but adds nothing the trivial one does
-- not give for the purposes of `Smoke.agda` pinning. When a genuine
-- cost-algebra instance lands in the repo, the per-lemma pins below
-- can be re-pointed at it.

module Echo.Bridges.EchoCostInstance where

open import Level                                 using (Level)
open import Data.Unit.Base                        using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Echo.Bridges.EchoCost using (CostAlgebra; module Cost)

----------------------------------------------------------------------
-- The trivial cost algebra on `⊤`
----------------------------------------------------------------------

-- All fields are tt / Unit; every law obligation is met by `tt` /
-- `refl`. `+-identityˡ tt ≡ tt` is `refl` because `(tt + tt) ≡ tt`
-- holds definitionally on the trivial `_+_ := λ _ _ → tt`.
trivialCostAlgebra : CostAlgebra Level.zero
trivialCostAlgebra = record
  { Cost        = ⊤
  ; zero        = tt
  ; _+_         = λ _ _ → tt
  ; _≤_         = λ _ _ → ⊤
  ; ≤-refl      = tt
  ; ≤-trans     = λ _ _ → tt
  ; +-identityˡ = λ _ → refl
  ; +-mono-≤    = λ _ _ → tt
  }

----------------------------------------------------------------------
-- Per-lemma proof-of-life pins for `Cost` at the trivial instance.
--
-- Top-level identifiers, one per `EchoCost.Cost` headline, with
-- `A := ⊤` and `B := ⊤` so each is a closed term that `Smoke.agda`
-- can enumerate in a `using` clause. Definitions use `=` (no
-- explicit type signature) so the original term's type is inferred
-- — which is exactly the typeability check the hygiene invariant
-- asks for.
----------------------------------------------------------------------

private
  open module CostT⊤ = Cost trivialCostAlgebra

cost-EchoC                   = EchoC
cost-intro                   = echo-cost-intro
cost-intro-≤                 = echo-cost-intro-≤
cost-relax                   = echo-cost-relax
cost-relax-zero              = echo-cost-relax-zero
cost-forget                  = echo-cost-forget
cost-compose                 = echo-cost-compose
cost-compose-mono            = echo-cost-compose-mono
cost-forget-compose-mono-A   = echo-cost-forget-compose-mono-A
