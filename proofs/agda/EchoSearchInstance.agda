{-# OPTIONS --safe --without-K #-}

-- A concrete instance for `EchoSearch` headlines, in the same spirit
-- as `EchoApproxInstance` for `EchoApprox.Approx`.
--
-- `EchoSearch` is parameterised in `A`, `B`, `enum`, `f`, `y`, `n`,
-- so to pin a closed term per headline lemma in `Smoke.agda` we
-- specialise to the trivial-on-⊤ choice:
--
--     A     := ⊤
--     B     := ⊤
--     enum  := λ _ → tt
--     f     := λ _ → tt
--     y     := tt
--     n     := 1
--
-- Every order / equality / bound obligation reduces to a one-step
-- inhabitant (`z<s : 0 < 1`, `refl : tt ≡ tt`, etc.). These pins are
-- proof-of-life that the parameterised lemmas typecheck at *some*
-- concrete instance — exactly the hygiene contract the working
-- rules of `CLAUDE.md` ask for. When a non-trivial enumerator
-- instance lands, the pins can be re-pointed.

module EchoSearchInstance where

open import Data.Unit.Base                        using (⊤; tt)
open import Data.Nat.Base                         using (ℕ; suc; zero; _<_; s≤s; z≤n)
open import Data.Nat.Properties                   using ()
open import Relation.Binary.PropositionalEquality using (refl)

open import Echo       using (Echo)
open import EchoSearch using
  ( SearchStrategy
  ; EchoS
  ; echo-search-intro
  ; echo-search-relax
  ; echo-search-forget
  ; echo-search-bound-zero
  ; echo-search-postcompose
  )

----------------------------------------------------------------------
-- The trivial enumerator on `⊤`
----------------------------------------------------------------------

trivialEnum : SearchStrategy ⊤
trivialEnum _ = tt

trivialF : ⊤ → ⊤
trivialF _ = tt

----------------------------------------------------------------------
-- Per-lemma proof-of-life pins.
--
-- Closed top-level identifiers (one per headline) so `Smoke.agda`
-- can enumerate them via a `using` clause. Definitions use `=` so
-- the original term's type is inferred — exactly the typeability
-- check the hygiene invariant asks for.
----------------------------------------------------------------------

-- Concrete bound-1 witness at the trivial instance. Uses `z<s` (the
-- smart constructor for `0 < n+1`) and `refl : tt ≡ tt`.
search-intro-⊤ : EchoS trivialEnum trivialF tt 1
search-intro-⊤ = echo-search-intro trivialEnum trivialF 0 1 (s≤s z≤n) refl

-- Bound monotonicity at the trivial instance: 1 ≤ 2 lifts the
-- bound-1 witness to a bound-2 witness.
search-relax-⊤ : EchoS trivialEnum trivialF tt 2
search-relax-⊤ = echo-search-relax trivialEnum trivialF (s≤s z≤n) search-intro-⊤

-- Forgetful projection at the trivial instance. The plain `Echo` for
-- `trivialF` at `tt` is trivially inhabited (every fibre is full).
-- The signature is given explicitly because `echo-search-forget`
-- takes all of its identifying parameters implicit, so type
-- inference at the use-site cannot resolve them from the witness.
search-forget-⊤ : Echo trivialF tt
search-forget-⊤ = echo-search-forget search-intro-⊤

-- Empty-budget vacuity at the trivial instance: bound 0 admits no
-- witness even on the trivial enumerator.
search-bound-zero-⊤ = echo-search-bound-zero trivialEnum trivialF tt

-- Post-composition at the trivial instance with `g := trivialF`.
-- The same step index, the same bound; the equality becomes
-- `cong trivialF refl ≡ refl`.
search-postcompose-⊤ = echo-search-postcompose trivialEnum trivialF trivialF search-intro-⊤
