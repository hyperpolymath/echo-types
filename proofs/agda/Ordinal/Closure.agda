{-# OPTIONS --safe --without-K #-}

-- Stage S0 / Milestone E3 of docs/buchholz-plan.adoc.
--
-- ℕ-staged closure family `C m t`: evidence that the ordinal term `t`
-- is generable at closure stage `m`. Closure is inductive on the
-- stage index `m : ℕ` and the term, with `psi β` admissible at stage
-- `m` when its argument `β` is already generable at some strictly
-- earlier stage `k < m`.
--
-- Headline lemma: `C-monotone` — increasing the stage index never
-- removes previously generable terms. This is the structural
-- theorem every subsequent `psi-notin-C` / least-gap proof leans on,
-- so it is the first proof we establish before any ψ-value is
-- even defined.

module Ordinal.Closure where

open import Data.Nat.Base using (ℕ; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)

open import Ordinal.Base using (OT; zero; omega; plus; psi)

-- Staged closure family. `C m t` reads as "t is generable at stage m".
--
-- The `c-psi` rule is the only rule that looks backwards: it requires
-- the argument β to have been generable at some strictly earlier stage
-- `k`. This is the seed of the Buchholz pattern: `ψ` at stage m can
-- only refer to things produced strictly before stage m.

data C : ℕ → OT → Set where
  c-zero  : ∀ {m} → C m zero
  c-omega : ∀ {m} → C m omega
  c-plus  : ∀ {m x y} → C m x → C m y → C m (plus x y)
  c-psi   : ∀ {m k β} → k < m → C k β → C m (psi β)

-- Headline lemma.
--
-- Proof by induction on the closure derivation. The `c-psi` case is
-- the only non-trivial one: the side condition `k < m` is pushed to
-- `k < n` by transitivity with `m ≤ n`, and the recursive argument
-- `C k β` is preserved verbatim (no recursion on it — it already
-- witnesses membership at the *same* earlier stage `k`).

C-monotone : ∀ {m n t} → m ≤ n → C m t → C n t
C-monotone _   c-zero             = c-zero
C-monotone _   c-omega            = c-omega
C-monotone m≤n (c-plus cx cy)     = c-plus (C-monotone m≤n cx) (C-monotone m≤n cy)
C-monotone m≤n (c-psi k<m ck)     = c-psi (≤-trans k<m m≤n) ck

-- Immediate consequence: closure is reflexive at every stage (every
-- derivation stays a derivation at the same stage). Added to exercise
-- the lemma rather than for novelty.

C-refl-stage : ∀ {m t} → C m t → C m t
C-refl-stage = C-monotone ≤-refl

-- A worked instance: `psi omega` is generable at stage 1 but not
-- constructively derivable at stage 0 under this closure — we can
-- only give the positive direction here. The negative direction
-- lives in Ordinal.PsiSimple once it is written.

psi-omega-at-1 : C 1 (psi omega)
psi-omega-at-1 = c-psi (s≤s z≤n) c-omega

-- And by monotonicity, it is generable at every larger stage.

psi-omega-at-2 : C 2 (psi omega)
psi-omega-at-2 = C-monotone (s≤s z≤n) psi-omega-at-1
