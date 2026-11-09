/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

Lean 4 recheck leg (re-proved) of proofs/agda/EchoSearchExample.agda.

PROOF-POLICY section 2: every Agda theory proof is rechecked in Rocq and
Lean, with no Mathlib.  This file is a hand re-proof in Lean core: no
imports beyond the prelude, no `sorry`, no new axioms.  Each definition
restates the Agda definition it mirrors, and each theorem the Agda headline
of the same name.  The statement correspondence and the residual
differences are recorded in proofs/RECHECK-EchoSearchExample.adoc.  The
closing `#print axioms` commands must report no axioms.
-/

namespace EchoSearchExample

universe u v

/-! Echo.agda: `Echo f y := Σ (x : A), f x ≡ y` -/
def Echo {A : Type u} {B : Type v} (f : A → B) (y : B) : Type u :=
  (x : A) ×' (f x = y)

/-! EchoSearch.agda -/
def SearchStrategy (A : Type u) : Type u := Nat → A

/-- `EchoS enum f y n = Σ k, (k < n) × (f (enum k) ≡ y)` -/
def EchoS {A : Type u} {B : Type v}
    (enum : SearchStrategy A) (f : A → B) (y : B) (n : Nat) : Type :=
  (k : Nat) ×' (k < n) ×' (f (enum k) = y)

def echoSearchForget {A : Type u} {B : Type v}
    {enum : SearchStrategy A} {f : A → B} {y : B} {n : Nat}
    (s : EchoS enum f y n) : Echo f y :=
  ⟨enum s.1, s.2.2⟩

/-- Agda's `Dec`, with `yes` / `no`. -/
inductive Dec (P : Sort u) : Sort (max 1 u) where
  | yes : P → Dec P
  | no : (P → False) → Dec P

theorem echoSearchBoundZero {A : Type u} {B : Type v}
    (enum : SearchStrategy A) (f : A → B) (y : B) :
    EchoS enum f y 0 → False :=
  fun s => Nat.not_lt_zero _ s.2.1

theorem ltSuccInv {k n : Nat} (h : k < n + 1) : k < n ∨ k = n :=
  Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h)

/-- `bounded-search-is-decidable`: structural recursion on the budget; the
successor step tests the new top index `n` FIRST, then recurses, as the
Agda procedure does. -/
def boundedSearchIsDecidable {A : Type u} {B : Type v}
    (deq : (x y : B) → Decidable (x = y))
    (enum : SearchStrategy A) (f : A → B) (y : B) :
    (n : Nat) → Dec (EchoS enum f y n)
  | 0 => Dec.no (echoSearchBoundZero enum f y)
  | m + 1 =>
    match deq (f (enum m)) y with
    | isTrue e => Dec.yes ⟨m, Nat.lt_succ_self m, e⟩
    | isFalse ne =>
      match boundedSearchIsDecidable deq enum f y m with
      | Dec.yes s => Dec.yes ⟨s.1, Nat.lt_succ_of_lt s.2.1, s.2.2⟩
      | Dec.no below =>
        Dec.no fun s =>
          match ltSuccInv s.2.1 with
          | Or.inl klt => below ⟨s.1, klt, s.2.2⟩
          | Or.inr keq => ne (keq ▸ s.2.2)

/-! EchoSearchExample.agda -/

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

def countUp : SearchStrategy Nat := fun k => k

/-- The hit is at step `3 < 4`, where `double 3 = 6` by computation. -/
def searchDouble6 : EchoS countUp double 6 4 :=
  ⟨3, by decide, rfl⟩

/-- The decider, run on this instance, computes to `yes` on exactly that
witness. -/
theorem searchDouble6Decided :
    boundedSearchIsDecidable (fun a b => Nat.decEq a b) countUp double 6 4
      = Dec.yes searchDouble6 := by
  rfl

/-- `EchoCost.Cost` at the step-count algebra `(ℕ, 0, +, ≤)`: the instance
unfolds to `Σ x, (f x ≡ y) × (cost x ≤ c)`. -/
def EchoC {A : Type u} {B : Type v}
    (cost : A → Nat) (c : Nat) (f : A → B) (y : B) : Type u :=
  (x : A) ×' (f x = y) ×' (cost x ≤ c)

def searchSteps : Nat → Nat := Nat.succ

/-- `k < n` is `k + 1 ≤ n` on the nose, so the bridge is a re-pairing. -/
def countUpSearchToCost {B : Type v} {f : Nat → B} {y : B} {n : Nat}
    (s : EchoS countUp f y n) : EchoC searchSteps n f y :=
  ⟨s.1, s.2.2, s.2.1⟩

/-- EchoDecidable: `EchoDec f y := Dec (Echo f y)`. -/
def EchoDec {A : Type u} {B : Type v} (f : A → B) (y : B) : Type u :=
  Dec (Echo f y)

def searchToDec {A : Type u} {B : Type v}
    {enum : SearchStrategy A} {f : A → B} {y : B} {n : Nat}
    (s : EchoS enum f y n) : EchoDec f y :=
  Dec.yes (echoSearchForget s)

/-! EchoAccess: the five grades, the 15-pair Hasse order, `CEcho` and
`degrade-access`, restated in full. -/

inductive Access where
  | free | decidable | enum | feasible | infeasible

inductive LeA : Access → Access → Type where
  | freeFree : LeA .free .free
  | freeDecidable : LeA .free .decidable
  | freeEnum : LeA .free .enum
  | freeFeasible : LeA .free .feasible
  | freeInfeasible : LeA .free .infeasible
  | decidableDecidable : LeA .decidable .decidable
  | decidableEnum : LeA .decidable .enum
  | decidableFeasible : LeA .decidable .feasible
  | decidableInfeasible : LeA .decidable .infeasible
  | enumEnum : LeA .enum .enum
  | enumFeasible : LeA .enum .feasible
  | enumInfeasible : LeA .enum .infeasible
  | feasibleFeasible : LeA .feasible .feasible
  | feasibleInfeasible : LeA .feasible .infeasible
  | infeasibleInfeasible : LeA .infeasible .infeasible

def CEcho {A : Type u} {B : Type v} : Access → (A → B) → B → Type u
  | .free, f, y => Echo f y
  | .decidable, f, y => EchoDec f y
  | .enum, _, _ => PUnit
  | .feasible, _, _ => PUnit
  | .infeasible, _, _ => PUnit

def degradeAccess {A : Type u} {B : Type v} {f : A → B} {y : B} :
    {c1 c2 : Access} → LeA c1 c2 → CEcho c1 f y → CEcho c2 f y
  | _, _, .freeFree, e => e
  | _, _, .freeDecidable, e => Dec.yes e
  | _, _, .freeEnum, _ => PUnit.unit
  | _, _, .freeFeasible, _ => PUnit.unit
  | _, _, .freeInfeasible, _ => PUnit.unit
  | _, _, .decidableDecidable, d => d
  | _, _, .decidableEnum, _ => PUnit.unit
  | _, _, .decidableFeasible, _ => PUnit.unit
  | _, _, .decidableInfeasible, _ => PUnit.unit
  | _, _, .enumEnum, e => e
  | _, _, .enumFeasible, _ => PUnit.unit
  | _, _, .enumInfeasible, _ => PUnit.unit
  | _, _, .feasibleFeasible, e => e
  | _, _, .feasibleInfeasible, _ => PUnit.unit
  | _, _, .infeasibleInfeasible, e => e

/-! The bridges fired on the concrete witness. -/
def searchAsEcho : Echo double 6 := echoSearchForget searchDouble6
def searchAsCost : EchoC searchSteps 4 double 6 := countUpSearchToCost searchDouble6
def searchAsDec : EchoDec double 6 := searchToDec searchDouble6
def searchAsFeasible : CEcho .feasible double 6 :=
  degradeAccess LeA.freeFeasible searchAsEcho

/-- Computational sanity: the bridges carry the witness `3`. -/
theorem searchAsEchoWitness : searchAsEcho.1 = 3 := rfl
theorem searchAsCostWitness : searchAsCost.1 = 3 := rfl

end EchoSearchExample

#print axioms EchoSearchExample.searchDouble6Decided
#print axioms EchoSearchExample.searchAsEcho
#print axioms EchoSearchExample.searchAsCost
#print axioms EchoSearchExample.searchAsDec
#print axioms EchoSearchExample.searchAsFeasible
#print axioms EchoSearchExample.searchAsCostWitness
