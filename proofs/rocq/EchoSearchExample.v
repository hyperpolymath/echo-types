(* SPDX-License-Identifier: MPL-2.0 *)
(* SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> *)

(* Rocq recheck leg (re-proved) of proofs/agda/EchoSearchExample.agda.

   PROOF-POLICY section 2: every Agda theory proof is rechecked in Rocq and
   Lean.  This file is a hand re-proof, not a Dedukti transport.  Each
   definition restates the Agda definition it mirrors, and each theorem
   restates the Agda headline of the same name.  The statement-by-statement
   correspondence, and the residual differences between the systems, are
   recorded in proofs/RECHECK-EchoSearchExample.adoc.

   Core library only (Init + the prelude); no Require, no axioms.  The
   closing `Print Assumptions` commands must report "Closed under the
   global context". *)

(* ---------------------------------------------------------------- *)
(* Echo.agda: Echo f y := Sigma (x : A), f x = y                     *)
(* ---------------------------------------------------------------- *)

Definition Echo {A B : Type} (f : A -> B) (y : B) : Type :=
  { x : A & f x = y }.

(* ---------------------------------------------------------------- *)
(* EchoSearch.agda                                                   *)
(* ---------------------------------------------------------------- *)

Definition SearchStrategy (A : Type) : Type := nat -> A.

(* EchoS enum f y n = Sigma k, (k < n) x (f (enum k) = y) *)
Definition EchoS {A B : Type}
  (enum : SearchStrategy A) (f : A -> B) (y : B) (n : nat) : Type :=
  { k : nat & ((k < n) * (f (enum k) = y))%type }.

Definition echo_search_forget {A B : Type}
  {enum : SearchStrategy A} {f : A -> B} {y : B} {n : nat}
  (s : EchoS enum f y n) : Echo f y :=
  match s with existT _ k (_, eq) => existT _ (enum k) eq end.

(* Agda's Dec, with yes / no. *)
Inductive Dec (P : Type) : Type :=
| yes : P -> Dec P
| no  : (P -> False) -> Dec P.
Arguments yes {P} _.
Arguments no  {P} _.

(* Decidable equality on nat, transparent so that the decider computes. *)
Definition nat_eq_dec : forall x y : nat, {x = y} + {x <> y}.
Proof. decide equality. Defined.

(* An index below `S n` is either below `n` or is `n` itself. *)
Lemma lt_succ_inv : forall k n, k < S n -> (k < n) + (k = n).
Proof.
  intros k n H. unfold lt in H. apply le_S_n in H.
  destruct (nat_eq_dec k n) as [e | ne]; [ right; exact e | left ].
  revert ne. induction H as [| m Hm IH]; intro ne.
  - exfalso. apply ne. reflexivity.
  - apply le_n_S. exact Hm.
Qed.

Lemma echo_search_bound_zero {A B : Type}
  (enum : SearchStrategy A) (f : A -> B) (y : B) :
  EchoS enum f y 0 -> False.
Proof. intros [k [H _]]. inversion H. Qed.

(* bounded-search-is-decidable: structural recursion on the budget; the
   successor step tests the new top index `n` FIRST, then recurses, as the
   Agda procedure does.  Defined (transparent) so it computes. *)
Fixpoint bounded_search_is_decidable {A B : Type}
  (deq : forall x y : B, {x = y} + {x <> y})
  (enum : SearchStrategy A) (f : A -> B) (y : B) (n : nat)
  : Dec (EchoS enum f y n) :=
  match n with
  | O => no (echo_search_bound_zero enum f y)
  | S m =>
      match deq (f (enum m)) y with
      | left e => yes (existT _ m (le_n (S m), e))
      | right ne =>
          match bounded_search_is_decidable deq enum f y m with
          | yes (existT _ k (klt, ek)) => yes (existT _ k (le_S _ _ klt, ek))
          | no below =>
              no (fun s =>
                    match s with
                    | existT _ k (klt, ek) =>
                        match lt_succ_inv k m klt with
                        | inl kltm => below (existT _ k (kltm, ek))
                        | inr keq =>
                            ne (eq_rect k (fun j => f (enum j) = y) ek m keq)
                        end
                    end)
          end
      end
  end.

(* ---------------------------------------------------------------- *)
(* EchoSearchExample.agda                                            *)
(* ---------------------------------------------------------------- *)

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S m => S (S (double m))
  end.

Definition countUp : SearchStrategy nat := fun k => k.

(* The hit is at step 3 < 4, where double 3 = 6 by computation. *)
Definition search_double_6 : EchoS countUp double 6 4 :=
  existT _ 3 (le_n 4, eq_refl).

(* The decider, run on this instance, computes to `yes` on exactly that
   witness. *)
Theorem search_double_6_decided :
  bounded_search_is_decidable nat_eq_dec countUp double 6 4
  = yes search_double_6.
Proof. reflexivity. Qed.

(* EchoCost.Cost at the step-count algebra (N, 0, +, <=): the instance
   unfolds to Sigma x, (f x = y) x (cost x <= c). *)
Definition EchoC {A B : Type}
  (cost : A -> nat) (c : nat) (f : A -> B) (y : B) : Type :=
  { x : A & ((f x = y) * (cost x <= c))%type }.

Definition search_steps : nat -> nat := S.

(* `k < n` is `S k <= n` on the nose, so the bridge is a re-pairing. *)
Definition count_up_search_to_cost {B : Type} {f : nat -> B} {y : B} {n : nat}
  (s : EchoS countUp f y n) : EchoC search_steps n f y :=
  match s with existT _ k (klt, eq) => existT _ k (eq, klt) end.

(* EchoDecidable: EchoDec f y := Dec (Echo f y). *)
Definition EchoDec {A B : Type} (f : A -> B) (y : B) : Type := Dec (Echo f y).

Definition search_to_dec {A B : Type}
  {enum : SearchStrategy A} {f : A -> B} {y : B} {n : nat}
  (s : EchoS enum f y n) : EchoDec f y :=
  yes (echo_search_forget s).

(* EchoAccess: the five access grades, the 15-pair Hasse order, CEcho and
   degrade-access, restated in full. *)
Inductive Access : Type := free | decidable | enum_ | feasible | infeasible.

Inductive le_a : Access -> Access -> Type :=
| free_free : le_a free free
| free_decidable : le_a free decidable
| free_enum : le_a free enum_
| free_feasible : le_a free feasible
| free_infeasible : le_a free infeasible
| decidable_decidable : le_a decidable decidable
| decidable_enum : le_a decidable enum_
| decidable_feasible : le_a decidable feasible
| decidable_infeasible : le_a decidable infeasible
| enum_enum : le_a enum_ enum_
| enum_feasible : le_a enum_ feasible
| enum_infeasible : le_a enum_ infeasible
| feasible_feasible : le_a feasible feasible
| feasible_infeasible : le_a feasible infeasible
| infeasible_infeasible : le_a infeasible infeasible.

Definition CEcho {A B : Type} (c : Access) (f : A -> B) (y : B) : Type :=
  match c with
  | free => Echo f y
  | decidable => EchoDec f y
  | enum_ | feasible | infeasible => unit
  end.

Definition degrade_access {A B : Type} {f : A -> B} {y : B}
  {c1 c2 : Access} (p : le_a c1 c2) : CEcho c1 f y -> CEcho c2 f y :=
  match p in le_a c1 c2 return CEcho c1 f y -> CEcho c2 f y with
  | free_free => fun e => e
  | free_decidable => fun e => yes e
  | free_enum => fun _ => tt
  | free_feasible => fun _ => tt
  | free_infeasible => fun _ => tt
  | decidable_decidable => fun d => d
  | decidable_enum => fun _ => tt
  | decidable_feasible => fun _ => tt
  | decidable_infeasible => fun _ => tt
  | enum_enum => fun e => e
  | enum_feasible => fun _ => tt
  | enum_infeasible => fun _ => tt
  | feasible_feasible => fun e => e
  | feasible_infeasible => fun _ => tt
  | infeasible_infeasible => fun e => e
  end.

(* The bridges fired on the concrete witness. *)
Definition search_as_echo : Echo double 6 := echo_search_forget search_double_6.
Definition search_as_cost : EchoC search_steps 4 double 6 :=
  count_up_search_to_cost search_double_6.
Definition search_as_dec : EchoDec double 6 := search_to_dec search_double_6.
Definition search_as_feasible : CEcho feasible double 6 :=
  degrade_access free_feasible search_as_echo.

(* Computational sanity: the bridges carry the witness 3. *)
Theorem search_as_echo_witness : projT1 search_as_echo = 3.
Proof. reflexivity. Qed.
Theorem search_as_cost_witness : projT1 search_as_cost = 3.
Proof. reflexivity. Qed.

Print Assumptions search_double_6_decided.
Print Assumptions search_as_echo.
Print Assumptions search_as_cost.
Print Assumptions search_as_dec.
Print Assumptions search_as_feasible.
Print Assumptions search_as_cost_witness.
