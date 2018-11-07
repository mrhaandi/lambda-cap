(*common header begin*)
Require Import Utf8.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.

Require Import List.
Import ListNotations.
(*common header end*)

Require Export Label.
Require Import UserTactics.

(*rewrite to_list l*)
Create HintDb list'.

(*non-empty list
Inductive list' (A : Type) : Type :=
 | singleton : A -> list' A
 | cons' : A -> list' A -> list' A.
*)

Inductive formula : Set :=
  | atom (a : label) : formula
  | arr (phi : list formula) (t : formula) : formula.
(*intersections may be empty (omega) in the strict system*)

Definition formula' := list formula.


(*used to define rank, lists with at least two elements are assigned at least the value 1*)
Definition rank_formula_aux' (f : formula -> nat) : formula' -> nat :=
  fix maxby_rec' (l: list formula) :=
    match l with
    | [] => 1
    | [x] => f x
    | (cons x xs) => Nat.max (maxby_rec' xs) (Nat.max (f x) 1)
    end.

Fixpoint rank_formula (t : formula) : nat :=
  match t with
  | (atom _) => 0
  | (arr phi s) => Nat.max (1 + rank_formula_aux' rank_formula phi) (rank_formula s)
  end.

Definition rank_formula' (phi : formula') := rank_formula_aux' rank_formula phi.


Definition label_to_atom (a : label) : formula := atom a.
Definition formula_to_singleton (s : formula) : formula' := [s].

(*embedding formulae into singleton intersections*)
Coercion formula_to_singleton : formula >-> formula'.
Coercion label_to_atom : label >-> formula. 


Lemma forall_exists_in_formula' : forall (P : formula -> Prop) (phi : formula'), phi <> [] -> Forall P phi -> exists (s : formula), In s phi /\ P s.
Proof.
move => P; case.
done.
move => s ? _. inversion.
exists s; split; auto.
by constructor.
Qed.
