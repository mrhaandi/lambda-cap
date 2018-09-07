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

(*non-empty list*)
Inductive list' (A : Type) : Type :=
 | singleton : A -> list' A
 | cons' : A -> list' A -> list' A.


Inductive formula : Set :=
  | atom (a : label) : formula
  | arr (phi : list' formula) (t : formula) : formula.
(*intersections are non-empty in the Coppo-Dezani type assingnment system*)

(*used to define rank, lists with at least two elements are assigned at least the value 1*)
Definition rank_formula_aux' (f : formula -> nat) : list' formula -> nat :=
  fix maxby_rec' (l: list' formula) :=
    match l with
    | (singleton x) => f x
    | (cons' x xs) => Nat.max (maxby_rec' xs) (Nat.max (f x) 1)
    end.

Fixpoint rank_formula (t : formula) : nat :=
  match t with
  | (atom _) => 0
  | (arr phi s) => Nat.max (1 + rank_formula_aux' rank_formula phi) (rank_formula s)
  end.

Definition rank_formula' (phi : list' formula) := rank_formula_aux' rank_formula phi.


Fixpoint to_list (A : Type) (l : list' A) : list A :=
  match l with
  | (singleton a) => cons a nil
  | (cons' a l) => cons a (to_list l)
  end.

Fixpoint to_list' (A : Type) (a : A) (l : list A) : list' A :=
  match l with
  | nil => singleton a
  | (cons b l) => cons' a (to_list' b l)
  end.

Lemma to_list_inv : forall (A : Type) (a : A) (l : list A), to_list (to_list' a l) = a :: l.
Proof.
move => A a l.
elim : l a; cbn; auto.
intros; by f_equal.
Qed.

Coercion to_list : list' >-> list.

Lemma to_list_cons' : forall (T : Type) (a : T) (l : list' T), 
  to_list (cons' a l) = a :: to_list l.
Proof. intros; reflexivity. Qed.

(*Definition formula' : Set := list' formula.*)
Notation formula' := (list' formula).

Definition label_to_atom (a : label) : formula := atom a.
Definition formula_to_singleton (s : formula) : formula' := singleton s.

(*embedding formulae into singleton intersections*)
Coercion formula_to_singleton : formula >-> formula'.
Coercion label_to_atom : label >-> formula. 

Lemma forall_exists_in_formula' : forall (P : formula -> Prop) (phi : formula'), Forall P phi -> exists (s : formula), In s phi /\ P s.
Proof.
move => P; case.
move => s; inversion.
exists s; split; auto.
by constructor.
move => s phi; inversion.
exists s; split; auto.
by constructor.
Qed.

Hint Rewrite @to_list_inv @to_list_cons' : list'.
