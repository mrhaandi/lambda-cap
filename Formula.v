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

(*non-empty list*)
Inductive list' (A : Type) : Type :=
 | singleton : A -> list' A
 | cons' : A -> list' A -> list' A.

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
move => a l IH b.
by f_equal.
Qed.

Coercion to_list : list' >-> list.

Lemma in_cons' : forall (T : Type) (a b : T) (l : list' T), In a (cons' b l) <-> b = a \/ In a l.
Proof.
intros.
split.
apply in_inv.
case; intro.
subst.
apply in_eq.
apply in_cons; auto.
Qed.

Inductive formula : Set :=
  | atom (a : label) : formula
  | arr (phi : list' formula) (t : formula) : formula.
(*intersections are non-empty since s, phi...*)

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
