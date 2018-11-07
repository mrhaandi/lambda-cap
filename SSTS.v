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

Require Import Seq.

Require Import Omega.

Require Import ListFacts.
Require Import UserTactics.
Require Import MiscFacts.


(*rewriting ab => cd*)
Definition rule : Set := ((nat*nat)*(nat*nat)).

(*SSTS rewriting relation*)
Inductive rewrites_to (rs : list rule) : list nat -> list nat -> Prop :=
  | ssts_refl : forall (v : list nat), rewrites_to rs v v
  | ssts_step : forall (a b c d : nat) (v1 v2 w : list nat), In ((a,b),(c,d)) rs -> 
    rewrites_to rs (v1 ++ (c :: d :: v2)) w -> rewrites_to rs (v1 ++ (a :: b :: v2)) w.

(*symbols 0, 1 always present*)
Fixpoint get_symbol_bound (rs : list rule) := 
  match rs with
  | nil => 2
  | (cons ((a,b),(c,d)) rs) => 1 + a + b + c + d + get_symbol_bound rs
  end.

Lemma one_lt_symbol_bound : forall (rs : list rule), 1 < get_symbol_bound rs.
Proof.
elim; cbn; first omega.
case; case => ? ?; case => ? ?.
intros; omega.
Qed.

Lemma split_word : forall (v : list nat) (i : nat), 
  1 + i < length v -> 
  exists (v1 v2 : list nat) (a b : nat), v = v1 ++ (a :: b :: v2) /\ length v1 = i.
Proof.
intros * => Hv.
have := nth_split v.
move /(_ i 0 ltac:(omega)).
move : (nth i v 0) => a.
move => [v1 [w [? ?]]].
subst v.

move : Hv.
rewrite app_length; cbn => ?.
have ? : length w > 0 by omega.
revert dependent w.
case; first (cbn; intros; omega).
move => b v2 Hv _.
do ? eexists; auto.
Qed.


Lemma rule_symbol_bound : forall (rs : list rule) (a b c d : nat), In (a, b, (c, d)) rs -> a + b + c + d < get_symbol_bound rs.
Proof.
elim.
done.
case; case => a' b'; case => c' d'.
move => rs IH a b c d.
inversion.
gimme @eq; case; intros; subst.
rewrite /get_symbol_bound; omega.

rewrite /get_symbol_bound -/get_symbol_bound.
suff : a + b + c + d < get_symbol_bound rs by intros; omega.
auto.
Qed.


