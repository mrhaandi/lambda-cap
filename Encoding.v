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

Require Import Formula.
Require Import Term.

Require Import Omega.
Require Import Psatz.

Require Import ListFacts.
Require Import UserTactics.


Require Export SSTS.
Require Import Derivation.

Require Import StrictDerivation.

(*rewrite In (x, phi) (Γ_all rs bound i) to a firstorder formula*)
Create HintDb lookup_Γ.
(*rewrite In (x, phi) (Γ_all rs bound i) where x is known to particular restrictions on phi*)
Create HintDb in_x_Γ.
(*rewrite In t phi where phi is known to particular restrictions on t*)
Create HintDb in_formula'.


Definition bullet : label := (0,0).
Definition star : label := (0,1).
(*indicates second symbol*)
Definition hash : label := (0,2).
(*indicates first symbol*)
Definition dollar : label := (0,3).
(*indicates very first split, used once*)
Definition triangle : label := (0,4).

(*encodes elements of the alphabet including 0 and 1*)
Definition symbol (x : nat) : label := (1, x).

Definition isl : label := (2,0).
Definition isr : label := (2,1).

Definition s_init : formula' := arr [atom hash; atom dollar] triangle.

Definition s_star : formula' := 
  [arr [arr [atom bullet] star] star; arr [arr [atom isl] star] hash; arr [arr [atom isr] hash; arr [atom bullet] dollar] dollar].

Definition s_0 : formula' := 
  [arr [atom (symbol 0)] star; arr [atom (symbol 0)] hash; arr [atom (symbol 1)] dollar].


Definition s_1 : formula' := [atom (symbol 1)].


Definition s_id_rules (symbol_bound : nat) : list formula := 
  map (fun (a : nat) => (arr [atom bullet] (arr [atom (symbol a)] (symbol a)))) (seq 0 symbol_bound).


Definition s_rule (rs : list rule) (r : rule) : formula' := 
  match r with
  | ((x,y),(x',y')) => cons (arr [atom isl] (arr [atom (symbol x')] (symbol x))) 
      (cons (arr [atom isr] (arr [atom (symbol y')] (symbol y))) (s_id_rules (get_symbol_bound rs)))
  end.


Definition s_pos (i j : nat) : formula' := if i =? j then isl else (if i =? 1+j then isr else bullet).


Definition x_0 : label := (0, 0).
Definition x_1 : label := (0, 1).
Definition x_star : label := (0, 2).
Definition x_init : label := (0, 3).
Definition x_rule (i : nat) : label := (1, i).
(*bound to isl, isr, bullet*)
Definition y_pos (i : nat) : label := (2, i).

Fixpoint map_indexed (A B : Type) (f : nat -> A -> B) (start : nat) (l : list A) :=
  match l with
  | nil => nil
  | (cons a l) => cons (f start a) (map_indexed f (S start) l)
  end.


(*used for initialization, expansion, and termination*)
Definition Γ_init : environment := [(x_init, s_init); (x_star, s_star); (x_0, s_0); (x_1, s_1)].

(*used for rule transition*)
Definition Γ_step (rs : list rule) : environment := 
  map (fun '(i, r) => (x_rule i, s_rule rs r)) (indexed 0 rs).

(*information on 'neighboring' environments*)
Definition Γ_lr (bound : nat) (i : nat) : environment := map (fun j => (y_pos j, s_pos i j)) (seq 0 bound).

(*collection of all the above type environments*)
Definition Γ_all (rs : list rule) (bound i : nat) := 
  Γ_init ++ Γ_lr bound i ++ Γ_step rs.


Lemma lookup_Γ_all : forall (rs : list rule) (bound i : nat), Γ_all rs bound i = Γ_init ++ Γ_lr bound i ++ Γ_step rs .
Proof. reflexivity. Qed.


Lemma lookup_Γ_init : forall (x : label) (phi : formula'), 
  In (x, phi) Γ_init <-> (x = x_init /\ phi = s_init) \/ (x = x_star /\ phi = s_star) \/ (x = x_0 /\ phi = s_0) \/ (x = x_1 /\ phi = s_1).
Proof.
intros *.
split.
(do_last 4 case); case; firstorder auto.
firstorder (subst; list_element).
Qed.


Lemma lookup_Γ_step : forall (rs : list rule) (x : label) (phi : formula'), 
  In (x, phi) (Γ_step rs) <-> (fst x) = (fst (x_rule 0)) /\ (exists (i : nat) (r : rule), In (i, r) (indexed 0 rs) /\ x = x_rule i /\ phi = s_rule rs r).
Proof.
intros *.
rewrite /Γ_step in_map_iff.
split.
move => [[i r] [H ?]].
case : H. 
intros; subst; split; eauto.
firstorder (subst => //).
Qed.

Lemma lookup_Γ_lr : forall (bound i : nat) (x : label) (phi : formula'), 
  In (x, phi) (Γ_lr bound i) <-> (fst x) = (fst (y_pos 0)) /\ (exists (j : nat), In j (seq 0 bound) /\ x = y_pos j /\ phi = s_pos i j).
Proof.
intros *.
rewrite /Γ_lr in_map_iff.
split.
move => [j [H ?]]; case : H. 
intros; subst; eauto.
firstorder (subst => //).
Qed.


Hint Rewrite @lookup_Γ_all : lookup_Γ.
Hint Rewrite @lookup_Γ_init : lookup_Γ.
Hint Rewrite @lookup_Γ_step : lookup_Γ.
Hint Rewrite @lookup_Γ_lr : lookup_Γ.
Hint Rewrite @in_app_iff : lookup_Γ.

Lemma in_x_init_eq : forall (rs : list rule) (i bound : nat) (phi : formula'), 
  In (x_init, phi) (Γ_all rs bound i) <-> phi = s_init.
Proof.
intros; autorewrite with lookup_Γ.
firstorder (by subst).
Qed.

Lemma in_x_star_eq : forall (rs : list rule) (i bound : nat) (phi : formula'), 
  In (x_star, phi) (Γ_all rs bound i) <-> phi = s_star.
Proof.
intros; autorewrite with lookup_Γ.
firstorder (by subst).
Qed.

Lemma in_x_0_eq : forall (rs : list rule) (i bound : nat) (phi : formula'), 
  In (x_0, phi) (Γ_all rs bound i) <-> phi = s_0.
Proof.
intros; autorewrite with lookup_Γ.
firstorder (by subst).
Qed.

Lemma in_x_1_eq : forall (rs : list rule) (i bound : nat) (phi : formula'), 
  In (x_1, phi) (Γ_all rs bound i) <-> phi = s_1.
Proof.
intros; autorewrite with lookup_Γ.
firstorder (by subst).
Qed.


Lemma in_x_rule_eq : forall (rs : list rule) (i bound j : nat) (phi : formula'), 
  In (x_rule i, phi) (Γ_all rs bound j) <-> exists (r : rule), In (i, r) (indexed 0 rs) /\ phi = s_rule rs r.
Proof.
intros.
autorewrite with lookup_Γ.
firstorder (subst => //).
all: subst; try done.
gimme (@eq label); case.
intro; subst. eauto.
Qed.


Lemma in_y_pos_eq : forall (rs : list rule) (i bound j : nat) (phi : formula'), 
  In (y_pos j, phi) (Γ_all rs bound i) <-> In j (seq 0 bound) /\ phi = s_pos i j.
Proof.
intros.
autorewrite with lookup_Γ.
firstorder (subst => //).
all: gimme (@eq label); case; intros; by subst.
Qed.


Hint Rewrite in_x_init_eq : in_x_Γ.
Hint Rewrite in_x_star_eq : in_x_Γ.
Hint Rewrite in_x_0_eq : in_x_Γ.
Hint Rewrite in_x_1_eq : in_x_Γ.
Hint Rewrite in_x_rule_eq : in_x_Γ.
Hint Rewrite in_y_pos_eq : in_x_Γ.


Lemma in_s_init_iff : forall (t : formula), 
  In t s_init <-> 
    t = arr [atom hash; atom dollar] triangle.
Proof.
intros *.
split; first by inversion.

intro; subst; list_element.
Qed.

Lemma in_s_star_iff : forall (t : formula), 
  In t s_star <-> 
    t = arr [arr [atom bullet] star] star \/
    t = arr [arr [atom isl] star] hash \/
    t = arr [arr [atom isr] hash; arr [atom bullet] dollar] dollar.
Proof.
intros *.
split.

rewrite /s_star.
intro.
do 4 (gimme In; inversion; auto).

do 2 (case; first (intro; subst; list_element)).
intro; subst; list_element.
Qed.


Lemma in_s_0_iff : forall (t : formula), 
  In t s_0 <-> 
    t = arr [atom (symbol 0)] star \/
    t = arr [atom (symbol 0)] hash \/ 
    t = arr [atom (symbol 1)] dollar.
Proof.
intros *.
split.

rewrite /s_0.
intro.
do 4 (gimme In; inversion; auto).

do 2 (case; first (intro; subst; list_element)).
intro; subst; list_element.
Qed.



Lemma in_s_rule_iff : forall (t : formula) (rs : list rule) (r : rule), 
  In t (s_rule rs r) <-> 
    exists (a b c d : nat), r = ((a,b),(c,d)) /\
    (t = arr [atom isl] (arr [atom (symbol c)] (symbol a)) \/
    t = arr [atom isr] (arr [atom (symbol d)] (symbol b)) \/
    (exists (e : nat), t = arr [atom bullet] (arr [atom (symbol e)] (symbol e)) /\ e < get_symbol_bound rs)).
Proof.
intros *.
move : r => [[? ?][? ?]].
rewrite /s_rule.
cbn; rewrite /s_id_rules in_map_iff.
split.
{
intro; do 4 eexists; split; first done.
firstorder.
gimme In; rewrite in_seq; firstorder.
}
{
move => [? [? [? [?]]]].
case; case; intros; subst.
firstorder (subst; try done).

do 2 right.
eexists; rewrite in_seq.
firstorder omega.
}
Qed.


Lemma in_s_1_iff : forall (t : formula), 
  In t s_1 <-> t = symbol 1.
Proof. intros; split; [by inversion | intro; subst; list_element]. Qed.


Lemma in_s_pos_iff : forall (t : formula) (i j : nat), 
  In t (s_pos i j) <-> t = if i =? j then isl else (if i =? 1+j then isr else bullet).
Proof. intros; split; [by inversion | intro; subst; list_element]. Qed.


Hint Rewrite in_s_init_iff : in_formula'.
Hint Rewrite in_s_star_iff : in_formula'.
Hint Rewrite in_s_0_iff : in_formula'.
Hint Rewrite in_s_1_iff : in_formula'.
Hint Rewrite in_s_pos_iff : in_formula'.
Hint Rewrite in_s_rule_iff : in_formula'.


Lemma in_s_rule_bullet : forall (rs : list rule) (r : rule) (a : nat), 
  a < get_symbol_bound rs -> In (arr [atom bullet] (arr [atom (symbol a)] (symbol a))) (s_rule rs r).
Proof.
intros.
case : r; case => ? ?; case => ? ?.
apply /in_s_rule_iff.
do 4 eexists.
firstorder eauto.
Qed.


Lemma well_formed_Γ_step : forall (rs : list rule), well_formed_environment (Γ_step rs).
Proof.
rewrite /Γ_step.
move : (0) => n rs.
move : (s_rule rs) => f.
elim : rs n; cbn.
constructor.

move => r rs IH n.
constructor; last auto.
rewrite Forall_forall.
move => [x phi].
move /in_map_iff => [[n' r']].
case; case; intros; subst; case; intro; subst.
gimme In; move /in_indexed_bounds.
intros; omega.
Qed.


Lemma well_formed_Γ_all : forall (rs : list rule), well_formed_environment (Γ_init ++ Γ_step rs).
Proof.
intro; cbn.
(do_last 4 constructor); last apply well_formed_Γ_step.
all: do ? (match goal with [|- Forall _ (_ :: _)] => constructor; try done end).
all: rewrite Forall_forall; move => [x phi].
all: autorewrite with lookup_Γ.
all: firstorder (subst; try done).
Qed.


Lemma max_le_iff : forall n m l, Nat.max n m <= l <-> n <= l /\ m <= l.
Proof.
intros. lia.
Qed.

Lemma rank_environment_bound : forall (rs : list rule) (x : label) (phi : formula'), 
  In (x, phi) (Γ_init ++ Γ_step rs) -> rank_formula' phi <= 2.
Proof.
intros *.
autorewrite with lookup_Γ.
firstorder (subst; try done); cbn; try omega.

clear.
gimme rule; move => [[? ?] [? ?]].
rewrite /s_rule.
move : (get_symbol_bound rs) => m; clear.

cbn.
rewrite max_le_iff. split; last omega.
rewrite /s_id_rules.

move : {1 3}(0) => i.

elim : m i; cbn; first (intros; lia).
move => ? IH i.
rewrite max_le_iff. split; last omega.
move /(_ (S i)) : IH.
done.
Qed.
