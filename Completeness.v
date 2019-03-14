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

Require Import ListFacts.
Require Import UserTactics.

Require Import Derivation.
Require Import Encoding.

(*if v rewrites to 1..1, then N is typed by 1 in Γ_all rs bound i for all i*)
Lemma completeness_step : forall (rs : list rule) (bound : nat)  (v : list nat),
  Forall (fun a => a < get_symbol_bound rs) v ->
  rewrites_to rs v (map (fun _ => 1) v) ->
  length v = 1 + bound ->
  exists (n : nat) (N : term),
  normal_form N /\
  Forall (fun '(i, a) => derivation (1+n) (Γ_all rs bound i) N (symbol a)) (indexed 0 v) /\
  derivation (1+n) (Γ_all rs bound (1 + bound)) N (symbol 1).
Proof.
intros * => Hv.
move Hw : (map (λ _ : nat, 1) v) => w.
move => Hvw.
elim : Hvw Hw Hv.
{
clear; move => w; intros.
exists 0, (free_var x_1).
do_last 2 split.
do 2 constructor.

rewrite Forall_forall.
move => [i a] /in_indexed_in.
rewrite <- Hw.
rewrite in_map_iff. move => [? [? ?]]; subst.

all: apply : ax.
by rewrite in_x_1_eq.
by constructor.

by rewrite in_x_1_eq.
by constructor.
}
clear.
move => a b c d v1 v2 w ? Hw IH.
intros; subst.
move : IH.
nip; first (rewrite ? map_app; by cbn).
nip.
gimme In; move /rule_symbol_bound => ?. 
gimme Forall.
rewrite ? Forall_app => [[?]].
inversion; gimme Forall; inversion.
split; auto.
constructor. omega.
constructor. omega.
auto.

nip; first (gimme where length; move => <-; rewrite ? app_length; by cbn).
move => [n [N [? [? ?]]]].
gimme In; move /in_in_indexed. move/(_ 0) => [i ?].
exists (S n), (term_app (term_app (free_var (x_rule i)) (free_var (y_pos (length v1)))) N).

have ? : length v1 < bound.
gimme where length; rewrite app_length; cbn; intros; omega.

do_last 2 split.

do ? (assumption + constructor).
{
gimme Forall; rewrite ? indexed_app.
rewrite <- ? plus_n_O.
rewrite ? Forall_app; move => [? ?].

split.
{ (*v1 case*)
rewrite Forall_forall.
move => [j a'] ?.
apply : elim_arr.
apply : elim_arr.
have ? : In (arr bullet (arr (symbol a') (symbol a'))) (s_rule rs ((a, b), (c, d))).
apply : in_s_rule_bullet.
gimme In; move /in_indexed_in => ?.
gimme Forall where get_symbol_bound.
rewrite Forall_app.
move => [H' _]. move : H'.
rewrite Forall_forall.
move /(_ _ ltac:(eassumption)). apply.

apply : ax; try eassumption.
rewrite in_x_rule_eq; eauto.

constructor; last constructor.
gimme In. move /in_indexed_bounds => [? ?].
apply : ax.
rewrite in_y_pos_eq in_seq.
split; [omega | reflexivity].
by constructor; by do ? inspect_eqb.

constructor; last constructor.
gimme Forall where (indexed 0 v1).
move /Forall_forall; move /(_ _ ltac:(eassumption)); apply.
}
rewrite /indexed -/indexed.
do 2 (gimme Forall where v2; inversion).

constructor; last constructor.
{ (*isl case*)
apply : elim_arr.
apply : elim_arr.
apply : ax.
rewrite in_x_rule_eq; eauto.
constructor; reflexivity.

constructor; last done.
apply : ax.
rewrite in_y_pos_eq in_seq.
split; [omega | reflexivity].
constructor; by inspect_eqb.

by constructor.
}

{ (*isr case*)
apply : elim_arr.
apply : elim_arr.
apply : ax.
rewrite in_x_rule_eq; eauto.
rewrite /s_rule.
autorewrite with list'.

firstorder reflexivity.

constructor; last done.
apply : ax.
rewrite in_y_pos_eq in_seq.
split; [omega | reflexivity].
by constructor; by do ? inspect_eqb.

by constructor.
}

{ (*v2 case*)
rewrite Forall_forall.
move => [j a'] ?.
apply : elim_arr.
apply : elim_arr.
apply : ax.
rewrite in_x_rule_eq; eauto.

suff : In (arr bullet (arr (symbol a') (symbol a'))) (s_rule rs ((a, b), (c, d))) by apply.

apply : in_s_rule_bullet.
gimme In; move /in_indexed_in => ?.
gimme Forall where get_symbol_bound.
rewrite Forall_app.
move => [_]; inversion.
gimme Forall; inversion.
gimme Forall; rewrite Forall_forall.
by move /(_ _ ltac:(eassumption)).

constructor; last done.
gimme In. move /in_indexed_bounds => [? ?].
apply : ax.
rewrite in_y_pos_eq in_seq.
split; [omega | reflexivity].
by constructor; by do ? inspect_eqb.

constructor; last done.
gimme Forall.
move /Forall_forall; move /(_ _ ltac:(eassumption)); apply.
}
}

{ (*derive 1 at 1+bound*)
apply : elim_arr. apply : elim_arr. apply : ax.
rewrite in_x_rule_eq.
eauto.
apply : in_s_rule_bullet.
apply one_lt_symbol_bound.

constructor => //.
apply : ax.
rewrite in_y_pos_eq.
rewrite in_seq.
intuition omega.

constructor. by do ? inspect_eqb.

constructor => //.
}
Qed.

(*0 is inhabited in Γ_all rs bound i for all i, then stars, hash, dollar is inhabited in Γ_all rs bound [0..bound-1, bound, bound+1]*)
Lemma completeness_star : forall (rs : list rule) (N : term) (n bound : nat), normal_form N -> 
  Forall (fun '(i, a) => derivation n (Γ_all rs bound i) N (symbol a)) (indexed 0 (repeat 0 (S bound))) ->
  derivation n (Γ_all rs bound (1+bound)) N (symbol 1) -> 
  exists (n' : nat) (N' : term), 
  normal_form N' /\
  Forall (fun i => derivation n' (Γ_all rs bound i) N' star) (seq 0 bound) /\
  derivation n' (Γ_all rs bound bound) N' hash /\
  derivation n' (Γ_all rs bound (1+bound)) N' dollar.
Proof.
intros.
exists (S n), (term_app (free_var x_0) N).
do_last 3 split.

do 2 constructor; auto; constructor.

gimme Forall; rewrite ? Forall_forall.
move => ? i ?.
gimme where repeat. move /(_ (i, 0)).

nip. gimme In; clear; elim : bound => //.
move => bound IH.

gimme where In.
autorewrite with seq.
rewrite ? in_app_iff; cbn.
rewrite ? app_length.
rewrite ? repeat_length.
move => ?; case => ?; firstorder (subst => //).

{ (*derive star*)
move => ?.
apply : elim_arr. apply : ax.
by rewrite in_x_0_eq.
by constructor.

by constructor.
}

{ (*derive hash*)
apply : elim_arr. apply : ax.
by rewrite in_x_0_eq.
apply in_cons.
by constructor.

constructor => //.

gimme Forall. autorewrite with seq.
rewrite ? app_length.
rewrite ? repeat_length.
rewrite ? Forall_app. move => [_]; by inversion.
}

{ (*derive dollar*)
apply : elim_arr. apply : ax.
by rewrite in_x_0_eq.
do 2 (apply in_cons).
by constructor.

constructor => //.
}
Qed.


Lemma shift_s_pos_gt : forall bound n, n > 0 -> map (λ j : nat, (y_pos j, s_pos (n + S bound) j)) (seq 0 bound) =
  map (λ j : nat, (y_pos j, s_pos (n + bound) j)) (seq 0 bound).
Proof.
elim => //.
move => bound IH n ?.
autorewrite with seq.
f_equal.
have : (n + S (S bound)) = ((S n) + (S bound)) by omega.
have : (n + (S bound)) = ((S n) + bound) by omega.
move => -> ->. eauto.

rewrite /s_pos.
by do ? inspect_eqb.
Qed.


Lemma y_pos_fresh : forall (rs : list rule) (bound i: nat), 
  fresh_in_environment (y_pos bound) (Γ_all rs bound i).
Proof.
intros.
rewrite /fresh_in_environment.
rewrite Forall_forall => [[x phi]].
autorewrite with lookup_Γ.
firstorder (subst; try done).
gimme In; rewrite in_seq => ?.
case; intro; omega.
Qed.

(*if stars, hash, dollar is inhabited in Γ_all rs bound [0..bound-1, bound, bound+1], then hash, dollar is inhabited in Γ_all rs 0 [0, 1]*)
Lemma completeness_expand : forall (rs : list rule) (bound n : nat) (N : term),
  normal_form N ->
  Forall (fun (i : nat) => derivation n (Γ_all rs bound i) N star) (seq 0 bound) ->
  derivation n (Γ_all rs bound bound) N hash ->
  derivation n (Γ_all rs bound (1 + bound)) N dollar ->
  exists (n' : nat) (N' : term), 
    normal_form N' /\
    derivation n' (Γ_all rs 0 0) N' hash /\ 
    derivation n' (Γ_all rs 0 1) N' dollar.
Proof.
move => rs.
elim.
cbn; intros; do 2 eexists; eauto.

move => bound IH n N; intros.

apply : (IH (2+n) (term_app (free_var x_star) (term_abs (bind (y_pos bound) 0 N)))); first last.

{ (*show dollar*)
apply : elim_arr.
apply : ax.
by rewrite in_x_star_eq.
do 2 (apply in_cons). by constructor.

do_last 2 constructor => //.

gimme derivation where hash.

move /(weakening (Γ':=(y_pos bound, s_pos (1+bound) bound) :: Γ_all rs bound (S bound))).
nip.
rewrite /Γ_all /Γ_lr.
autorewrite with seq. list_inclusion.

move /fresh_abstraction_bind.
nip; first (apply y_pos_fresh).
rewrite /s_pos. do ? inspect_eqb.
apply.

gimme derivation where dollar.

move /(weakening (Γ':=(y_pos bound, s_pos (1+S bound) bound) :: Γ_all rs bound (S bound))).
nip.
rewrite /Γ_all /Γ_lr.
autorewrite with seq.
rewrite shift_s_pos_gt; auto.
list_inclusion.

move /fresh_abstraction_bind.
nip; first (apply y_pos_fresh).
rewrite /s_pos. do ? inspect_eqb.
apply.
}


{ (*show hash*)
apply : elim_arr.
apply : ax.
by rewrite in_x_star_eq.
apply in_cons. by constructor.

constructor => //.

gimme Forall.
autorewrite with seq.
move => [_].

move /(weakening (Γ':=(y_pos bound, s_pos bound bound) :: Γ_all rs bound bound)).
nip.
rewrite /Γ_all /Γ_lr.
autorewrite with seq. list_inclusion.

move /fresh_abstraction_bind.
nip; first (apply y_pos_fresh).
rewrite /s_pos. do ? inspect_eqb.
apply.
}

{ (*show star*)
gimme Forall.
autorewrite with seq.
move => [? _]; gimme Forall.
rewrite ? Forall_forall.
move => HDs i Hi.
move /in_seq : (Hi) => ?.

apply : elim_arr.
apply : ax.
by rewrite in_x_star_eq.
by constructor.

constructor => //.

move /(_ _ Hi) : HDs.
move /(weakening (Γ':=(y_pos bound, s_pos i bound) :: Γ_all rs bound i)).
nip.
rewrite /Γ_all /Γ_lr.
autorewrite with seq. list_inclusion.

move /fresh_abstraction_bind.
nip; first (apply y_pos_fresh).
rewrite /s_pos. do ? inspect_eqb.
apply.
}

do 2 constructor.
constructor.
apply : normal_abs.
by apply normal_bind.
Qed.

(*hash, dollar is inhabited in Γ_all rs 0 [0, 1], then triangle is inhabited in (Γ_init ++ Γ_step rs)*)
Lemma completeness_init : forall (rs : list rule) (n : nat) (N : term),
  normal_form N -> 
  derivation n (Γ_all rs 0 0) N hash ->
  derivation n (Γ_all rs 0 1) N dollar ->
  exists (n' : nat) (N' : term), normal_form N' /\ derivation n' (Γ_init ++ Γ_step rs) N' triangle.
Proof.
intros.
exists (S n), (term_app (free_var x_init) N).
split.
eauto using normal_form, head_form.


have : Γ_init ++ Γ_step rs = Γ_all rs 0 0 by reflexivity.
move => ->.

apply : elim_arr.
apply : ax.

by autorewrite with in_x_Γ.
by constructor.

by do_last 3 constructor.
Qed.

(*if 0..0 rewrites to 1..1, then triangle is inhabited in (Γ_init ++ Γ_step rs)*)
Theorem completeness : forall (rs : list rule) (m : nat),
  rewrites_to rs (repeat 0 (1+m)) (repeat 1 (1+m)) ->
  exists (n : nat) (N : term), normal_form N /\ derivation n (Γ_init ++ Γ_step rs) N triangle.
Proof.
intros *.
have : (repeat 1 (1 + m)) = (map (fun _ => 1) (repeat 0 (1 + m))).
elim : m; first done; cbn.
intros; f_equal; auto.

move => ->.
move /completeness_step.
move /(_ m).

nip. (*0 < symbol bound*)
rewrite Forall_forall => a.
move /(@repeat_spec nat); intros; subst.
have := one_lt_symbol_bound rs.
intros; omega.

nip; first (apply repeat_length).

move => [n [N [? [? ?]]]].
gimme Forall.
move /completeness_star.
do 2 (nip; first done).

clear.
move => [n [N [? [? [? ?]]]]].
gimme Forall. move /completeness_expand.
do 3 (nip; first auto).
firstorder.
gimme derivation where dollar. move /completeness_init.
auto.
Qed.
