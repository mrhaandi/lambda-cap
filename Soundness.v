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

(*only s_rule can be used deriving a type with two parameters for a normal form*)
Lemma two_params_rule : forall (rs : list rule) (bound n i: nat) (N : term) (phi psi : formula') (s : formula),
  head_form N -> 
  derivation n (Γ_all rs bound i) N (arr phi (arr psi s)) ->
  (exists (i : nat) (r : rule) (e : nat), In (i, r) (indexed 0 rs) /\ N = free_var (x_rule i) /\ 
    (phi = isl \/ phi = isr \/ phi = bullet) /\ s = symbol e).
Proof.
move => rs bound n i.
apply (lt_wf_ind n).
move => {n} n IH; intros until 0. 
inversion; inversion.
{
gimme In where Γ_all.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).

match goal with [H : rule |- _] => rename H into r end.
revert dependent r; case; case => ? ?; case => ? ?.
intro.
autorewrite with in_formula'.
firstorder (subst; try done).
1-3: gimme @eq; case; intros; subst.
1-3: (do 3 eexists); firstorder eassumption.
}
(*use IH*)
exfalso.
gimme derivation. move /IH. 
move /(_ ltac:(omega) ltac:(assumption)).
move => [? [? [? [? [? [? ?]]]]]]. 
done.
Qed.


Lemma invert_isl : forall (rs : list rule) (N : term) (bound n i : nat), 
  normal_form N -> derivation n (Γ_all rs bound i) N isl -> In i (seq 0 bound) /\ N = free_var (y_pos i).
Proof.
intros until 0; case; last (intros; gimme derivation; inversion).
move => {N} N.
case.
{ (*actual case*)
move => x; inversion.
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
1: match goal with [_ : In ?x (seq 0 bound) |- _ ] => rename x into j end.
2: match goal with [_ : In ?x (seq 0 bound) |- _ ] => rename x into j end.

all: gimme @eq.
all: have : i = j \/ i = 1 + j \/ (i < j ∨ 1 + j < i) by omega.
all: case; last case.
all: intro; do ? inspect_eqb; inversion.
all: by subst.
}

intros; gimme derivation; inversion.
move => {N} N N2.
case.
{ (*one argument case*)
intros; exfalso; do 2 (gimme derivation; inversion).
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
}
intros; do 2 (gimme derivation; inversion).
intros; exfalso; 
do 2 (gimme derivation; inversion).
gimme derivation; move /two_params_rule.
nip; first auto.
firstorder done.
Qed.

Lemma invert_isr : forall (rs : list rule) (N : term) (bound n i : nat), 
  normal_form N -> derivation n (Γ_all rs bound i) N isr -> exists (j : nat), In j (seq 0 bound) /\ i = 1 + j /\ N = free_var (y_pos j).
Proof.
intros until 0; case; last (intros; gimme derivation; inversion).
move => {N} N.
case.
{ (*actual case*)
move => x; inversion.
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).

match goal with [_ : In ?x (seq 0 bound) |- _ ] => rename x into j end.

all: gimme @eq.
all: have : i = j \/ i = 1 + j \/ (i < j ∨ 1 + j < i) by omega.
all: case; last case.
all: intro; do ? inspect_eqb; inversion.
eauto.
}
intros; gimme derivation; inversion.
move => {N} N N2.
case.
{ (*one argument case*)
intros; exfalso; do 2 (gimme derivation; inversion).
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
}
intros; do 2 (gimme derivation; inversion).
intros; exfalso; 
do 2 (gimme derivation; inversion).
gimme derivation; move /two_params_rule.
nip; first auto.
firstorder done.
Qed.


Lemma invert_bullet : forall (rs : list rule) (N : term) (bound n i : nat), 
  normal_form N -> derivation n (Γ_all rs bound i) N bullet -> exists (j : nat), In j (seq 0 bound) /\  (i < j \/ 1+j < i) /\ N = free_var (y_pos j).
Proof.
intros until 0; case; last (intros; gimme derivation; inversion).
move => {N} N.
case.
{ (*actual case*)
move => x; inversion.
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).

match goal with [_ : In ?x (seq 0 bound) |- _ ] => rename x into j end.

all: gimme @eq.
all: have : i = j \/ i = 1 + j \/ (i < j ∨ 1 + j < i) by omega.
all: case; last case.
all: intro; do ? inspect_eqb; inversion.
eauto.
}
intros; gimme derivation; inversion.
move => {N} N N2.
case.
{ (*one argument case*)
intros; exfalso; do 2 (gimme derivation; inversion).
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
}
intros; do 2 (gimme derivation; inversion).
intros; exfalso; 
do 2 (gimme derivation; inversion).
gimme derivation; move /two_params_rule.
nip; first auto.
firstorder done.
Qed.

(*a symbol is derived only using x_rule or x_1*)
Lemma term_1 : forall (rs : list rule) (n bound e : nat) (N : term),
  normal_form N -> 
  derivation n (Γ_all rs bound 0) N (symbol e) -> 
  (exists (i j : nat) (r : rule) (M : term), 
    In (i, r) (indexed 0 rs) /\ In j (seq 0 bound) /\
    N = term_app (term_app (free_var (x_rule i)) (free_var (y_pos j))) M)
  \/ (N = free_var x_1).
Proof.
intros until 0.
case; last (intros; gimme derivation; inversion).
move => {N} N.
case.
{ (*N = x_1*)
move => {N} x.
inversion.
right.
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
gimme @eq.
match goal with [|- context[if ?P then _ else _]] => case : P; inversion end.
}
intros until 0; by inversion.

move => {N} N N2.
case.
{ (*x N1 not possible*)
intros; exfalso.
do 2 (gimme derivation; inversion).
gimme where Γ_all.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
}
{ (*head is bound*)
intros; do 2 (gimme derivation; inversion).
}
{ (*actual case M N1 N2*)

move => {N} N N1.
intros.
left. 
do 2 (gimme derivation; inversion).
gimme derivation. move /two_params_rule.
nip; auto.
move => [i [r [e' [? [? [? ?]]]]]].
have : exists j, In j (seq 0 bound) /\ N1 = free_var (y_pos j).
{
gimme or.
case; last case.
all: intro; subst; gimme Forall; inversion.
all: gimme derivation.
1: move /invert_isl.
2: move /invert_isr.
3: move /invert_bullet.
all: nip; first auto.
eauto.
1-2: move => [? [? [? ?]]]; eauto.
}

move => [j [? ?]].
subst.

do 4 eexists.
eauto.
}
Qed.


Lemma dollar_not_in_Γ_all : forall (rs : list rule) (x : label) (phi : formula') (bound : nat),
  @In formula dollar phi -> In (x, phi) (Γ_all rs bound (1 + bound)) -> False.
Proof.
intros until 0 => ?.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula); clear.
all: try (gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (try done).
gimme where dollar.
match goal with [|- context[if ?P then _ else _]] => case : P; first inversion end.
match goal with [|- context[if ?P then _ else _]] => case : P; inversion end.
Qed.


Lemma triangle_not_in_Γ_all : forall (rs : list rule) (x : label) (phi : formula') (bound : nat),
  @In formula triangle phi -> In (x, phi) (Γ_all rs 0 0) -> False.
Proof.
intros until 0 => ?.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula); clear.
all: try (gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (try done).
Qed.

(*dollar is derived only by x_0 and x_star*)
Lemma term_shape_dollar : forall (rs : list rule) (n bound : nat) (N : term),
  normal_form N -> 
  derivation n (Γ_all rs bound (1 + bound)) N dollar -> 
    (exists (N' : term), normal_form N' /\ N = term_app (free_var x_0) N') \/
    (exists (N' : term), normal_form (term_abs N') /\ N = term_app (free_var x_star) (term_abs N')).
Proof.
intros until 0.
case; last (move => ? ?; inversion). (*N is not an abstraction*)
move => {N} N.
case.
{
move => x; inversion.
exfalso.
apply : dollar_not_in_Γ_all; eauto.
}
(*head cannot be bound*)
intros until 0; inversion.
move => {N} N N'.
case.
{
move => x HN'; inversion.
gimme derivation; inversion.
gimme In; gimme In; move => HIn1 HIn2.
move : HIn1.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
gimme @eq; case; intro; subst.
right.
do 2 (gimme Forall; inversion).
gimme derivation; inversion; eauto; exfalso.

{
gimme In where Γ_all.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
}

{
gimme derivation. move /two_params_rule.
nip.
gimme normal_form; inversion.
by gimme head_form; inversion.
clear; firstorder (subst; try done).
}
}

intros; exfalso. do 2 (gimme derivation; inversion). (*head cannt be bound*)
intros; exfalso.
do 2 (gimme derivation; inversion).
(*head cannot have two arguments because types are too short*)
gimme derivation. move /two_params_rule. 
nip; first auto.
firstorder done.
Qed.


Lemma extend_Γ_lr_lt : forall (bound i : nat), i < bound ->
  Γ_lr (1+bound) i = Γ_lr bound i ++ [(y_pos bound, (bullet : formula'))].
Proof.
move => bound i H. rewrite /Γ_lr /s_pos.
autorewrite with seq.
do ? inspect_eqb.
f_equal.
Qed.

Lemma extend_Γ_lr0 : forall (bound : nat), 
  Γ_lr (1+bound) bound = Γ_lr bound bound ++ [(y_pos bound, (isl : formula'))].
Proof.
move => bound. rewrite /Γ_lr /s_pos.
autorewrite with seq.
do ? inspect_eqb.
f_equal.
Qed.


Lemma extend_Γ_lr1 : forall (bound : nat), 
  Γ_lr (1+bound) (1+bound) = Γ_lr bound (1+bound) ++ [(y_pos bound, (isr : formula'))].
Proof.
move => bound. rewrite /Γ_lr /s_pos.
autorewrite with seq.
do ? inspect_eqb.
f_equal.
Qed.


Lemma extend_Γ_lr2 : forall (bound : nat), 
  Γ_lr (1+bound) (2+bound) = Γ_lr bound (1+bound) ++ [(y_pos bound, (bullet : formula'))].
Proof.
move => bound. rewrite /Γ_lr /s_pos.
autorewrite with seq.
do ? inspect_eqb.
f_equal.

set indices := (seq 0 bound).
move Heq : (bound) => bound'.
have : bound <= bound' by omega.
subst indices.
move : bound {Heq} bound'.

elim; first reflexivity.
move => bound IH bound' H.
autorewrite with seq.

f_equal.
apply IH; omega.
do ? inspect_eqb.
reflexivity.
Qed.


Lemma invert_forall_x_0 : forall (rs : list rule) (n bound: nat) (N : term),
  Forall (fun (Γi : environment) => derivation n Γi (term_app (free_var x_0) N) star) 
    (map (Γ_all rs bound) (seq 0 bound))
  -> Forall (fun (Γi : environment) => derivation (Nat.pred n) Γi N (symbol 0)) 
    (map (Γ_all rs bound) (seq 0 bound)).
Proof.
intros until 0.
rewrite ? Forall_forall.
move => HDs Γ H.
move /(_ Γ H) : HDs.
gimme In; rewrite in_map_iff.
move => [i [? ?]]; subst.
inversion; gimme derivation; inversion.
gimme In; gimme In; autorewrite with in_x_Γ; move => ->.
(do_last 3 case); try done.
case; intro; subst.
gimme Forall; by inversion.
Qed.

(*if triangle is inhabited in (Γ_init ++ Γ_step rs), then hash, dollar is inhabited in (Γ_all rs 0 0)*)
Lemma soundness_init : forall (rs : list rule) (n : nat) (N : term),
  normal_form N ->
  derivation n (Γ_init ++ Γ_step rs) N triangle ->
  exists (n' : nat) (N' : term), normal_form N' /\
  derivation n' (Γ_all rs 0 0) N' hash /\
  derivation n' (Γ_all rs 0 0) N' dollar.
Proof.
intros until 0.

have : (Γ_init ++ Γ_step rs) = Γ_all rs 0 0 by reflexivity.
move => ->.

case; last (move => ? ?; inversion). (*N is not an abstraction*)
move => {N} N.
case.
{
move => x; inversion.
exfalso.
apply : triangle_not_in_Γ_all; eauto.
}
(*head cannot be bound*)
intros until 0; inversion.
move => {N} N N'.
case.
{
(*actual case*)
move => x HN'; inversion.
gimme derivation; inversion.
gimme In; gimme In; move => HIn1 HIn2.
move : HIn1.
autorewrite with lookup_Γ.
firstorder (subst; try done).
all: gimme (@In formula).
all: try (clear; gimme rule; case; case => ? ?; case => ? ?).
all: autorewrite with in_formula'.
all: firstorder (subst; try done).
gimme @eq; case; intro; subst.
do 2 (gimme Forall; inversion).
eauto.
}

intros; exfalso. do 2 (gimme derivation; inversion). (*head cannot be bound*)
intros; exfalso.
do 2 (gimme derivation; inversion).
(*head cannot have two arguments because types are too short*)
gimme derivation. move /two_params_rule. 
nip; first auto.
firstorder done.
Qed.

(*if stars, hash, dollar is inhabited in (Γ_all rs bound [0 .. 1+bound]), then 0 is inhabited in (Γ_all rs bound [0 .. bound'])*)
Lemma soundness_expand : forall (rs : list rule) (n bound : nat) (N : term),
  normal_form N ->
  Forall (fun Γi => derivation n Γi N star) (map (Γ_all rs bound) (seq 0 bound)) ->
  derivation n (Γ_all rs bound bound) N hash ->
  derivation n (Γ_all rs bound (1+bound)) N dollar ->
  exists (n' bound' : nat) (N' : term),
  normal_form N' /\
  Forall (fun Γi => derivation n' Γi N' (symbol 0)) (map (Γ_all rs bound') (seq 0 (1+bound'))).
Proof.
move => rs n.
apply (lt_wf_ind n).
move => {n} n IH bound N HN HDs HDN1 HDN2.
move /term_shape_dollar : (HDN2). nip; auto.
case.
{ (*x_0 is used*)
move => [N' [HN' ?]]; subst N; clear HN.
gimme Forall; move /invert_forall_x_0.
move => HDs.
exists (Nat.pred n), bound, N'.
split; auto.
autorewrite with seq; split; auto.
(* hash <- 0 *)
move : HDN1; inversion; gimme derivation; inversion.
gimme In; gimme In; autorewrite with in_x_Γ; move => ->.
(do_last 3 case); try done.
case; intro; subst.
gimme Forall; by inversion.
}

(*x_star is used*)
move => [N' [HN' ?]]; subst N; clear HN.
move : HDN2; inversion.
gimme derivation; inversion.
gimme In; gimme In; autorewrite with in_x_Γ; move => ->.
case; first done.
case; first done.
case; last done.
case; intros; subst.
do 3 (gimme Forall; inversion).
do 2 (gimme derivation; inversion).
gimme where derivation; move /(_ (y_pos bound)).
gimme where derivation; move /(_ (y_pos bound)).
(*show that shape context is extended by 1*)
move /(weakening (Γ':=Γ_init ++ Γ_lr (1+bound) (2+bound) ++ Γ_step rs)).
nip; first (rewrite extend_Γ_lr2; list_inclusion).
move => HN'1.
move /(weakening (Γ':=Γ_init ++ Γ_lr (1+bound) (1+bound) ++ Γ_step rs)).
nip; first (rewrite extend_Γ_lr1; list_inclusion).
move => HN'2.
apply : IH.
5: exact HN'1.
all: try (omega + assumption).
(*instantiate N' is in normal form*)
apply instantiate_normal_form.
gimme normal_form; inversion; done + (gimme head_form; inversion).
(*show Forall Γi |- ? : star*)
autorewrite with seq.
split.
{
gimme Forall; clear.
rewrite ? Forall_forall.
move => Hds Γ'.
rewrite ? in_map_iff.
move => [i [? ?]]; subst.
move /(_ (Γ_all rs bound i)) : Hds.
rewrite ? in_map_iff.
nip; first eauto.
inversion.
gimme derivation; inversion.
gimme In; gimme In; autorewrite with in_x_Γ; move => ->.

case; last (case; case; try done).
case; intros; subst.
do ? (gimme Forall; inversion).
gimme derivation; inversion.
gimme where derivation; move /(_ (y_pos bound)).
move /weakening. apply.
gimme In; move /in_seq => [? ?].
rewrite /Γ_all.
rewrite extend_Γ_lr_lt; try omega.
list_inclusion.
}
{
(*bound : hash <- star*)
move : HDN1; clear.
inversion.
gimme derivation; inversion.
gimme In; gimme In; autorewrite with in_x_Γ; move => ->.
case; first done.
case; last (intuition done).
case; intro; subst.
do ? (gimme Forall; inversion).
gimme derivation; inversion.
gimme where derivation; move /(_ (y_pos bound)).
move /weakening.
apply.
rewrite /Γ_all.
rewrite extend_Γ_lr0. list_inclusion.
}
Qed.


Lemma invert_derivation_y_pos_lt : forall rs n bound i j s, derivation n (Γ_all rs bound i) (free_var (y_pos j)) s -> i < j -> s = bullet.
Proof.
intros until 0.
inversion => ?.
gimme In where Γ_all.
autorewrite with lookup_Γ.
rewrite /y_pos.
firstorder (subst; try done).
gimme (@eq label).
case; intro; subst.
gimme (@In formula).
case => //.
by (do ? inspect_eqb).
Qed.


Lemma invert_derivation_y_pos_gt : forall rs n bound i j s, derivation n (Γ_all rs bound i) (free_var (y_pos j)) s -> i > 1 + j -> s = bullet.
Proof.
intros until 0.
inversion => ?.
gimme In where Γ_all.
autorewrite with lookup_Γ.
rewrite /y_pos.
firstorder (subst; try done).
gimme (@eq label).
case; intro; subst.
gimme (@In formula).
case => //.
by (do ? inspect_eqb).
Qed.


Lemma invert_derivation_y_pos_isl : forall rs n bound j s, derivation n (Γ_all rs bound j) (free_var (y_pos j)) s -> s = isl.
Proof.
intros until 0.
inversion.
gimme In where Γ_all.
autorewrite with lookup_Γ.
rewrite /y_pos.
firstorder (subst; try done).
gimme (@eq label).
case; intro; subst.
gimme (@In formula).
case => //.
by (do ? inspect_eqb).
Qed.


Lemma invert_derivation_y_pos_isr : forall rs n bound j s, derivation n (Γ_all rs bound (S j)) (free_var (y_pos j)) s -> s = isr.
Proof.
intros until 0.
inversion.
gimme In where Γ_all.
autorewrite with lookup_Γ.
rewrite /y_pos.
firstorder (subst; try done).
gimme (@eq label).
case; intro; subst.
gimme (@In formula).
case => //.
by (do ? inspect_eqb).
Qed.


Lemma get_s_rule_bullet : forall (rs : list rule) (r : rule) (phi psi : formula') (a : nat), 
  In (arr phi (arr psi (symbol a))) (s_rule rs r) -> In (atom bullet) phi -> phi = bullet /\ psi = symbol a.
Proof.
intros until 0.
case : r.
case => ? ?. case => ? ?.
autorewrite with in_formula'.
firstorder.
all: gimme @eq; case; intros; subst; try done.
all: gimme In; inversion; try done.
Qed.


Lemma get_s_rule_isl : forall (rs : list rule) (a' a b c d : nat) (phi psi : formula'), 
  In (arr phi (arr psi (symbol a'))) (s_rule rs ((a,b),(c,d))) -> In (atom isl) phi -> phi = isl /\ psi = symbol c /\ a' = a.
Proof.
intros until 0.
autorewrite with in_formula'.
firstorder.
all: gimme @eq; case; intros; subst; try done.
all: gimme In; inversion; try done.
Qed.


Lemma get_s_rule_isr : forall (rs : list rule) (a' a b c d : nat) (phi psi : formula'), 
  In (arr phi (arr psi (symbol a'))) (s_rule rs ((a,b),(c,d))) -> In (atom isr) phi -> phi = isr /\ psi = symbol d /\ a' = b.
Proof.
intros until 0.
autorewrite with in_formula'.
firstorder.
all: gimme @eq; case; intros; subst; try done.
all: gimme In; inversion; try done.
Qed.

(*if [a_0 .. a_bound] is inhabited in (Γ_all rs bound [0 .. bound], then a_0..a_bound rewrites to 1..1 *)
Lemma soundness_step : forall (rs : list rule) (n bound : nat) (N : term) (v : list nat),
  normal_form N ->
  length v = 1 + bound ->
  Forall (fun '(i, a) => derivation n (Γ_all rs bound i) N (symbol a)) (indexed 0 v) ->
  rewrites_to rs v (map (fun _ => 1) v).
Proof.
move => rs n.
apply (lt_wf_ind n).
move => {n} n IH bound N v HN Hv HDs.

have : exists (e : nat), derivation n (Γ_all rs bound 0) N (symbol e).
revert dependent v.
case; first (cbn; intros; done).
intros; gimme Forall; inversion. eexists; eassumption.

move => [e ?].
gimme derivation. move /term_1.
nip; auto.
case.
{
move => [i [j [r [M [? [Hj ?]]]]]].
subst N.
move /in_seq : (Hj) => [_ ?].

have : 1 + j < length v by omega.
move /split_word => [v1 [v2 [a [b [? Hv1]]]]].
subst v.
gimme Forall.
rewrite -> indexed_app.
rewrite /indexed -/indexed Forall_app Hv1.
rewrite <- plus_n_O.
move => [?].
move /Forall_cons=> [?].
move /Forall_cons=> [?] ?.
do ? (gimme derivation where term_app; inversion).
do ? (gimme derivation where free_var; inversion).

(*show that arguments at j, 1+j positions are isl and isr*)
gimme Forall where (y_pos j). 
move /forall_exists_in_formula' => [sl [?]].
move /invert_derivation_y_pos_isl.
intro; subst sl.
gimme Forall where (y_pos j).
move /forall_exists_in_formula' => [sr [?]].
move /invert_derivation_y_pos_isr.
intro; subst sr.

gimme In where Γ_all.
gimme In where Γ_all.
autorewrite with lookup_Γ.
firstorder (subst; try done).
do 2 (gimme (@eq label); case).
intros; subst.
gimme In. move /(in_indexed_eq).
move /(_ _ ltac:(eassumption)); intro; subst.
gimme In. move /(in_indexed_eq).
move /(_ _ ltac:(eassumption)); intro; subst.
have : exists (a' b' c' d' : nat), r = ((a',b'),(c',d')).
clear; case : r.
case => ? ?; case => ? ?; eauto.
move => [a' [b' [c' [d' ?]]]]; subst r.

(*show isl rewrites a' to c'*)
gimme In where a.
move /get_s_rule_isl.
nip; first auto.
move => [? [? ?]]; subst.

(*show isr rewrites b' to d'*)
gimme In where b.
move /get_s_rule_isr.
nip; first auto.
move => [? [? ?]]; subst.

gimme In where rs; move /in_indexed_in.
move => ?.
apply : (ssts_step ltac:(eassumption)).
have : (map (λ _ : nat, 1) (v1 ++ a' :: b' :: v2)) = (map (λ _ : nat, 1) (v1 ++ c' :: d' :: v2)) by rewrite ? map_app.
move => ->.
eapply (IH (S n)); first omega.

gimme normal_form; inversion.
gimme head_form; inversion; eassumption.

rewrite <- Hv.
by rewrite ? app_length.

(*show derivability of (v1 ++ c' :: d' :: v2)*)
rewrite -> indexed_app.
rewrite /indexed -/indexed.
rewrite <- plus_n_O.
apply Forall_app.
split.
{ (*derivability of v1*)
gimme Forall where (indexed 0 v1).
rewrite ? Forall_forall.
move => HDs [i a] Hia.
move /(_ (i, a) Hia) : HDs; inversion.
do 2 (gimme derivation; inversion).
gimme In where x_rule.
autorewrite with lookup_Γ.
firstorder (subst; try done).
gimme Forall where y_pos.
move /forall_exists_in_formula' => [s [?]].

move /invert_derivation_y_pos_lt.
nip. gimme (In (i, a)). move /in_indexed_bounds; intros; omega.
intro; subst.
gimme In where a.
move /get_s_rule_bullet.
nip; auto.
move => [? ?]; subst.
gimme Forall; by inversion.
}
(*derivability of c'*)
constructor.
gimme Forall where c'.
inversion; assumption.
(*derivability of d'*)
constructor.
gimme Forall where d'.
inversion; assumption.

{ (*derivability of v2*)
gimme Forall where v2.
rewrite ? Forall_forall.
move => HDs [i a] Hia.
move /(_ (i, a) Hia) : HDs; inversion.
do 2 (gimme derivation; inversion).
gimme In where x_rule.
autorewrite with lookup_Γ.
firstorder (subst; try done).
gimme Forall where y_pos.
move /forall_exists_in_formula' => [s [?]].

move /invert_derivation_y_pos_gt.
nip. gimme (In (i, a)). move /in_indexed_bounds; intros; omega.
intro; subst.
gimme In where a.
move /get_s_rule_bullet.
nip; auto.
move => [? ?]; subst.
gimme Forall; by inversion.
}

} (*end of inductive case*)
clear Hv.
intro; subst.
suff : v = (map (λ _ : nat, 1) v).
move => <-. apply ssts_refl.
gimme Forall; clear.
move : {1}(0) => m.
elim : v m; first auto.
move => a v IH m.
rewrite /indexed -/indexed.
move /Forall_cons => [HD HDs].
cbn.
f_equal; last eauto.
{
gimme derivation; inversion.
gimme In; gimme In.
autorewrite with lookup_Γ.
firstorder (subst; try done).
gimme In; inversion; last done.
gimme (@eq formula); by case.
}
Qed.

(*if triangle is inhabited in (Γ_init ++ Γ_step rs), then 0..0 rewrites to 1..1*)
Theorem soundness : forall (rs : list rule) (n : nat) (N : term),
  normal_form N ->
  derivation n (Γ_init ++ Γ_step rs) N triangle ->
  exists (m : nat), rewrites_to rs (repeat 0 (1+m)) (repeat 1 (1+m)).
Proof.
intros.
gimme derivation.
move /soundness_init. nip; first done.
clear. move => [n [N [? [?]]]].
have : (Γ_all rs 0 0) = (Γ_all rs 0 1) by reflexivity.
move => ->.
move /soundness_expand.
do 4 (nip; first auto).
cbn; auto.
clear.
move => [n [bound [N [? ?]]]].
exists bound.
gimme normal_form; move /(soundness_step (n := n) (bound := bound) (rs := rs) (v := (repeat 0 (1 + bound)))).
have ? := repeat_length.
nip; first (cbn; auto).

nip.
{ (*show that derivations are equavalent*)
gimme Forall.
clear.
move : {2 4}(0) => m.
move : (Γ_all rs bound) => Γ.
elim : bound m.
cbn.
intro; inversion.
constructor; auto.

move => bound IH m.

have : (map Γ (seq m (1 + S bound))) = 
  (Γ m) :: (map Γ (seq (1+m) (1 + bound))) by reflexivity.
have : (indexed m (repeat 0 (1 + S bound))) = (m, 0) :: (indexed (1+m) (repeat 0 (1 + bound))) by reflexivity.
move => -> ->.

move /Forall_cons => [? ?].
constructor; eauto.
}

have : (map (λ _ : nat, 1) (repeat 0 (1 + bound))) = (repeat 1 (1 + bound)).
clear; elim: bound; first auto.
cbn; intros; f_equal; auto.

congruence.
Qed.