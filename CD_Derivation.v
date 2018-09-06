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

Require Export Formula.
Require Export Term.

Require Import Omega.
Require Import UserTactics.
Require Import Derivation.

(*Γ is well formed, if any term variable appears at most once*)
Inductive well_formed_environment : environment -> Prop :=
  | wfe_nil : well_formed_environment nil
  | wfe_cons : forall (x : label) (phi : formula') (Γ: environment), 
    Forall (fun '(y, _) => x <> y) Γ -> well_formed_environment Γ -> well_formed_environment ((x, phi ) :: Γ).

(*M is well formed, if it contains no unbound De Bruijn indices*)
Inductive well_formed_term (M : term) : Prop :=
  | wft_lc : lc 0 M -> well_formed_term M.

(*van Bakel, Strict Intersection Types for the Lambda Calculus, p. 11, 3.2 The Coppo-Dezani type assignment system*)
Inductive cd_derivation : environment -> term -> formula' -> Prop :=
  | cd_elim_cap : forall (Γ: environment) (x : label) (phi: formula') (t : formula), 
    well_formed_environment Γ -> 
    In (x, phi) Γ -> In t phi -> cd_derivation Γ (free_var x) (singleton t)
  | cd_intro_cap : forall (Γ: environment) (M : term) (phi: formula') (t : formula), 
    well_formed_environment Γ -> well_formed_term M ->
    Forall (fun t => cd_derivation Γ M (singleton t)) (cons' t phi) -> cd_derivation Γ M (cons' t phi)
  | cd_intro_arr : forall (Γ: environment) (M : term) (x : label) (phi : formula') (t : formula), 
    well_formed_environment ((x, phi) :: Γ) -> well_formed_term M ->
    cd_derivation ((x, phi) :: Γ) M (singleton t) -> cd_derivation Γ (term_abs (bind x 0 M)) (singleton (arr phi t))
  | cd_elim_arr : forall (Γ: environment) (M N : term) (phi : formula') (t : formula), 
    well_formed_environment Γ -> well_formed_term M -> well_formed_term N ->
    cd_derivation Γ M (singleton (arr phi t)) -> cd_derivation Γ N phi -> cd_derivation Γ (term_app M N) (singleton t).


(*strict version of the Coppo-Dezani type assignment system*)
Inductive strict_cd_derivation : environment -> term -> formula -> Prop :=
  | strict_cd_ax : forall (Γ: environment) (x : label) (phi: formula') (t : formula), 
    well_formed_environment Γ -> 
    In (x, phi) Γ -> In t phi -> strict_cd_derivation Γ (free_var x) t
  | strict_cd_intro_arr : forall (Γ: environment) (M : term) (x : label) (phi : formula') (t : formula), 
    well_formed_environment ((x, phi) :: Γ) -> well_formed_term M ->
    strict_cd_derivation ((x, phi) :: Γ) M t -> strict_cd_derivation Γ (term_abs (bind x 0 M)) (arr phi t)
  | strict_cd_elim_arr : forall (Γ: environment) (M N : term) (phi : formula') (t : formula), 
    well_formed_environment Γ -> well_formed_term M -> well_formed_term N ->
    strict_cd_derivation Γ M (arr phi t) -> Forall (strict_cd_derivation Γ N) phi -> strict_cd_derivation Γ (term_app M N) t.


Lemma cd_derivation_soundness : forall (Γ: environment) (M : term) (t : formula),
   cd_derivation Γ M (singleton t) -> strict_cd_derivation Γ M t.
Proof.
move => Γ M t.
have [m H_m] := exists_term_depth M.

move : Γ M t H_m.
apply (lt_wf_ind m).
move => {m} m IH.

move => Γ; case.

1-2: intros; gimme cd_derivation; inversion; eauto using strict_cd_derivation.

intros M N; intros; gimme cd_derivation; inversion.
gimme term_depth; inversion.
match goal with [m' : nat |- _] => rename m' into m end.

gimme cd_derivation where arr; move /IH.
move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => ?.
apply : strict_cd_elim_arr; try eassumption.
gimme cd_derivation.
move : IH. move /(_ _ _ Γ N _ ltac:(eassumption)). move /(_ ltac:(omega)).
clear.
case : phi; intros.
(do_last 2 constructor); auto.

gimme cd_derivation; inversion.
apply : Forall_impl; last eassumption; auto.


move => M ?; inversion; inversion.
apply : strict_cd_intro_arr; try assumption.
gimme term_depth. move /bind_depth => ?.
apply : IH; try eassumption; omega.
Qed.


Lemma cd_derivation_completeness : forall (Γ: environment) (M : term) (t : formula),
   strict_cd_derivation Γ M t -> cd_derivation Γ M (singleton t).
Proof.
move => Γ M t.
have [m H_m] := exists_term_depth M.

move : Γ M t H_m.
apply (lt_wf_ind m).
move => {m} m IH.

move => Γ; case.

1-2: intros; gimme strict_cd_derivation; inversion; eauto using cd_derivation.

intros M N; intros; gimme strict_cd_derivation; inversion.
gimme term_depth; inversion.
match goal with [m' : nat |- _] => rename m' into m end.

gimme strict_cd_derivation where arr; move /IH.
move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => ?.
apply : cd_elim_arr; try eassumption.
gimme Forall. move /(_ m ltac:(omega) Γ N _ ltac:(assumption)): IH.
revert dependent phi; case.

intros; gimme Forall; inversion; auto.
intros. apply : cd_intro_cap; eauto.
apply : Forall_impl; last eassumption; eauto.

move => M ?; inversion; inversion.
apply : cd_intro_arr; try assumption.
gimme term_depth. move /bind_depth => ?.
apply : IH; try eassumption; omega.
Qed.


Lemma strict_cd_derivation_completeness : forall (n : nat) (Γ: environment) (M : term) (t : formula), 
  well_formed_environment Γ -> derivation n Γ M t -> strict_cd_derivation Γ M t.
Proof.
move => n.
apply (lt_wf_ind n).
move => {n} n IH.
intros; gimme derivation; inversion.

apply : strict_cd_ax; eassumption.

{(*abs*)
match goal with [M' : term |- _] => rename M' into M end.
have := exists_fresh M Γ; move => [x [? ?]].
gimme where instantiate. 
move /(_ x) => HD.
move /derivation_lc /wft_lc : (HD) => ?.

erewrite <- (bind_instantiate 0 (M:=M)); try eassumption.
apply : strict_cd_intro_arr; auto.
by constructor.

apply : IH; last eassumption; first omega.
by constructor.
}

{(*app*)
apply : strict_cd_elim_arr => //.

gimme derivation; move /derivation_lc; by constructor.

gimme Forall; move /forall_exists_in_formula' => [s [? ?]].
gimme derivation; move /derivation_lc; by constructor.

apply : (IH); last eassumption; first omega; auto.

gimme Forall.
rewrite ? Forall_forall.

move => Hds s ?.
gimme where derivation; move /(_ s ltac:(auto)) /IH.
nip; [omega | auto].
}
Qed.


Theorem strict_cd_derivation_soundness : forall (Γ: environment) (M : term) (t : formula), 
  strict_cd_derivation Γ M t ->
  exists (n : nat), derivation n Γ M t.
Proof.
intros until 0.
have [m H_m] := exists_term_depth M.
move : Γ M t H_m.
apply (lt_wf_ind m).
move => {m} m IH; intros until 0.
inversion; inversion.

{(*case var*)
exists 0; apply : ax; eassumption.
}

{(*case app*)
move : (IH).
move /(_ n ltac:(omega) Γ _ _ _ ltac:(eassumption)).
move /(_ ltac:(assumption)).
match goal with [_ : Forall (strict_cd_derivation _ ?N') _ |- _] => rename N' into N end.
match goal with [_ : strict_cd_derivation _ _ (arr ?phi' _) |- _] => rename phi' into phi end.

have : exists (n : nat), Forall (derivation n Γ N) phi.
{(*show that N is uniformly typable wrt. depth*)
gimme Forall.
gimme term_depth where N => HN.
move / (_ n ltac:(omega) Γ N _ HN) : IH.
clear => IH.
gimme formula'; elim.

move => s; inversion.
gimme strict_cd_derivation; move /IH => [? ?].
eexists; do_last 2 constructor. eassumption.

move => s phi IH'; inversion.
gimme strict_cd_derivation; move /IH => [n1 ?].
gimme Forall; move /IH' => [n2 ?].
eexists (n1+n2); constructor.

apply : derivation_relax_depth; eassumption + omega.
apply : Forall_impl; last eassumption.
intros; apply : derivation_relax_depth; eassumption + omega.
}

clear => [[n1 ?] [n2 ?]].
exists (S (n1+n2)).
apply : elim_arr.
apply : derivation_relax_depth; eassumption + omega.
apply : Forall_impl; last eassumption.
intros; apply : derivation_relax_depth; eassumption + omega.
}


{(*case abs*)
gimme strict_cd_derivation.
match goal with [n' : nat |- _] => rename n' into n end.
move /IH; move /(_ n ltac:(omega)).

nip; first (apply : bind_depth; eassumption).
move => [n' ?].
gimme well_formed_environment; inversion.
exists (S n').
apply : fresh_abstraction_bind; auto.
}
Qed.


Lemma strict_cd_derivation_has_well_formed_environment: forall (Γ: environment) (M : term) (t : formula), 
  strict_cd_derivation Γ M t -> well_formed_environment Γ.
Proof.
intros until 0; inversion => //.
gimme well_formed_environment; by inversion.
Qed.


(*typing environments may be arbitrarily permuted or extended as long as well-formedness is preserved*)
Theorem cd_weakening : forall (Γ Γ': environment) (M: term) (t: formula), 
  cd_derivation Γ M t -> well_formed_environment Γ' -> (forall (p : label * formula'), In p Γ -> In p Γ') -> cd_derivation Γ' M t.
Proof.
intros; gimme cd_derivation.
move /cd_derivation_soundness.
move /strict_cd_derivation_soundness => [n].
move /weakening. move /(_ _ ltac:(eassumption)).
move /strict_cd_derivation_completeness. move /(_ ltac:(assumption)).
apply /cd_derivation_completeness.
Qed.

