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
Require Import ListFacts.
Require Import Derivation.

(*Γ is well formed, if any term variable appears at most once*)
Inductive well_formed_environment : environment -> Prop :=
  | wfe_nil : well_formed_environment nil
  | wfe_cons : forall (x : label) (phi : formula') (Γ: environment), 
    Forall (fun '(y, _) => x <> y) Γ -> well_formed_environment Γ -> well_formed_environment ((x, phi ) :: Γ).

(*M is well formed, if it contains no unbound De Bruijn indices*)
Definition well_formed_term (M : term) : Prop := lc 0 M.

(*van Bakel, Strict Intersection Types for the Lambda Calculus, p. 24, 5 The strict system*)
Inductive strict_derivation : environment -> term -> formula -> Prop :=
  | strict_elim_cap : forall (Γ: environment) (x : label) (phi: formula') (t : formula), 
    well_formed_environment Γ -> 
    In (x, phi) Γ -> In t phi -> strict_derivation Γ (free_var x) t
  | strict_intro_arr : forall (Γ: environment) (M : term) (x : label) (phi : formula') (t : formula), 
    well_formed_environment ((x, phi) :: Γ) -> well_formed_term M ->
    strict_derivation ((x, phi) :: Γ) M t -> strict_derivation Γ (term_abs (bind x 0 M)) (arr phi t)
  | strict_elim_arr : forall (Γ: environment) (M N : term) (phi : formula') (t : formula), 
    well_formed_environment Γ -> well_formed_term M -> well_formed_term N ->
    strict_derivation Γ M (arr phi t) -> strict_derivation_cap Γ N phi -> strict_derivation Γ (term_app M N) t
with strict_derivation_cap : environment -> term -> formula' -> Prop :=
  | strict_intro_cap : forall (Γ: environment) (M : term) (phi: formula'), 
    well_formed_environment Γ -> well_formed_term M ->
    Forall (strict_derivation Γ M) phi -> strict_derivation_cap Γ M phi.

Lemma strict_derivation_completeness : forall (n : nat) (Γ: environment) (M : term) (t : formula), 
  well_formed_environment Γ -> derivation n Γ M t -> strict_derivation Γ M t.
Proof.
elim /lt_wf_ind => n IH.
intros; gimme derivation; inversion.

apply : strict_elim_cap; eassumption.

{(*abs*)
match goal with [M' : term |- _] => rename M' into M end.
have := exists_fresh M Γ; move => [x [? ?]].
gimme where instantiate. 
move /(_ x) => HD.
move /derivation_lc : (HD) => ?.

erewrite <- (bind_instantiate 0 (M:=M)); try eassumption.
apply : strict_intro_arr; auto.
by constructor.

apply : IH; last eassumption; first omega.
by constructor.
}

{(*app*)
apply : strict_elim_arr; try trivial.

apply : derivation_lc; eassumption.

apply : (IH); last eassumption; first omega; auto.
apply : strict_intro_cap; auto. 
apply : Forall_impl; last eassumption.
eauto.
}
Qed.


Lemma strict_derivation_soundness : forall (Γ: environment) (M : term) (t : formula),
   strict_derivation Γ M t -> exists (n : nat), derivation n Γ M t.
Proof.
intros *.
have [m H_m] := exists_term_depth M.
move : m Γ M t H_m.
elim /lt_wf_ind.
move => m IH; intros *.
inversion; inversion.

{(*case var*)
exists 0; apply : ax; eassumption.
}


{(*case app*)
match goal with [phi' : formula' |- _] => rename phi' into phi end.
have : exists (n : nat), Forall (derivation n Γ N) phi.
{(*show that N is uniformly typable wrt. depth*)
gimme strict_derivation_cap; gimme strict_derivation => _.
inversion.
apply Forall_exists_monotone.

intros; apply : derivation_relax_depth; [eassumption | omega].

apply : Forall_impl; last eassumption.
intros. apply : IH; try eassumption; omega.
}

gimme strict_derivation; move /IH.
move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => [n1 ?] [n2 ?].
exists (S (n1+n2)).
apply : elim_arr.
apply : derivation_relax_depth; eassumption + omega.
apply : Forall_impl; last eassumption.
intros; apply : derivation_relax_depth; eassumption + omega.
done.
}


{(*case abs*)
gimme strict_derivation.
gimme term_depth.
move /bind_depth => ?.
move /IH. move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => [n' ?].
exists (S n').
gimme well_formed_environment; inversion.
apply : fresh_abstraction_bind; auto.
}
Qed.

(*typing environments may be arbitrarily permuted or extended as long as well-formedness is preserved*)
Theorem strict_weakening : forall (Γ Γ': environment) (M: term) (t: formula), 
  strict_derivation Γ M t -> well_formed_environment Γ' -> (forall (p : label * formula'), In p Γ -> In p Γ') -> strict_derivation Γ' M t.
Proof.
intros; gimme strict_derivation.
move /strict_derivation_soundness => [n].
move /weakening. move /(_ _ ltac:(eassumption)).
move /strict_derivation_completeness. 
auto.
Qed.

