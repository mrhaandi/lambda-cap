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


Lemma cd_derivation_completeness : forall (n : nat) (Γ: environment) (M : term) (t : formula), 
  well_formed_environment Γ -> derivation n Γ M t -> cd_derivation Γ M (singleton t).
Proof.
elim /lt_wf_ind => n IH.
intros; gimme derivation; inversion.

apply : cd_elim_cap; eassumption.

{(*abs*)
match goal with [M' : term |- _] => rename M' into M end.
have := exists_fresh M Γ; move => [x [? ?]].
gimme where instantiate. 
move /(_ x) => HD.
move /derivation_lc /wft_lc : (HD) => ?.

erewrite <- (bind_instantiate 0 (M:=M)); try eassumption.
apply : cd_intro_arr; auto.
by constructor.

apply : IH; last eassumption; first omega.
by constructor.
}

{(*app*)
apply : cd_elim_arr => //.

gimme derivation; move /derivation_lc; by constructor.

gimme Forall; move /forall_exists_in_formula' => [s [? ?]].
gimme derivation; move /derivation_lc; by constructor.

apply : (IH); last eassumption; first omega; auto.

gimme Forall; gimme derivation; move => _.
gimme formula'; case.

move => s; inversion. apply : IH; try eassumption; omega.

move => s phi ?.
apply : cd_intro_cap => //.
gimme Forall; inversion.
gimme derivation; move /derivation_lc. auto using well_formed_term.

apply : Forall_impl; last eassumption.
intros. apply : IH; try eassumption; omega.
}
Qed.


Lemma cd_derivation_soundness : forall (Γ: environment) (M : term) (t : formula),
   cd_derivation Γ M (singleton t) -> exists (n : nat), derivation n Γ M t.
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
gimme cd_derivation; gimme cd_derivation; move => _.
case : phi.

move => s.
move /IH. move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => [n' ?].
eexists; constructor; eauto.

move => s phi; inversion.
apply Forall_exists_monotone.

intros; apply : derivation_relax_depth; [eassumption | omega].

apply : Forall_impl; last eassumption.
intros. apply : IH; try eassumption; omega.
}

gimme cd_derivation where arr; move /IH.
move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => [n1 ?] [n2 ?].
exists (S (n1+n2)).
apply : elim_arr.
apply : derivation_relax_depth; eassumption + omega.
apply : Forall_impl; last eassumption.
intros; apply : derivation_relax_depth; eassumption + omega.
}


{(*case abs*)
gimme cd_derivation.
gimme term_depth.
move /bind_depth => ?.
move /IH. move /(_ _ _ ltac:(eassumption)). move /(_ ltac:(omega)) => [n' ?].
exists (S n').
gimme well_formed_environment; inversion.
apply : fresh_abstraction_bind; auto.
}
Qed.


(*typing environments may be arbitrarily permuted or extended as long as well-formedness is preserved*)
Theorem cd_weakening : forall (Γ Γ': environment) (M: term) (t: formula), 
  cd_derivation Γ M t -> well_formed_environment Γ' -> (forall (p : label * formula'), In p Γ -> In p Γ') -> cd_derivation Γ' M t.
Proof.
intros; gimme cd_derivation.
move /cd_derivation_soundness => [n].
move /weakening. move /(_ _ ltac:(eassumption)).
move /cd_derivation_completeness. 
auto.
Qed.

