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

Require Import ListFacts.
Require Import UserTactics.
Require Import MiscFacts.

Definition environment : Set := list (label * formula').

Definition fresh_in_environment (x : label) (Γ : environment) := Forall (fun (e : label * formula') => let (y, _) := e in x <> y) Γ.

(*first paramater n contains an upper bound on the derivation depth*)
Inductive derivation : nat -> environment -> term -> formula → Prop :=
  | ax : forall (n : nat) (Γ: environment) (x : label) (phi: formula') (t : formula), 
    In (x, phi) Γ -> In t phi -> derivation n Γ (free_var x) t
  | intro_arr : forall (n : nat) (Γ: environment) (M : term) (phi : formula') (t : formula), 
    (forall (x : label), derivation n ((x, phi) :: Γ) (instantiate x 0 M) t) → derivation (S n) Γ (term_abs M) (arr phi t)
  | elim_arr : forall (n : nat) (Γ: environment) (M N : term) (phi : formula') (t : formula), 
    derivation n Γ M (arr phi t) → Forall (derivation n Γ N) phi → derivation (S n) Γ (term_app M N) t.

(*
Conjecture normalization : forall (m : nat) (Γ: environment) (M :term) (t: formula), 
  derivation m Γ M t → exists (n : nat) (N : term), normal_form N /\ derivation n Γ N t.
*)

(*environments may be extended or permuted*)
Theorem weakening : ∀ (n : nat) (Γ Γ': environment) (M: term) (t: formula), 
  derivation n Γ M t → (∀ (p : label * formula'), In p Γ → In p Γ') → derivation n Γ' M t.
Proof.
elim.
(*base case*)
intros until 0.
inversion.
move /(_ _ ltac:(eassumption)).
eauto using derivation.

move => n IH.
intros until 0; inversion.
move /(_ _ ltac:(eassumption)).
eauto using derivation.
move => H_in.
apply intro_arr.
move => x; apply : IH. eauto.
move => p.
move /(_ p) : H_in.
list_inclusion.

move => ?.
move /(_ Γ Γ' _ _ _ ltac:(eassumption)) : (IH).
move /(_ Γ Γ' _ _ ltac:(eassumption) ltac:(eassumption)) : IH.
intros.
apply : elim_arr; try eassumption.
gimme Forall; rewrite ? Forall_forall.
auto.
Qed.


Fixpoint term_label_bound (M : term) : nat :=
  match M with
  | (free_var (_, n)) => 1+n
  | (bound_var _) => 0
  | (term_app M N) => (term_label_bound M) + (term_label_bound N)
  | (term_abs M) => term_label_bound M
  end.


Fixpoint environment_label_bound (Γ : environment) : nat :=
  match Γ with
  | [] => 0
  | (((_, n), _) :: Γ) => 1 + n + environment_label_bound Γ
  end.


Lemma exists_fresh : forall (M : term) (Γ : environment), exists (x : label), fresh_in x M /\ fresh_in_environment x Γ.
Proof.
move => M Γ.
exists (0, term_label_bound M + environment_label_bound Γ).
split.
{
move : (environment_label_bound Γ) => m.
clear; elim : M m; cbn.

case; intros; constructor.
case; intros; omega.

intros; constructor.

move => M IHM N IHN m; constructor. 
rewrite <- Nat.add_assoc; auto.
have : term_label_bound M + term_label_bound N + m = term_label_bound N + (term_label_bound M + m) by omega.
move => ->; auto.

eauto using fresh_in.
}
{
move : (term_label_bound M) => m.
clear; elim : Γ m; cbn.

intros; constructor.

case; case; intros; constructor.
case; omega.
have : forall a b c, a + S (b + c) = (1+a+b) + c by intros; omega.
move => ->.
gimme where fresh_in_environment; apply.
}
Qed.


Lemma fresh_abstraction : forall (x : label) (n : nat) (Γ : environment) (M : term) (phi : formula') (t : formula), 
  fresh_in x M -> fresh_in_environment x Γ ->
  derivation n ((x, phi) :: Γ) (instantiate x 0 M) t ->
  derivation (S n) Γ (term_abs M) (arr phi t).
Proof.
intros.
apply : intro_arr.
move => y.
gimme derivation.
move : (0) => m.
revert dependent x => x.
move : x y Γ M phi t m.
apply (lt_wf_ind n).

move => {n} n IH; intros; gimme derivation; inversion.
{(*case M is var*)
revert dependent M.
case; cbn; try done.
intro; inversion; case.
intro; subst.
gimme In where x; inversion.
gimme @eq; case; done.
gimme In; move /(in_cons (y, phi)).
eauto using derivation.

move => i _.
case : (i =? m). 
case; intro; subst.
gimme In where x.
inversion.
gimme @eq; case; intro; subst.
apply : ax; try eassumption.
by constructor.

exfalso; gimme fresh_in_environment; move /Forall_forall.
by move /(_ _ ltac:(eassumption)).

inversion.
}

{(*case M is abs*)
revert dependent M.
case; cbn; try done.

move => i; case : (i =? m); done.

move => M'; inversion.
case; intro; subst.
apply : intro_arr => z'.
match goal with [ |- derivation _ ((z', ?phi') :: _) _ _] => rename phi' into psi end.

have := exists_fresh M' ((x, phi) :: (y, phi) :: Γ) => [[z [?]]].
inversion.
apply : (IH); try eassumption + omega.
clear z'.
gimme Forall; inversion.
apply : fresh_in_instantiate; done.

apply (weakening (Γ := ((y, phi) :: (z, psi) :: Γ))); last list_inclusion.
gimme where psi.
move /(_ z) /(weakening (Γ' := ((x, phi) :: (z, psi) :: Γ))).
nip; first list_inclusion.
rewrite ? (swap_instantiations z); try omega.
apply : IH.

omega.
apply : fresh_in_instantiate; auto.

constructor; auto.
}
{(*case M is app*)
revert dependent M.
case; cbn; try done.

move => i; case : (i =? m); done.

move => M' N'; inversion; case; intros; subst.
gimme derivation; move /IH.
nip; first omega.
move /(_ y ltac:(assumption) ltac:(assumption)) => ?.
apply : elim_arr; try eassumption.
gimme Forall.
rewrite ? Forall_forall => ? ? ?.
apply : IH; try omega + eauto.
}
Qed.

(*only locally closed (well-formed) terms are typable*)
Theorem derivation_lc : forall (n : nat) (M : term) (Γ : environment) (t : formula), derivation n Γ M t -> lc 0 M.
Proof.
move => n.
apply (lt_wf_ind n).
move => {n} n IH.
intros until 0; inversion.

auto using lc.

constructor.
gimme where instantiate; move /(_ (0,0)).
move /IH.
nip; first omega.
move /Lc.instantiate_iff. apply.

gimme Forall; move /forall_exists_in_formula' => [? [? ?]].
constructor; eauto.
Qed.


(*it suffices to bind a fresh variable wrt. environment*)
Theorem fresh_abstraction_bind : forall (x : label) (n : nat) (Γ : environment) (M : term) (phi : formula') (t : formula), 
  fresh_in_environment x Γ ->
  derivation n ((x, phi) :: Γ) M t ->
  derivation (S n) Γ (term_abs (bind x 0 M)) (arr phi t).
Proof.
intros.

apply : fresh_abstraction; try eassumption.
apply : fresh_in_bind.
rewrite Lc.instantiate_bind.
apply : derivation_lc; eassumption.
done.
Qed.


Lemma derivation_relax_depth : forall (n m : nat) (Γ: environment) (M : term) (t : formula), 
  derivation n Γ M t -> n <= m -> derivation m Γ M t.
Proof.
move => n.
apply (lt_wf_ind n).
move => {n} n IH; intros.
gimme derivation; inversion.

eauto using derivation.

all: have : m = S (Nat.pred m) by omega.
all: move => ->.

apply : intro_arr.
move => x; gimme where derivation; move /(_ x) => ?.
apply : IH; try eassumption; omega.

apply : elim_arr.
apply: IH; try eassumption; omega.
apply : Forall_impl; last eassumption.
intros; apply : IH; try eassumption; omega.
Qed.
