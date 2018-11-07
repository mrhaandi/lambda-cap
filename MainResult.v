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

Require Import Derivation.
Require Import StrictDerivation.
Require Import Encoding.
Require Import Soundness.
Require Import Completeness.

(*
given set "rs" of rewriting rules of shape ab -> cd,
we have that 0..0 ->* 1..1 for some positive number of symbols
iff
triangle is inhabited in the environment (Γ_init ++ Γ_step rs) by a normal form N in the Coppo-Dezani-Venneri (cf. Strict Type Assignment [1]) type assignment system [2].
*)
Theorem correctness : forall (rs : list rule), 
  (exists (m : nat), rewrites_to rs (repeat 0 (1+m)) (repeat 1 (1+m))) <->
  (exists (N : term), normal_form N /\
    strict_derivation (Γ_init ++ Γ_step rs) N (atom triangle)).
Proof.
intro; split.

move => [m]. move /completeness => [n [M [?]]].
move /strict_derivation_completeness.
move /(_ (well_formed_Γ_all rs)).
eauto.

move => [N [?]].
move /strict_derivation_soundness => [n]. 
move /soundness.
eauto.
Qed.

Print Assumptions correctness.


(*show that all environment types are at most rank 2 and the goal type is at most rank 3 (actually rank 0)*)
Lemma rank_bound : 
  (rank_formula' (atom triangle) <= 3) /\ 
  (forall (rs : list rule) (x : label) (phi : formula'), 
    In (x, phi) (Γ_init ++ Γ_step rs) -> rank_formula' phi <= 2).
Proof.
split; intros.
cbn; do ? constructor.
apply : rank_environment_bound; eassumption.
Qed.

(*
Bibliography
[1] van Bakel S. Strict Intersection Types for the Lambda Calculus. ACM Computing Surveys, 2011. 43(3). doi:10.1145/1922649.1922657.
[2] M. Coppo, M. Dezani-Ciancaglini, and B. Venneri. Functional characters of solvable terms. Zeitschrift für Mathematische Logik und Grundlagen der Mathematik, 27:45–58, 1981.
*)