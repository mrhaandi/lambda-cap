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
Require Import CD_Derivation.
Require Import Encoding.
Require Import Soundness.
Require Import Completeness.


(*
given set "rs" of rewriting rules of shape ab -> cd,
we have that 0..0 ->* 1..1 for some positive number of symbols
iff
triangle is inhabited in the environment (Γ_init ++ Γ_step rs) by a normal form N in the Coppo-Dezani type assignment system.
*)
Theorem correctness : forall (rs : list rule), 
  (exists (m : nat), rewrites_to rs (repeat 0 (1+m)) (repeat 1 (1+m))) <->
  (exists (N : term), normal_form N /\
    cd_derivation (Γ_init ++ Γ_step rs) N (singleton (atom triangle))).
Proof.
intro; split.

move => [m]. move /completeness => [n [M [?]]].
move /strict_cd_derivation_completeness.
move /(_ (well_formed_Γ_all rs)).
move /cd_derivation_completeness.
eauto.

move => [N [?]].
move /cd_derivation_soundness.
move /strict_cd_derivation_soundness.
move => [n]. move /soundness.
eauto.
Qed.

Print Assumptions correctness.