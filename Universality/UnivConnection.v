(* The analogue of CKAUndec/Glue/TLToRTarget.v for the universality
   encodings of Universality/UnivEncoding.v: connects R_TL, through
   coq-library-undecidability's Reductions/MM2_Splice.v, to R_target_univ
   and its binary-alphabet counterpart R_target_univ_bin, and to their
   full-universality versions in KA (Universality/UnivTop.v). Each is an
   instance of CKAUndec/Glue/TLToRTarget.v's R_TL_connection_of, which
   states the splice argument once. Feeds Universality/UnivMComplete.v. *)

From Undecidability.MinskyMachines Require Import MM MM2 MMA Util.MM2_facts.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
From Undecidability.FRACTRAN Require Import
  fractran_utils prime_seq mm_fractran.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import Universality.UnivEncoding Universality.UnivTop.

Theorem R_TL_R_target_univ_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R_target_univ c (ps 1 * enc 2 v)).
Proof.
exact (@R_TL_connection_of univ_leq (@univ_completeness) (@univ_soundness)).
Qed.

Theorem R_TL_R_target_univ_bin_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R_target_univ_bin c (ps 1 * enc 2 v)).
Proof.
exact (@R_TL_connection_of univ_leq_bin (@univ_completeness_bin)
         (@univ_soundness_bin)).
Qed.

Theorem R_TL_R_target_univ_top_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R_target_univ_top c (ps 1 * enc 2 v)).
Proof.
exact (@R_TL_connection_of univ_top_leq (@univ_top_completeness)
         (@univ_top_soundness)).
Qed.

Theorem R_TL_R_target_univ_top_bin_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R_target_univ_top_bin c (ps 1 * enc 2 v)).
Proof.
exact (@R_TL_connection_of univ_top_leq_bin (@univ_top_completeness_bin)
         (@univ_top_soundness_bin)).
Qed.
