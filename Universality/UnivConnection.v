(* The analogue of CKAUndec/Glue/TLToRTarget.v for the universality
   encodings of Universality/UnivEncoding.v: connects R_TL, through
   coq-library-undecidability's Reductions/MM2_Splice.v, to R_target_univ
   and its binary-alphabet counterpart R_target_univ_bin, and to their
   full-universality versions in KA (Universality/UnivTop.v). The splice
   argument is stated once (R_TL_connection_of), for any family of
   propositions that is complete for runs halting at (0,(0,0)) and sound
   for halting runs. Feeds Universality/UnivMComplete.v. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia Relations.
From Undecidability Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import MM MM2 MMA Util.MM2_facts.
Import MM2Notations.

From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
Import vec_notations.
Import Vector.VectorNotations.

From Undecidability.MinskyMachines Require Import
  mm_defs mma_defs fractran_mma mma_utils.
From Undecidability.FRACTRAN Require Import
  fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.

From Undecidability.MinskyMachines.Reductions Require Import
  FRACTRAN_computable_to_MM2_computable MM2_Splice MMA2_to_MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_simulator.
From kacc Require Import CKAUndec.Glue.RtcBridge.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import Universality.UnivEncoding Universality.UnivTop.

Require Import SyntheticComputability.Models.T_L_Uniform.
From stdpp Require relations.
Notation rtc := relations.rtc.

Section Connection.

Variable R : list mm2_instr -> mm2_state -> Prop.
Hypothesis R_complete :
  forall P s1, rtc (mm2_step P) s1 (0, (0, 0)) -> R P s1.
Hypothesis R_sound :
  forall P s1 s2, rtc (mm2_step P) s1 s2 -> mm2_stop P s2 -> R P s1 ->
    s2 = (0, (0, 0)).

Lemma Psplice_R_divides (Q : list (nat * nat)) (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
    (i0 Q, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  R (progOf (c_P Q)) (1, (ps 1 * enc 2 v, 0)).
Proof.
intros Hc Hd.
apply R_complete, crt_to_rtc.
apply Psplice_mm2_divides with (b := b); [exact Hc | exact Hd].
Qed.

Lemma Psplice_R_not_divides
    (Q : list (nat * nat)) (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
    (i0 Q, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ R (progOf (c_P Q)) (1, (ps 1 * enc 2 v, 0)).
Proof.
intros Hc Hnd Hred.
assert (Hbad : ~ (progOf (c_P Q)) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0))).
{ apply Psplice_mm2_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hout : sss_output (@mma_sss 2) (1, Psplice Q)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
                 (q_target Q, 0 ## b ## vec_nil)).
{ apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hterm : sss_terminates (@mma_sss 2) (1, Psplice Q)
                  (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  by (exists (q_target Q, 0 ## b ## vec_nil); exact Hout).
apply (mma_mma2_reduction (Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  in Hterm.
destruct Hterm as [s2 [Hreach Hstop]].
assert (Hs2 : s2 <> (0, (0, 0))).
{ intros ->. apply Hbad. rewrite (progOf_c_P Q). exact Hreach. }
apply crt_to_rtc in Hreach.
rewrite (progOf_c_P Q) in Hred.
exact (Hs2 (R_sound Hreach Hstop Hred)).
Qed.

Theorem R_TL_connection_of :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R (progOf c) (1, (ps 1 * enc 2 v, 0))).
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
exists (c_P Q).
intros v m Hm1 HR.
apply HQ in HR.
destruct HR as [b [Hcompute [Hdiv1 Hdiv2]]].
split.
- intros ->.
  assert (Hdb : divides (qs 1) b)
    by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
  exact (Psplice_R_divides Hcompute Hdb).
- intros HRt.
  destruct (Nat.eq_dec m 0) as [-> | Hne]; [| lia].
  exfalso.
  assert (Hndb : ~ divides (qs 1) b)
    by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
  exact (Psplice_R_not_divides Hcompute Hndb HRt).
Qed.

End Connection.

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
