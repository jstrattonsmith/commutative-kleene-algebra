(* Bridges T_L (Rocq's own L-interpreter, compiled via the library's
   FRACTRAN->MMA2 chain, then spliced via MM2/Splice.v) to Encoding.v's own
   R_target/red_leq convention (halt EXACTLY at (0,(0,0))).

   MM2/Splice.v builds Psplice, a program that runs a compiled FRACTRAN
   program then tests/redirects on the output register's divisibility by
   qs 1 -- entirely MM2-generic, no mention of Encoding.v or R_target. This
   file is the CKA/T_L-specific glue connecting that construction to
   Encoding.v's own soundness/completeness pair (mm2_R_completeness/
   soundness), closing with R_TL_R_target_connection. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia Relations.
From Undecidability Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import MM MM2 MMA Util.MM2_facts.
Import MM2Notations.

From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
Import vec_notations.
Import Vector.VectorNotations.

From Undecidability.MinskyMachines Require Import mm_defs mma_defs fractran_mma mma_utils.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.

From kacc Require Import MM2.FractranCompiler MM2.Simulator MM2.Splice.
From kacc Require Import CKAUndec.Glue.MM2ToKATerm.
Require kacc.CKAUndec.Encoding.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import SyntheticComputability.Models.T_L_Uniform.
From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

Lemma R_TL_FRACTRAN_computable : FRACTRAN_computable T_L_Uniform.R_TL.
Proof.
apply MM_computable_to_FRACTRAN_computable.
apply BSM_computable_to_MM_computable.
apply TM_computable_to_BSM_computable.
apply MMA_computable_to_TM_computable.
apply L_computable_closed_to_MMA_computable.
exact T_L_Uniform.L_computable_closed_R_TL.
Qed.

(* --- Connect MM2/Splice.v's construction to Encoding.v's own R_target
   directly (bypassing Theta_ours_MM2 entirely -- R_target c y :=
   red_leq (progOf c) (1,(y,0)) is already stated for ANY program via
   mm2_R_completeness/soundness, generalized over P inside Encoding.v's own
   MM2Adapter section). *)

Lemma Psplice_R_target_divides (Q : list (nat * nat)) (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0 Q, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  R_target (c_P Q) (ps 1 * enc 2 v).
Proof.
intros Hc Hd.
unfold R_target.
apply Encoding.mm2_R_completeness.
apply crt_to_rtc.
apply Psplice_mm2_divides with (b := b); [exact Hc | exact Hd].
Qed.

Lemma Psplice_R_target_not_divides (Q : list (nat * nat)) (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0 Q, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ R_target (c_P Q) (ps 1 * enc 2 v).
Proof.
intros Hc Hnd Hred.
assert (Hbad : ~ (progOf (c_P Q)) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0))).
{ apply Psplice_mm2_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hout : sss_output (@mma_sss 2) (1, Psplice Q)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target Q, 0 ## b ## vec_nil)).
{ apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hterm : sss_terminates (@mma_sss 2) (1, Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  by (exists (q_target Q, 0 ## b ## vec_nil); exact Hout).
apply (mma_mma2_reduction (Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)) in Hterm.
destruct Hterm as [s2 [Hreach Hstop]].
assert (Hs2 : s2 <> (0, (0, 0))).
{ intros ->. apply Hbad. rewrite (progOf_c_P Q). exact Hreach. }
apply crt_to_rtc in Hreach.
assert (Hred' : red_leq (List.map mma_mm2_instr (Psplice Q))
                  (mma_mm2_state (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))).
{ unfold R_target in Hred. rewrite (progOf_c_P Q) in Hred. exact Hred. }
assert (Hsound : s2 = (0, (0, 0))).
{ eapply Encoding.mm2_R_soundness; [exact Hreach | exact Hstop | exact Hred']. }
exact (Hs2 Hsound).
Qed.

Definition R_TL_MMA2_pinned := FRACTRAN_computable_to_MMA2_pinned R_TL_FRACTRAN_computable.

(* --- Payoff: R_TL bridged all the way to Encoding.v's own R_target.

   The `m <= 1` hypothesis is not a limitation of the splice construction
   itself (Psplice/the divides-test in MM2/Splice.v works for any m,
   distinguishing "m = 0" from "m > 0" via a single divisibility check)
   -- it's here because it's all A0_L/B1_L (CKAUndec.K.v,
   Computability/TL_Bridge.v) ever need: those sets only ever ask about
   R_TL's outputs 0 and 1, never larger m. Stating the connection only
   for m <= 1 keeps this theorem's proof from having to characterize
   what happens for m >= 2 (which the divides-test alone doesn't
   determine, since divides (qs 1 ^ m) is not injective across m
   without the accompanying ~divides (qs 1 ^ (S m)) bound also pinning m
   from above). *)

Theorem R_TL_R_target_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R_target c (ps 1 * enc 2 v)).
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
exists (c_P Q).
intros v m Hm1 HR.
apply HQ in HR.
destruct HR as [b [Hcompute [Hdiv1 Hdiv2]]].
split.
- intros ->.
  assert (Hdb : divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
  apply Psplice_R_target_divides with (b := b); [exact Hcompute | exact Hdb].
- intros HRt.
  destruct (Nat.eq_dec m 0) as [-> | Hne]; [| lia].
  exfalso.
  assert (Hndb : ~ divides (qs 1) b)
    by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
  assert (Hcontra : ~ R_target (c_P Q) (ps 1 * enc 2 v))
    by (apply Psplice_R_target_not_divides with (b := b); assumption).
  exact (Hcontra HRt).
Qed.
