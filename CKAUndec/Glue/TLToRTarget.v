(* Bridges T_L (Rocq's own L-interpreter, compiled via the library's
   FRACTRAN->MMA2 chain, then spliced via coq-library-undecidability's Reductions/MM2_Splice.v) to Encoding.v's own
   R_target/red_leq convention (halt EXACTLY at (0,(0,0))).

   coq-library-undecidability's Reductions/MM2_Splice.v builds Psplice, a program that runs a compiled FRACTRAN
   program then tests/redirects on the output register's divisibility by
   qs 1 -- entirely MM2-generic, no mention of Encoding.v or R_target. This
   file is the CKA/T_L-specific glue connecting that construction to
   Encoding.v's own soundness/completeness pair (mm2_R_completeness/
   soundness), closing with R_TL_R_target_connection -- the connection
   CKAUndec/K.v builds its effective-inseparability argument on. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia Relations.
From Undecidability.MinskyMachines Require Import MM MM2 MMA Util.MM2_facts.
Import MM2Notations.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.
From Undecidability.MinskyMachines.Reductions Require Import
  FRACTRAN_computable_to_MM2_computable MM2_Splice.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat MM2_simulator.
From kacc Require Import CKAUndec.Glue.RtcBridge.
From kacc Require Import CKAUndec.Encoding.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

Require Import SyntheticComputability.Models.T_L_Uniform.
From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.
From stdpp Require relations.
Notation rtc := relations.rtc.

Lemma R_TL_FRACTRAN_computable : FRACTRAN_computable T_L_Uniform.R_TL.
Proof.
apply MM_computable_to_FRACTRAN_computable.
apply BSM_computable_to_MM_computable.
apply TM_computable_to_BSM_computable.
apply MMA_computable_to_TM_computable.
apply L_computable_closed_to_MMA_computable.
exact T_L_Uniform.L_computable_closed_R_TL.
Qed.

(* --- Connect coq-library-undecidability's Reductions/MM2_Splice.v's
   construction to any predicate R on the start states of the spliced
   program that is complete for runs halting at (0,(0,0)) and sound for
   halting runs: Encoding.v's red_leq (mm2_R_completeness/soundness), its
   binary-alphabet counterpart red_leq' (CKAUndec/Glue/BinaryAlphabetConnection.v)
   and the universality encodings (Universality/UnivConnection.v). *)

Section Splice.

Variable (Q : list (nat * nat)).
Notation P := (progOf (c_P Q)).
Variable R : mm2_state -> Prop.
Hypothesis R_complete : forall s1, rtc (mm2_step P) s1 (0, (0, 0)) -> R s1.
Hypothesis R_sound : forall s1 s2,
  rtc (mm2_step P) s1 s2 -> mm2_stop P s2 -> R s1 -> s2 = (0, (0, 0)).

Lemma Psplice_R_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0 Q, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  R (1, (ps 1 * enc 2 v, 0)).
Proof.
intros Hc Hd.
apply R_complete, crt_to_rtc.
apply Psplice_mm2_divides with (b := b); [exact Hc | exact Hd].
Qed.

Lemma Psplice_R_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0 Q, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ R (1, (ps 1 * enc 2 v, 0)).
Proof.
intros Hc Hnd Hred.
assert (Hbad : ~ P // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0))).
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
rewrite <- progOf_c_P in Hreach, Hstop.
apply crt_to_rtc in Hreach.
exact (Hs2 (R_sound Hreach Hstop Hred)).
Qed.

End Splice.

Definition R_TL_MMA2_pinned := FRACTRAN_computable_to_MMA2_pinned R_TL_FRACTRAN_computable.

(* --- Payoff: R_TL bridged all the way to Encoding.v's own R_target.

   The `m <= 1` hypothesis is not a limitation of the splice construction
   itself (Psplice/the divides-test in coq-library-undecidability's Reductions/MM2_Splice.v works for any m,
   distinguishing "m = 0" from "m > 0" via a single divisibility check)
   -- it's here because it's all A0_L/B1_L (CKAUndec.K.v,
   Computability/TL_Bridge.v) ever need: those sets only ever ask about
   R_TL's outputs 0 and 1, never larger m. Stating the connection only
   for m <= 1 keeps this theorem's proof from having to characterize
   what happens for m >= 2 (which the divides-test alone doesn't
   determine, since divides (qs 1 ^ m) is not injective across m
   without the accompanying ~divides (qs 1 ^ (S m)) bound also pinning m
   from above). *)

(* The witness c does not depend on R: one spliced program serves every
   predicate that is complete and sound for it. *)
Theorem R_TL_connection_gen :
  exists c : nat, forall R : mm2_state -> Prop,
    (forall s1, rtc (mm2_step (progOf c)) s1 (0, (0, 0)) -> R s1) ->
    (forall s1 s2, rtc (mm2_step (progOf c)) s1 s2 -> mm2_stop (progOf c) s2 ->
       R s1 -> s2 = (0, (0, 0))) ->
    forall (v : Vector.t nat 2) (m : nat),
      m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R (1, (ps 1 * enc 2 v, 0))).
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
exists (c_P Q).
intros R Hcomp Hsound v m Hm1 HR.
apply HQ in HR.
destruct HR as [b [Hcompute [Hdiv1 Hdiv2]]].
split.
- intros ->.
  assert (Hdb : divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
  exact (Psplice_R_divides Hcomp Hcompute Hdb).
- intros HRt.
  destruct (Nat.eq_dec m 0) as [-> | Hne]; [| lia].
  exfalso.
  assert (Hndb : ~ divides (qs 1) b)
    by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
  exact (Psplice_R_not_divides Hsound Hcompute Hndb HRt).
Qed.

(* The same, for a family R indexed by the program. *)
Theorem R_TL_connection_of (R : list mm2_instr -> mm2_state -> Prop)
    (R_complete : forall P s1, rtc (mm2_step P) s1 (0, (0, 0)) -> R P s1)
    (R_sound : forall P s1 s2, rtc (mm2_step P) s1 s2 -> mm2_stop P s2 ->
       R P s1 -> s2 = (0, (0, 0))) :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R (progOf c) (1, (ps 1 * enc 2 v, 0))).
Proof.
destruct R_TL_connection_gen as [c Hc].
exists c. apply Hc; [apply R_complete | apply R_sound].
Qed.

Theorem R_TL_R_target_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R_target c (ps 1 * enc 2 v)).
Proof.
exact (R_TL_connection_of Encoding.mm2_R_completeness Encoding.mm2_R_soundness).
Qed.
