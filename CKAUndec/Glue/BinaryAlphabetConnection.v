(* The binary-alphabet analogue of CKA/Glue/TLToRTarget.v: mirrors its
   Psplice_R_target_divides/_not_divides/R_TL_R_target_connection,
   substituting CKA/BinaryAlphabet.v's mm2_R_completeness'/
   mm2_R_soundness' (halting-case only, exactly mirroring
   Encoding.mm2_R_completeness/mm2_R_soundness's own restriction) for
   the unembedded originals. Reuses MM2/Splice.v's Psplice_mm2_divides/
   Psplice_mm2_not_divides UNCHANGED -- those are pure MM2-level (rtc)
   facts, no KA terms involved, so nothing about the embedding touches
   them.

   Naming note: the binary-alphabet character encoding is named `bEnc`
   throughout (NOT `enc`) to avoid shadowing prime_seq.enc, which this
   file also uses pervasively (`ps 1 * enc 2 v`, from the Psplice
   construction) -- a real name collision caught while drafting this
   file, not a style choice. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import MM2 MMA.
Import MM2Notations.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
Import vec_notations.
Import Vector.VectorNotations.
From Undecidability.MinskyMachines Require Import mm_defs mma_defs fractran_mma
  mma_utils.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

From stdpp Require base decidable.
From kacc Require Import KA.algebra KA.pre_ka KA.enumerable.
From kacc Require Import CKAUndec.Glue.TLToRTarget Computability.TL_Bridge.
From Undecidability.MinskyMachines.Reductions Require Import
  FRACTRAN_computable_to_MM2_computable MM2_Splice.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat MM2_simulator.
From kacc Require Import MM2.Simulator MM2.RtcBridge.
From kacc Require Import CKAUndec.Glue.MM2ToKATerm.
From kacc Require Import CKAUndec.BinaryAlphabet.
Require kacc.CKAUndec.Encoding.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Synthetic.Definitions
  SyntheticComputability.Synthetic.EnumerabilityFacts.

(* algebra.v/pre_ka.v open ka_scope, whose `0`/`1` typeclass-resolved
   literals otherwise hijack every plain nat literal below (vec_nil
   cons cells, MM2 states, etc.) -- re-opening nat_scope last makes it
   win ties for bare numerals, avoiding a %nat annotation on every
   single occurrence. *)
Open Scope nat_scope.

Section SpliceBin.

Variable (Q : list (nat * nat)).
Notation QF := (Fin.t (S (S (length (progOf (c_P Q)))))).
Variable (k : nat).
Variable (bEnc : setoid_car (@Encoding.mm_sym_setoid QF) → list bool).
Variable (HbEnc : ∀ x y, bEnc x = bEnc y → x = y).
Variable (Hlen : ∀ x, length (bEnc x) = k).
Variable (Hk_pos : (0 < k)%nat).

Lemma Psplice_red_leq_bin_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
    (i0 Q, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  red_leq' (c := c_P Q) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat.
Proof.
intros Hc Hd.
apply (mm2_R_completeness' HbEnc Hlen Hk_pos).
apply crt_to_rtc.
apply (@Psplice_mm2_divides Q v b Hc Hd).
Qed.

Lemma Psplice_red_leq_bin_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
    (i0 Q, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ red_leq' (c := c_P Q) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat.
Proof.
intros Hc Hnd Hred.
assert (Hbad : ~ (progOf (c_P Q)) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)))
  by (apply Psplice_mm2_not_divides with (b := b); [exact Hc | exact Hnd]).
assert (Hout : sss_output (@mma_sss 2) (1, Psplice Q)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target Q, 0 ## b ## vec_nil))
  by (apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]).
assert (Hterm : sss_terminates (@mma_sss 2) (1, Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  by (exists (q_target Q, 0 ## b ## vec_nil); exact Hout).
apply (mma_mma2_reduction (Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)) in Hterm.
destruct Hterm as [s2 [Hreach Hstop]].
assert (Hs2 : s2 <> (0, (0, 0))).
{ intros ->. apply Hbad. rewrite progOf_c_P. exact Hreach. }
rewrite <- progOf_c_P in Hreach, Hstop.
apply crt_to_rtc in Hreach.
assert (Hred' : red_leq' (c := c_P Q) Hlen Hk_pos
    (mma_mm2_state (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))).
{ rewrite mma_mm2_state_22. exact Hred. }
assert (Hsound : s2 = (0, (0, 0))).
{ eapply (mm2_R_soundness' HbEnc); [exact Hreach | exact Hstop | exact Hred']. }
exact (Hs2 Hsound).
Qed.

End SpliceBin.

Theorem R_TL_R_target_connection_bin :
  exists (c k : nat) (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  forall (v : Vector.t nat 2) (m : nat),
    (m <= 1)%nat -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> red_leq' (c := c) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat).
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
destruct (binary_encoding_exists (c_P Q)) as [k [bEnc [HbEnc [Hlen Hk_pos]]]].
exists (c_P Q), k, bEnc, Hlen, Hk_pos.
intros v m Hm1 HR.
apply HQ in HR.
destruct HR as [b [Hcompute [Hdiv1 Hdiv2]]].
split.
- intros ->.
  assert (Hdb : divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
  exact (Psplice_red_leq_bin_divides HbEnc Hlen Hk_pos Hcompute Hdb).
- intros HRt.
  destruct (Nat.eq_dec m 0) as [-> | Hne]; [| lia].
  exfalso.
  assert (Hndb : ~ divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
  exact (Psplice_red_leq_bin_not_divides HbEnc Hcompute Hndb HRt).
Qed.
