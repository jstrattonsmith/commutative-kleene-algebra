(* NOT on the critical path -- superseded, kept for documentation.
   Connects MM2/Legacy/Simulator.v's Theta_MM2 to CKAUndec/Encoding.v's
   R_target (and its embedded-alphabet analogue, against
   CKAUndec/BinaryAlphabet.v's red_leq'). The project actually connects
   to R_target directly via Encoding.v's own soundness/completeness
   pair (CKAUndec/Glue/TLToRTarget.v and its embedded mirror), which
   needs no separate evaluator to reconcile against a compiled
   program's reachability facts; neither lemma below is used elsewhere.

   Kept separate from MM2/Legacy/Simulator.v itself: this file needs
   CKAUndec/Encoding.v and CKAUndec/BinaryAlphabet.v, which pull in
   ssreflect, and Simulator.v's other clients (MM2_PrefixSplice.v,
   SMN_MM2.v) are plain-tactic-style and break if that leaks in. Being
   a leaf (nothing else Requires this file) keeps it contained. *)

From Stdlib Require Import Unicode.Utf8.
From stdpp Require relations.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat MM2_simulator.
Import MM2Notations.
From kacc Require Import MM2.RtcBridge.
From kacc Require Import MM2.Legacy.Simulator.
Require kacc.KA.algebra.
From kacc Require Import CKAUndec.Encoding.
Require kacc.CKAUndec.BinaryAlphabet.

Require Import SyntheticComputability.Shared.partial.

Lemma R_target_iff_outcome c y v :
  Θ_MM2 c y =! v -> (R_target c y <-> v = 1).
Proof.
intros [n Hn] % seval_hasvalue.
rewrite seval_Theta_MM2 in Hn.
unfold R_target.
assert (Hrtc : relations.rtc (mm2_step (progOf c)) (1,(y,0)) (mm2_iter (progOf c) n (1,(y,0))))
  by (apply crt_to_rtc; apply mm2_iter_rtc).
unfold mm2_outcome_at in Hn.
destruct (mm2_haltedAt (progOf c) n (1,(y,0))) eqn:Ehalt; [| discriminate].
assert (Hstop_fun : mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1,(y,0))) = None).
{ unfold mm2_haltedAt in Ehalt.
  destruct (mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1,(y,0))));
    [discriminate | reflexivity]. }
assert (Hstop : mm2_stop (progOf c) (mm2_iter (progOf c) n (1,(y,0))))
  by exact (mm2_stop_of_step_fun_none _ _ Hstop_fun).
destruct (mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0))) eqn:Eeq.
- apply mm2_state_eqb_true in Eeq.
  assert (Hv : v = 1) by congruence.
  subst v.
  split; [intros _; reflexivity | intros _].
  apply mm2_R_completeness. rewrite Eeq in Hrtc. exact Hrtc.
- assert (Hv : v = 0) by congruence.
  subst v.
  split.
  + intros Hle. exfalso.
    pose proof (mm2_R_soundness Hrtc Hstop Hle) as Heq.
    assert (Eeq' : mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0)) = true)
      by (apply mm2_state_eqb_true; exact Heq).
    rewrite Eeq' in Eeq. discriminate.
  + discriminate.
Qed.

(* The embedded/binary-alphabet analogue, against
   CKAUndec/BinaryAlphabet.v's own exported red_leq'/
   mm2_R_completeness'/mm2_R_soundness' -- that file needs no import
   from Legacy/ itself. *)

Lemma R_target_iff_outcome_binary (c k : nat)
  (enc : algebra.setoid_car
           (@Encoding.mm_sym_setoid (Fin.t (S (S (length (progOf c)))))) ->
         list bool)
  (Henc : forall x y, enc x = enc y -> x = y)
  (Hlen : forall x, length (enc x) = k)
  (Hk_pos : 0 < k) (y v : nat) :
  Θ_MM2 c y =! v ->
  (@BinaryAlphabet.red_leq' c k enc Hlen Hk_pos (1%nat, (y, 0%nat)) <-> v = 1%nat).
Proof.
intros [n Hn] % seval_hasvalue.
rewrite seval_Theta_MM2 in Hn.
unfold BinaryAlphabet.red_leq'.
assert (Hrtc : relations.rtc (mm2_step (progOf c)) (1%nat, (y, 0%nat)) (mm2_iter (progOf c) n (1%nat, (y, 0%nat))))
  by (apply crt_to_rtc; apply mm2_iter_rtc).
unfold mm2_outcome_at in Hn.
destruct (mm2_haltedAt (progOf c) n (1%nat, (y, 0%nat))) eqn:Ehalt; [| discriminate].
assert (Hstop_fun : mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1%nat, (y, 0%nat))) = None).
{ unfold mm2_haltedAt in Ehalt.
  destruct (mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1%nat, (y, 0%nat))));
    [discriminate | reflexivity]. }
assert (Hstop : mm2_stop (progOf c) (mm2_iter (progOf c) n (1%nat, (y, 0%nat))))
  by exact (mm2_stop_of_step_fun_none _ _ Hstop_fun).
destruct (mm2_state_eqb (mm2_iter (progOf c) n (1%nat, (y, 0%nat))) (0, (0, 0))) eqn:Eeq.
- apply mm2_state_eqb_true in Eeq.
  assert (Hv : v = 1%nat) by congruence.
  subst v.
  split; [intros _; reflexivity | intros _].
  apply (@BinaryAlphabet.mm2_R_completeness' c k enc Henc Hlen Hk_pos).
  rewrite Eeq in Hrtc. exact Hrtc.
- assert (Hv : v = 0%nat) by congruence.
  subst v.
  split.
  + intros Hle. exfalso.
    pose proof (@BinaryAlphabet.mm2_R_soundness' c k enc Henc Hlen Hk_pos
                  (1%nat, (y, 0%nat)) (mm2_iter (progOf c) n (1%nat, (y, 0%nat)))
                  Hrtc Hstop Hle) as Heq.
    assert (Eeq' : mm2_state_eqb (mm2_iter (progOf c) n (1%nat, (y, 0%nat))) (0, (0, 0)) = true)
      by (apply mm2_state_eqb_true; exact Heq).
    rewrite Eeq' in Eeq. discriminate.
  + discriminate.
Qed.
