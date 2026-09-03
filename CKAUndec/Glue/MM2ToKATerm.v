(* Bridges MM2/Simulator.v's step-indexed evaluator (Theta_MM2) to
   Encoding.v's own KA-term encoding: R_target c y is the KA-term
   inequality Encoding.v attaches to running the program coded by c
   from register state (y,0) -- a per-program *dependent* Prop
   (red_lb/red_ub's own KA-term type depends on P via
   Q := fin (S (S (length P))), so there is no single common `ka_term`
   type to state this over; each c simply routes through its own type
   internally, which is fine since the end result is just a Prop). This
   bridging needs no axiom -- it is a straightforward consequence of
   Encoding.v's mm2_R_soundness/mm2_R_completeness, applicable
   regardless of which route (axiom-free machine-relative, or
   CT_L-based absolute) is used to finish the undecidability argument.
   R_target/R_target_iff_outcome are what CKAUndec/Glue/TLToRTarget.v
   and CKAUndec/K.v build on. *)

From Stdlib Require Import Unicode.Utf8.
From stdpp Require relations.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat MM2_simulator.
From kacc.MM2 Require Import Simulator RtcBridge.
From kacc Require Import CKAUndec.Encoding.

Require Import SyntheticComputability.Shared.partial.

(* Writing `red_lb P s1 ⊑ red_ub P` directly here (fresh notation
   elaboration) fails: Coq's ⊑ instance search needs to recognize the
   product generator type as `monoid_car (prod_monoid M1 M2)`, but
   red_lb's/red_ub's own generator-type expressions unfold their two
   factors to different (definitionally equal, syntactically distinct)
   normal forms, and typeclass-search-time unification (unlike ordinary
   conversion checking) doesn't chase that Canonical Structure chain
   through the mismatch. Fix: extract the *already-elaborated* Prop
   directly from mm2_R_completeness's own stored type via Ltac reflection,
   instead of re-stating it via the ⊑ notation ourselves -- this performs
   no fresh instance search at all. *)
Definition red_leq (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@mm2_R_completeness P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target (c y : nat) : Prop := red_leq (progOf c) (1,(y,0)).

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
