(* Native effective inseparability over MM2 program codes, mirroring
   coq-synthetic-computability's Models/EffectiveInseparability_L.v but built
   directly over two-counter machines instead of L. Unlike L's opaque
   enum_term/I_term retraction, MM2 programs are simple first-order data (a
   4-constructor instruction type + list), so nat<->program decoding is a
   concrete, structural stdpp Countable instance -- no self-interpretation
   wall here. *)

From Stdlib Require Import Unicode.Utf8.
From stdpp Require Import countable list.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

From kacc Require Import mm.

Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
(* Only for enum_iff (a plain enumerable <-> semi_decidable fact) -- not for
   the EA typeclass itself, so no axiom dependency is introduced here. *)
Require Import SyntheticComputability.Axioms.EA.

(* --- 0. nat <-> list mm2_instr, via a concrete stdpp Countable instance -- *)

Instance mm2_instr_eq_dec : EqDecision mm2_instr.
Proof. unfold EqDecision, Decision. decide equality; apply Nat.eq_dec. Defined.

Definition mm2_instr_to_sum (i : mm2_instr) : unit + unit + nat + nat :=
  match i with
  | mm2_inc_a => inl (inl (inl tt))
  | mm2_inc_b => inl (inl (inr tt))
  | mm2_dec_a j => inl (inr j)
  | mm2_dec_b j => inr j
  end.

Definition mm2_instr_of_sum (s : unit + unit + nat + nat) : mm2_instr :=
  match s with
  | inl (inl (inl tt)) => mm2_inc_a
  | inl (inl (inr tt)) => mm2_inc_b
  | inl (inr j) => mm2_dec_a j
  | inr j => mm2_dec_b j
  end.

Instance mm2_instr_countable : Countable mm2_instr.
Proof.
  apply (inj_countable' mm2_instr_to_sum mm2_instr_of_sum).
  intros []; reflexivity.
Defined.

(* Countable (list mm2_instr) comes for free from stdpp's list_countable
   instance, given Countable mm2_instr above. *)

Definition progOf (c : nat) : list mm2_instr :=
  match decode_nat c with Some P => P | None => [] end.

Definition codeOf (P : list mm2_instr) : nat := encode_nat P.

Lemma progOf_codeOf P : progOf (codeOf P) = P.
Proof. unfold progOf, codeOf. now rewrite decode_encode_nat. Qed.

(* Deliberately NOT `Import partial.implementation`: it pulls the *concrete*
   part/seval/hasvalue/mu into unqualified scope, shadowing the abstract
   class-projection versions used throughout the rest of this file (the same
   gotcha noted in EffectiveInseparability_L.v). Register the instance via a
   qualified reference instead. *)
Global Existing Instance SyntheticComputability.Shared.partial.implementation.monotonic_functions.

(* --- 1. step-indexed MM2 evaluator, monotone by construction ----------- *)

Definition mm2_step_total (P : list mm2_instr) (s : mm2_state) : mm2_state :=
  match mm2_step_fun P s with Some s' => s' | None => s end.

Definition mm2_iter (P : list mm2_instr) (n : nat) (s0 : mm2_state) : mm2_state :=
  Nat.iter n (mm2_step_total P) s0.

Definition mm2_haltedAt (P : list mm2_instr) (n : nat) (s0 : mm2_state) : bool :=
  match mm2_step_fun P (mm2_iter P n s0) with Some _ => false | None => true end.

Lemma mm2_iter_S P n s0 : mm2_iter P (S n) s0 = mm2_step_total P (mm2_iter P n s0).
Proof. reflexivity. Qed.

Lemma mm2_iter_frozen P n s0 :
  mm2_step_fun P (mm2_iter P n s0) = None ->
  forall k, mm2_iter P (n + k) s0 = mm2_iter P n s0.
Proof.
  intros Hstop k. induction k as [|k IH].
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r, mm2_iter_S, IH.
    unfold mm2_step_total. now rewrite Hstop.
Qed.

Lemma mm2_haltedAt_mono P s0 : monotonic (fun n => if mm2_haltedAt P n s0 then Some tt else None).
Proof.
  intros n1 [] Hn1 n2 Hle.
  unfold mm2_haltedAt in *.
  destruct (mm2_step_fun P (mm2_iter P n1 s0)) as [s'|] eqn:E; [discriminate |].
  assert (Hk : exists k, n2 = n1 + k) by (exists (n2 - n1); lia).
  destruct Hk as [k ->].
  rewrite (mm2_iter_frozen P n1 s0 E k).
  now rewrite E.
Qed.

Definition mm2_state_eqb (s1 s2 : mm2_state) : bool :=
  match s1, s2 with
  | (i1,(a1,b1)), (i2,(a2,b2)) => (Nat.eqb i1 i2 && Nat.eqb a1 a2 && Nat.eqb b1 b2)%bool
  end.

Definition mm2_outcome_at (c y n : nat) : option nat :=
  if mm2_haltedAt (progOf c) n (1,(y,0))
  then Some (if mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0)) then 1 else 0)
  else None.

Lemma monotonic_mm2_outcome_at c y : monotonic (mm2_outcome_at c y).
Proof.
  intros n1 v Hn1 n2 Hle.
  unfold mm2_outcome_at in *.
  destruct (mm2_haltedAt (progOf c) n1 (1,(y,0))) eqn:E1; [| discriminate].
  pose proof (mm2_haltedAt_mono (progOf c) (1,(y,0)) n1 tt) as Hmono.
  cbn in Hmono.
  rewrite E1 in Hmono.
  specialize (Hmono eq_refl n2 Hle).
  destruct (mm2_haltedAt (progOf c) n2 (1,(y,0))) eqn:E2; [| discriminate].
  assert (Hk : exists k, n2 = n1 + k) by (exists (n2 - n1); lia).
  destruct Hk as [k ->].
  assert (Hstop : mm2_step_fun (progOf c) (mm2_iter (progOf c) n1 (1,(y,0))) = None).
  { unfold mm2_haltedAt in E1.
    destruct (mm2_step_fun (progOf c) (mm2_iter (progOf c) n1 (1,(y,0)))); [discriminate|reflexivity]. }
  rewrite (mm2_iter_frozen (progOf c) n1 (1,(y,0)) Hstop k).
  exact Hn1.
Qed.

Definition Θ_ours_MM2 (c y : nat) : part nat :=
  partial.implementation.Build_part (monotonic_mm2_outcome_at c y).

Definition W_MM2 (c y : nat) : Prop := exists n, mm2_haltedAt (progOf c) n (1,(y,0)) = true.

Definition semidec_of_MM2 (c y n : nat) : bool := mm2_haltedAt (progOf c) n (1,(y,0)).

Lemma semidec_of_MM2_spec c : semi_decider (semidec_of_MM2 c) (W_MM2 c).
Proof. intros y. unfold semidec_of_MM2, W_MM2. tauto. Qed.

Definition A0_MM2 (z : nat) : Prop := Θ_ours_MM2 (fst (unembed z)) (snd (unembed z)) =! 1.
Definition B1_MM2 (z : nat) : Prop := Θ_ours_MM2 (fst (unembed z)) (snd (unembed z)) =! 0.

Lemma A0_MM2_enumerable : enumerable A0_MM2.
Proof.
apply (proj2 (enum_iff A0_MM2)).
exists (fun z n =>
  match (partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n) with
  | Some v => Nat.eqb v 1
  | None => false
  end).
intros z. unfold A0_MM2. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct ((partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n)) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Lemma B1_MM2_enumerable : enumerable B1_MM2.
Proof.
apply (proj2 (enum_iff B1_MM2)).
exists (fun z n =>
  match (partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n) with
  | Some v => Nat.eqb v 0
  | None => false
  end).
intros z. unfold B1_MM2. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct ((partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n)) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.
