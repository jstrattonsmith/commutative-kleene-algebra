(* The Church's-Thesis-witness wrapper around coq-library-undecidability's
   MM2_simulator.v: builds Theta_MM2, a `part`-valued MM2 evaluator, plus
   two disjoint enumerable halting sets (A0_MM2/B1_MM2) directly from it.

   This half of the original file couldn't move upstream with the pure
   Godel-coding/step-indexed-simulator content (now
   Undecidability.MinskyMachines.Util.MM2_simulator): it genuinely needs
   SyntheticComputability's own machinery (Shared.partial, Axioms.EA,
   Synthetic.{Definitions,EnumerabilityFacts}), and coq-synthetic-
   computability's own scope is L-only -- adding MM2-specific machinery
   there would be over-specific to this project, not that library's
   general purpose (Jeremy's call, 2026-08-31; revisit if Arthur wants
   it there instead).

   mm2_outcome_at itself and the whole MetaRocq-driven L-extractability
   section moved upstream too, alongside progOf/codeOf/mm2_iter/
   mm2_haltedAt/mm2_state_eqb (2026-08-31): mm2_outcome_at has zero
   SyntheticComputability content on its own (it's only ever *used* to
   build Theta_MM2 below), and colocating the extraction instances with
   the functions they extract turned out to matter -- `extract` didn't
   reliably bridge a `computableExt`-registered instance across a file
   boundary, even though the exact same proof scripts work fine
   colocated (confirmed empirically while doing this split).

   Renamed Theta_ours_MM2 -> Theta_MM2 (2026-08-31): "ours" was
   uninformative, and this now matches the plain `_MM2`/`_L` per-model
   suffix convention (see also the coq-synthetic-computability
   Theta_ours/Theta_ours_L rename tracked in the same pass). *)

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import Lia.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat MM2_simulator.
Import MM2Notations.

(* MM2_stepper.v (imported above) has `Set Implicit Arguments` active at
   its own top level (not inside a Section, so not auto-reverted) --
   `Require Import` replays that as a side effect here too, silently
   making every P/s0/c/y-style argument below implicit unless reset.
   Confirmed empirically: every lemma declared in this file after the
   import, when later applied positionally, mismatched by exactly the
   number of arguments inferable from a later part of its type. *)
Unset Implicit Arguments.

Require Import SyntheticComputability.Shared.partial.
(* Deliberately NOT importing SyntheticComputability.Shared.embed_nat:
   embed/unembed already come from Util.MM2_embed_nat above (imported via
   Util.MM2_simulator's own transitive import). Having both in scope would
   put two distinct, unrelated `unembed` definitions in play. *)
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
(* Only for enum_iff (a plain enumerable <-> semi_decidable fact) -- not for
   the EA typeclass itself, so no axiom dependency is introduced here. *)
Require Import SyntheticComputability.Axioms.EA.

(* Deliberately NOT `Import partial.implementation`: it pulls the *concrete*
   part/seval/hasvalue/mu into unqualified scope, shadowing the abstract
   class-projection versions used throughout the rest of this file (the same
   gotcha noted in EffectiveInseparability_L.v). Register the instance via a
   qualified reference instead. *)
Global Existing Instance SyntheticComputability.Shared.partial.implementation.monotonic_functions.

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

Definition Θ_MM2 (c y : nat) : part nat :=
  partial.implementation.Build_part (monotonic_mm2_outcome_at c y).

Definition W_MM2 (c y : nat) : Prop := exists n, mm2_haltedAt (progOf c) n (1,(y,0)) = true.

Definition semidec_of_MM2 (c y n : nat) : bool := mm2_haltedAt (progOf c) n (1,(y,0)).

Lemma semidec_of_MM2_spec c : semi_decider (semidec_of_MM2 c) (W_MM2 c).
Proof. intros y. unfold semidec_of_MM2, W_MM2. tauto. Qed.

Definition A0_MM2 (z : nat) : Prop := Θ_MM2 (fst (unembed z)) (snd (unembed z)) =! 1.
Definition B1_MM2 (z : nat) : Prop := Θ_MM2 (fst (unembed z)) (snd (unembed z)) =! 0.

Lemma A0_MM2_enumerable : enumerable A0_MM2.
Proof.
apply (proj2 (enum_iff A0_MM2)).
exists (fun z n =>
  match (partial.seval (Θ_MM2 (fst (unembed z)) (snd (unembed z))) n) with
  | Some v => Nat.eqb v 1
  | None => false
  end).
intros z. unfold A0_MM2. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct ((partial.seval (Θ_MM2 (fst (unembed z)) (snd (unembed z))) n)) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Lemma B1_MM2_enumerable : enumerable B1_MM2.
Proof.
apply (proj2 (enum_iff B1_MM2)).
exists (fun z n =>
  match (partial.seval (Θ_MM2 (fst (unembed z)) (snd (unembed z))) n) with
  | Some v => Nat.eqb v 0
  | None => false
  end).
intros z. unfold B1_MM2. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct ((partial.seval (Θ_MM2 (fst (unembed z)) (snd (unembed z))) n)) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Lemma seval_Theta_MM2 c y n :
  partial.seval (Θ_MM2 c y) n = mm2_outcome_at c y n.
Proof. reflexivity. Qed.
