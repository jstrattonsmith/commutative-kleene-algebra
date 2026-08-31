(* Compatibility shim for the two MM2/Stepper.v lemmas that got
   deduplicated away during the 2026-08-31 upstream migration
   (mm2_step_det, mm2_stop_spec both duplicated existing MM2_facts.v
   lemmas -- mm2_step_det and mm2_stop_index_iff respectively -- under a
   different proof route; dropped in favor of reusing those directly).

   Restated here in exactly Stepper.v's original Section-scoped shape
   (Variable P, not a plain lemma argument) so CKAUndec/Encoding.v's and
   CKAUndec/BinaryAlphabet.v's existing `(mm2_stop_spec P)`/
   `(@mm2_step_det P)`-style call sites keep working unchanged --
   Set Implicit Arguments (active in Encoding.v as this project's own
   style) treats a bare top-level lemma's arguments differently from a
   Section Variable's, so this needs to match the original structure
   exactly, not just the original statements. *)

From Stdlib Require Import Unicode.Utf8 Lia.
Require Import ssreflect.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts.
Import MM2Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MM2StepperCompat.

Variable P : list mm2_instr.

Lemma mm2_step_det s s1 s2 :
  mm2_step P s s1 → mm2_step P s s2 → s1 = s2.
Proof. exact: MM2_facts.mm2_step_det. Qed.

Lemma mm2_stop_spec s : mm2_stop P s ↔ ¬ (0 < index s ∧ index s <= length P).
Proof. rewrite MM2_facts.mm2_stop_index_iff. lia. Qed.

End MM2StepperCompat.
