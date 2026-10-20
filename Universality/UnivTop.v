(* Full universality in KA: the encodings of Universality/UnivEncoding.v, with
   `Σ*` (Universality/BalancedKA.v's `sigma_top`, i.e. `pseudo_top`) on the
   left instead of `bal_star`. The upper bounds are those of UnivEncoding.v
   joined with `unbal`, the words with the wrong number of commuting letters.
   Completeness comes from the pre-KA completeness theorems through
   `ka_top_complete`; soundness goes through the language model
   (`ka_top_sound`). This needs star induction and so holds in the free KA,
   not in the free pre-KA. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite fin relations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.
From kacc Require Import Universality.balanced.
From kacc Require Import KA.BinaryAlphabetTransport.
From kacc Require Import Universality.BalancedBinary.
From kacc Require Import KA.ka Universality.BalancedKA.
From kacc Require Import CKAUndec.Encoding Universality.UnivEncoding.
From Undecidability.MinskyMachines.Util Require Import
  MM2_facts MM2_stepper MM2_simulator.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

Section MM2Top.

Variable P : list mm2_instr.
Notation Q := (fin (S (S (length P)))).
Notation TL := (option_setoid (@mm_sym_setoid Q)).

Definition univ_top_ub (s1 : mm2_state) := univ_ub_mm2 P s1 ⊔ unbal.

Theorem univ_top_completeness s1 :
  rtc (mm2_step P) s1 (0, (0, 0)) →
  FKA (sigma_top (A := TL)) ⊑ FKA (univ_top_ub s1).
Proof. by move/univ_completeness; exact: ka_top_complete. Qed.

Theorem univ_top_soundness s1 s2 :
  rtc (mm2_step P) s1 s2 → mm2_stop P s2 →
  FKA (sigma_top (A := TL)) ⊑ FKA (univ_top_ub s1) →
  s2 = (0, (0, 0)).
Proof.
case/rtc_uchain => cs [cs' [Hc E]] Hstop /ka_top_sound Hl.
apply: uconf_of_halt0.
refine (univ_sound_lang (@F1_not_active P) Hc E (stop_not_active Hstop) _).
exact: (Hl (run (uconf_of P s1 :: cs))).
Qed.

(** ** Over the binary alphabet *)

Definition univ_top_ub_bin (s1 : mm2_state) := univ_ub_bin P s1 ⊔ unbal.

Theorem univ_top_completeness_bin s1 :
  rtc (mm2_step P) s1 (0, (0, 0)) →
  FKA (sigma_top (A := bool_setoid)) ⊑ FKA (univ_top_ub_bin s1).
Proof. by move/univ_completeness_bin; exact: ka_top_complete. Qed.

Theorem univ_top_soundness_bin s1 s2 :
  rtc (mm2_step P) s1 s2 → mm2_stop P s2 →
  FKA (sigma_top (A := bool_setoid)) ⊑ FKA (univ_top_ub_bin s1) →
  s2 = (0, (0, 0)).
Proof.
case/rtc_uchain => cs [cs' [Hc E]] Hstop /ka_top_sound Hle.
have Hl := bin_sound_lang (enc_onehot_inj' TL) (enc_onehot_length TL)
             (kL_pos P) Hle.
apply: uconf_of_halt0.
refine (univ_sound_lang (@F1_not_active P) Hc E (stop_not_active Hstop) _).
exact: (Hl _ (run (uconf_of P s1 :: cs))).
Qed.

End MM2Top.

Definition univ_top_leq (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@univ_top_completeness P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target_univ_top (c y : nat) : Prop :=
  univ_top_leq (progOf c) (1%nat, (y, 0)).

Definition univ_top_leq_bin (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@univ_top_completeness_bin P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target_univ_top_bin (c y : nat) : Prop :=
  univ_top_leq_bin (progOf c) (1%nat, (y, 0)).
