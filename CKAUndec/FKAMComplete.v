(* The CKA encoding in the free KA: KA derivability of term inequalities
   over CKAUndec/Encoding.v's carrier is Sigma^0_1-complete under CT_L
   (KA_ineq_fka_m_complete), by the same sandwich route as the pre-KA
   KA_ineq_m_complete (CKAUndec/KMComplete.v's m_complete_of_K_of).

   The sandwich only asks about halting runs:
   - a run halting at (0,(0,0)) gives the pre-KA inequality
     (mm2_R_completeness), which holds in KA too (fka_le_of_pre);
   - a run halting elsewhere refutes it, since languages form a KA
     (fka_lang) and the soundness argument only needs language inclusion
     (Encoding.v's mm2_R_soundness_lang).
   Divergent runs may land on either side. In KA some do land on the
   provable side: DirectUndec/FKALoop.v's fka_red_leq_not_terminates_fails,
   so the direct reduction from halting of DirectUndec/ fails here, while
   this route goes through unchanged. Comparison/Routes.v puts the two
   side by side. *)

From Stdlib Require Import Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base countable fin finite relations.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From kacc Require Import KA.algebra KA.pre_ka KA.lang KA.preka_enumerable.
From kacc Require Import KA.ka KA.ka_enumerable.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.
From Undecidability.MinskyMachines.Util Require Import
  MM2_facts MM2_stepper MM2_simulator.
From kacc Require Import CKAUndec.Encoding CKAUndec.Glue.TLToRTarget.
From kacc Require Import CKAUndec.KEnumerable.
From kacc Require CKAUndec.KMComplete.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Axioms.EA.

Local Open Scope nat_scope.

(** * The encoding in KA, correct on halting runs *)

Theorem mm2_R_completeness_fka P s1 :
  rtc (mm2_step P) s1 (0, (0, 0)) →
  FKA (red_lb P s1) ⊑ FKA (red_ub P).
Proof. by move/mm2_R_completeness; exact: fka_le_of_pre. Qed.

Theorem mm2_R_soundness_fka P s1 s2 :
  rtc (mm2_step P) s1 s2 → mm2_stop P s2 →
  FKA (red_lb P s1) ⊑ FKA (red_ub P) →
  s2 = (0, (0, 0)).
Proof. by move=> Hrtc Hstop /fka_lang; exact: mm2_R_soundness_lang. Qed.

Definition red_leq_fka (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@mm2_R_completeness_fka P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target_fka (c y : nat) : Prop :=
  red_leq_fka (progOf c) (1%nat, (y, 0)).

Theorem R_TL_R_target_fka_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> R_target_fka c (ps 1 * enc 2 v)).
Proof.
exact (@R_TL_connection_of red_leq_fka (@mm2_R_completeness_fka)
         (@mm2_R_soundness_fka)).
Qed.

(** * KA derivability over the encoding's carrier *)

Section FKAIneq.

Variable c : nat.

Notation Tm := (monoid_car (TmMonoid c)).

Local Existing Instances Tm_eqdec Tm_countable Tm_leibniz.

(* KEnumerable.v's KA_ineq with KA derivability in place of pre-KA
   derivability. *)
Definition KA_ineq_fka : ka_term Tm * ka_term Tm → Prop :=
  fun p => FKA p.1 ⊑ FKA p.2.

Theorem KA_ineq_fka_enumerable : enumerable KA_ineq_fka.
Proof.
(* Undecidability's and coq-synthetic-computability's `enumerable` are
   the same definition under different names. *)
have [f Hf] := @fka_le_enumerable (TmMonoid c) _ _ (@Tm_leibniz c).
by exists f.
Qed.

Definition K_fka : nat → Prop := K_of (R_target_fka c).

Lemma K_to_KA_ineq_fka_spec z : K_fka z ↔ KA_ineq_fka (K_to_KA_ineq c z).
Proof. reflexivity. Qed.

Theorem K_fka_enumerable : enumerable K_fka.
Proof.
apply: (enumerable_reduce (f := K_to_KA_ineq c) (Q := KA_ineq_fka));
[exact: K_to_KA_ineq_fka_spec | exact: KA_ineq_fka_enumerable].
Qed.

End FKAIneq.

(** * Sigma^0_1-completeness *)

Theorem KA_ineq_fka_m_complete :
  CT_L → ∃ c, m-complete (@KA_ineq_fka c).
Proof.
move=> ct; have [c Hc] := R_TL_R_target_fka_connection; exists c.
exact: (KMComplete.m_complete_of_K_of Hc (K_fka_enumerable c)
          (K_to_KA_ineq_fka_spec c) ct).
Qed.
