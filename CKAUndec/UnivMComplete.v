(* m-completeness for the universality encoding of CKAUndec/UnivEncoding.v,
   following CKAUndec/BinaryAlphabetMComplete.v's generic route:
   K_univ c := K_of (R_target_univ c) is effectively inseparable from
   B1_L (via CKAUndec/Glue/UnivConnection.v), enumerable (via
   KA/enumerable.v), hence m-complete under CT_L and MP. Composing with
   the reduction z ↦ univ_ub_mm2 ... gives m-completeness of
   `Univ c := {e | bal_star ⊑ e}`, the balanced universality problem
   over the carrier `list (option (mm_sym Q)) * nat`. The same argument over
   the fixed carrier `list bool * nat` (via KA/BalancedBinary.v) gives
   Univ_bin_m_complete, with no existential over the machine. In the free
   KA, the same holds for full universality `Σ* ⊑ e` (CKAUndec/UnivTop.v,
   enumerable by KA/ka_enumerable.v): Univ_top_m_complete and
   Univ_top_bin_m_complete. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts
  DecidabilityFacts MoreReducibilityFacts.
From stdpp Require base decidable countable fin finite.
From kacc Require Import KA.algebra KA.pre_ka KA.enumerable KA.balanced.
From kacc Require Import CKAUndec.Encoding CKAUndec.UnivEncoding.
From kacc Require Import KA.ka KA.ka_enumerable KA.BalancedKA.
From kacc Require Import CKAUndec.UnivTop.
From kacc Require Import CKAUndec.Glue.UnivConnection.
From kacc Require CKAUndec.BinaryAlphabetMComplete.
From Undecidability.MinskyMachines.Util Require Import MM2_simulator.

Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.Models.EA_L_Myhill.
Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
From SyntheticComputability.ReducibilityDegrees Require Import
  EffectiveInseparabilityTransport EffectiveInseparabilityGeneric
  EffectiveInseparability.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.
Require Import SyntheticComputability.Synthetic.Definitions
  SyntheticComputability.Synthetic.EnumerabilityFacts
  SyntheticComputability.Synthetic.DecidabilityFacts
  SyntheticComputability.Synthetic.reductions.

Open Scope nat_scope.

Section UnivMComplete.

Variable c : nat.

Notation QF := (Fin.t (S (S (length (progOf c))))).

Definition Tm_univ : monoid :=
  prod_monoid (list_monoid (option_setoid (@Encoding.mm_sym_setoid QF)))
              nat_add_monoid.

Instance Tm_univ_eqdec : base.RelDecision (@Logic.eq (monoid_car Tm_univ)).
Proof. apply _. Defined.

Instance mm_sym_QF_countable : countable.Countable (Encoding.mm_sym QF).
Proof. apply finite.finite_countable. Defined.

Instance Tm_univ_countable : countable.Countable (monoid_car Tm_univ).
Proof. apply _. Defined.

Lemma Tm_univ_leibniz : base.LeibnizEquiv (monoid_car Tm_univ).
Proof. move=> x y; exact: M_equiv_eq. Qed.

(* The balanced universality problem over this carrier. *)
Definition Univ : ka_term (monoid_car Tm_univ) → Prop :=
  fun e =>
    base.sqsubseteq (bal_star (A := option_setoid (@mm_sym_setoid QF))) e.

Definition K_univ : nat → Prop := K_of (R_target_univ c).

Definition K_to_Univ (z : nat) : ka_term (monoid_car Tm_univ) :=
  univ_ub_mm2 (progOf c) (1, (ps 1 * enc 2 (z_vec z), 0)).

Lemma K_to_Univ_spec z : K_univ z ↔ Univ (K_to_Univ z).
Proof. reflexivity. Qed.

Theorem K_univ_enumerable : enumerable K_univ.
Proof.
have [f Hf] := @slice_enumerable_r Tm_univ _ _ Tm_univ_leibniz
  (bal_star (A := option_setoid (@mm_sym_setoid QF))) K_to_Univ.
by exists f => z; rewrite K_to_Univ_spec; exact: Hf z.
Qed.

(* Full universality in KA over the same carrier: `Σ* ⊑ e`, with `Σ*`
   the star of all generators of `list T * nat`. *)
Definition Univ_top : ka_term (monoid_car Tm_univ) → Prop :=
  fun e => base.sqsubseteq
    (FKA (sigma_top (A := option_setoid (@mm_sym_setoid QF)))) (FKA e).

Definition K_univ_top : nat → Prop := K_of (R_target_univ_top c).

Definition K_to_Univ_top (z : nat) : ka_term (monoid_car Tm_univ) :=
  univ_top_ub (progOf c) (1, (ps 1 * enc 2 (z_vec z), 0)).

Lemma K_to_Univ_top_spec z : K_univ_top z ↔ Univ_top (K_to_Univ_top z).
Proof. reflexivity. Qed.

Theorem K_univ_top_enumerable : enumerable K_univ_top.
Proof.
have [f Hf] := @fka_le_slice_enumerable_r Tm_univ _ _ Tm_univ_leibniz
  (sigma_top (A := option_setoid (@mm_sym_setoid QF))) K_to_Univ_top.
by exists f => z; rewrite K_to_Univ_top_spec; exact: Hf z.
Qed.

End UnivMComplete.

Theorem K_univ_m_complete : CT_L -> MP -> exists c, m-complete (K_univ c).
Proof.
intros ct MP_assm.
destruct R_TL_R_target_univ_connection as [c Hc].
exists c.
exact (m_complete_of_eff_insep_shape ct MP_assm
         (BinaryAlphabetMComplete.eff_insep_shape_K_of_B1_L
            Hc (K_univ_enumerable c))).
Qed.

Theorem Univ_m_complete : CT_L -> MP -> exists c, m-complete (@Univ c).
Proof.
intros ct MP_assm.
destruct (K_univ_m_complete ct MP_assm) as [c Hc].
exists c. intros q Hq.
apply (red_m_transitive (K_univ c) (@Univ c)).
- exact (Hc q Hq).
- exists (K_to_Univ c). exact (K_to_Univ_spec c).
Qed.

(** * Over the binary alphabet

    The carrier `list bool * nat` is one fixed algebra, independent of the
    machine, so the final statement needs no existential over `c`. *)

Definition Tm_ubin : monoid :=
  prod_monoid (list_monoid bool_setoid) nat_add_monoid.

Instance Tm_ubin_eqdec : base.RelDecision (@Logic.eq (monoid_car Tm_ubin)).
Proof. apply _. Defined.

Instance Tm_ubin_countable : countable.Countable (monoid_car Tm_ubin).
Proof. apply _. Defined.

Lemma Tm_ubin_leibniz : base.LeibnizEquiv (monoid_car Tm_ubin).
Proof. move=> x y; exact: M_equiv_eq. Qed.

Definition Univ_bin : ka_term (monoid_car Tm_ubin) → Prop :=
  fun e => base.sqsubseteq (bal_star (A := bool_setoid)) e.

Definition K_univ_bin (c : nat) : nat → Prop := K_of (R_target_univ_bin c).

Definition K_to_Univ_bin (c z : nat) : ka_term (monoid_car Tm_ubin) :=
  univ_ub_bin (progOf c) (1, (ps 1 * enc 2 (z_vec z), 0)).

Lemma K_to_Univ_bin_spec c z : K_univ_bin c z ↔ Univ_bin (K_to_Univ_bin c z).
Proof. reflexivity. Qed.

Theorem K_univ_bin_enumerable c : enumerable (K_univ_bin c).
Proof.
have [f Hf] := @slice_enumerable_r Tm_ubin _ _ Tm_ubin_leibniz
  (bal_star (A := bool_setoid)) (K_to_Univ_bin c).
by exists f => z; rewrite K_to_Univ_bin_spec; exact: Hf z.
Qed.

Theorem K_univ_bin_m_complete :
  CT_L -> MP -> exists c, m-complete (K_univ_bin c).
Proof.
intros ct MP_assm.
destruct R_TL_R_target_univ_bin_connection as [c Hc].
exists c.
exact (m_complete_of_eff_insep_shape ct MP_assm
         (BinaryAlphabetMComplete.eff_insep_shape_K_of_B1_L
            Hc (K_univ_bin_enumerable c))).
Qed.

(* Balanced universality over the fixed binary carrier is
   Sigma^0_1-complete. *)
Theorem Univ_bin_m_complete : CT_L -> MP -> m-complete Univ_bin.
Proof.
intros ct MP_assm.
destruct (K_univ_bin_m_complete ct MP_assm) as [c Hc].
intros q Hq.
apply (red_m_transitive (K_univ_bin c) Univ_bin).
- exact (Hc q Hq).
- exists (K_to_Univ_bin c). exact (K_to_Univ_bin_spec c).
Qed.

(** * Full universality in KA

    The same results with `Σ*` on the left, in the free KA. *)

Theorem K_univ_top_m_complete :
  CT_L -> MP -> exists c, m-complete (K_univ_top c).
Proof.
intros ct MP_assm.
destruct R_TL_R_target_univ_top_connection as [c Hc].
exists c.
exact (m_complete_of_eff_insep_shape ct MP_assm
         (BinaryAlphabetMComplete.eff_insep_shape_K_of_B1_L
            Hc (K_univ_top_enumerable c))).
Qed.

Theorem Univ_top_m_complete : CT_L -> MP -> exists c, m-complete (@Univ_top c).
Proof.
intros ct MP_assm.
destruct (K_univ_top_m_complete ct MP_assm) as [c Hc].
exists c. intros q Hq.
apply (red_m_transitive (K_univ_top c) (@Univ_top c)).
- exact (Hc q Hq).
- exists (K_to_Univ_top c). exact (K_to_Univ_top_spec c).
Qed.

Definition Univ_top_bin : ka_term (monoid_car Tm_ubin) → Prop :=
  fun e => base.sqsubseteq (FKA (sigma_top (A := bool_setoid))) (FKA e).

Definition K_univ_top_bin (c : nat) : nat → Prop :=
  K_of (R_target_univ_top_bin c).

Definition K_to_Univ_top_bin (c z : nat) : ka_term (monoid_car Tm_ubin) :=
  univ_top_ub_bin (progOf c) (1, (ps 1 * enc 2 (z_vec z), 0)).

Lemma K_to_Univ_top_bin_spec c z :
  K_univ_top_bin c z ↔ Univ_top_bin (K_to_Univ_top_bin c z).
Proof. reflexivity. Qed.

Theorem K_univ_top_bin_enumerable c : enumerable (K_univ_top_bin c).
Proof.
have [f Hf] := @fka_le_slice_enumerable_r Tm_ubin _ _ Tm_ubin_leibniz
  (sigma_top (A := bool_setoid)) (K_to_Univ_top_bin c).
by exists f => z; rewrite K_to_Univ_top_bin_spec; exact: Hf z.
Qed.

Theorem K_univ_top_bin_m_complete :
  CT_L -> MP -> exists c, m-complete (K_univ_top_bin c).
Proof.
intros ct MP_assm.
destruct R_TL_R_target_univ_top_bin_connection as [c Hc].
exists c.
exact (m_complete_of_eff_insep_shape ct MP_assm
         (BinaryAlphabetMComplete.eff_insep_shape_K_of_B1_L
            Hc (K_univ_top_bin_enumerable c))).
Qed.

(* Universality `Σ* ⊑ e` in the free KA over the fixed binary carrier
   `list bool * nat`, i.e. over the letters `0`, `1` and a letter `b`
   commuting with both, is Sigma^0_1-complete. *)
Theorem Univ_top_bin_m_complete : CT_L -> MP -> m-complete Univ_top_bin.
Proof.
intros ct MP_assm.
destruct (K_univ_top_bin_m_complete ct MP_assm) as [c Hc].
intros q Hq.
apply (red_m_transitive (K_univ_top_bin c) Univ_top_bin).
- exact (Hc q Hq).
- exists (K_to_Univ_top_bin c). exact (K_to_Univ_top_bin_spec c).
Qed.
