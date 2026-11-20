(* Closes the project's Theorem 17 analogue: the KA-term-level set K
   (an actual red_lb/red_ub inequality, i.e. a bona fide statement about
   validity of a KA-term ordering, via Encoding.v's R_target) is effectively
   inseparable from B1_L.

   Key structural point (traced through both source papers): NO
   numbering change is needed. Kuznetsov's own argument (ICTAC 2023,
   Section 4, Propositions 7-9) settles this directly: K, B1_L, A0_L are
   ALL subsets of the SAME domain (nat, indexed by z), and Proposition 9
   (eff_insep_superset) is simply reapplied with A0_L as the known subset
   and K as the new superset. Azevedo de Amorim et al.'s own Theorem 17
   (CSL 2025) is stated exactly this way -- disjointness plus a witness
   function, with NO enumerability of the sets baked in -- and so is
   coq-synthetic-computability's eff_insep.

   The library's eff_insep has a TOTAL witness, which is stronger than
   the papers' Definition 5 ("there exists a partial computable f...").
   eff_insep_K_B1_L states Theorem 17 in that stronger form;
   eff_insep_partial_K_B1_L is the paper's own partial form, derived from
   it by eff_insep_to_partial (no MP).

   The generic machinery (eff_insep, eff_insep_partial,
   eff_insep_to_partial, eff_insep_superset) lives in
   coq-synthetic-computability's
   ReducibilityDegrees/EffectiveInseparability.v; the "connection ->
   eff_insep" argument itself (z_vec, K_of,
   A0_L_subset_K_of/K_of_B1_L_disjoint/eff_insep_K_of_B1_L, generic over
   an arbitrary Pred) lives in that project's Models/T_L_Bridge.v. This
   file is just the CKA-specific instantiation at Pred := R_target c: K
   itself, and its effective inseparability from B1_L. K's enumerability
   (CKAUndec/KEnumerable.v) is what CKAUndec/KMComplete.v adds for the
   Sigma^0_1-completeness argument. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Shared.Libs.DLW Require Import vec.
Import vec_notations.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import CKAUndec.Encoding.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparability.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.

(* --- 2. K: the actual KA-term-level set, via R_target/red_leq -- a
   genuine red_lb ⊑ red_ub statement (Encoding.v), not a detour through
   Theta_ours_MM2. Fixed once via R_TL_R_target_connection's witness c.
   One-line instantiation of Models/T_L_Bridge.v's generic K_of at
   Pred := R_target c. *)

Section Splice6.

Variable (c : nat).
Hypothesis Hc : forall (v : Vector.t nat 2) (m : nat),
  m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R_target c (ps 1 * enc 2 v)).

Definition K (z : nat) : Prop := K_of (R_target c) z.

Lemma A0_L_subset_K (z : nat) : A0_L z -> K z.
Proof. intros HA. exact (A0_L_subset_K_of Hc HA). Qed.

Lemma K_B1_L_disjoint (z : nat) : K z -> ~ B1_L z.
Proof. intros HK. exact (K_of_B1_L_disjoint Hc HK). Qed.

End Splice6.

(* --- 3. The deliverable: K (the KA-term-level set) is effectively
   inseparable from B1_L, with a total witness. This is the project's
   Theorem 17 analogue at the actual KA-term/red_leq level.
   One-line instantiation of Models/T_L_Bridge.v's generic
   eff_insep_K_of_B1_L. *)

Theorem eff_insep_K_B1_L :
  exists c : nat, eff_insep W_L (K c) B1_L.
Proof.
destruct R_TL_R_target_connection as [c Hc].
exists c. exact (eff_insep_K_of_B1_L Hc).
Qed.

(* The same in the papers' Definition 5 form (partial witness). *)
Corollary eff_insep_partial_K_B1_L {Part : partiality} :
  exists c : nat, eff_insep_partial W_L (K c) B1_L.
Proof.
destruct eff_insep_K_B1_L as [c Hc].
exists c. exact (eff_insep_to_partial _ _ _ Hc).
Qed.
