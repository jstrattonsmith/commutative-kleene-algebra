(* The three routes to Sigma^0_1-completeness, side by side.

   Every result below is proved elsewhere in this repository, or is a
   few-line twin of one; this file only puts the statements next to each
   other so that their hypotheses and proof dependencies can be compared
   directly (Print Assumptions at the end). See Comparison/ROUTES.md.

   - EI: effective inseparability from B1_L (the eff_insep predicate,
     T_L_Bridge.v's eff_insep_K_of_B1_L) gives creativity, and Myhill's
     theorem gives m-completeness. That last step needs MP, provably so
     (MPFree_L.v's MP_of_eff_insep_L_m_complete).
   - Sandwich: an enumerable set between A0_L and B1_L is m-complete
     (MPFree_L.v's m_complete_K_of, Smullyan's race on that pair). Uses
     the same two facts as the EI route (A0_L_subset_K_of,
     K_of_B1_L_disjoint), not the eff_insep predicate. CT_L only.
   - Direct: a many-one reduction from MM2 halting
     (DirectUndec/), plus m-completeness of halting by the textbook
     argument (DirectUndec/SigmaComplete.v). CT_L only, and undecidability
     with no axioms at all. It needs divergent runs to be refuted, which
     fails in KA (DirectUndec/FKALoop.v), so it has no KA instance; for
     the CKA encoding in KA, red_leq_fka_direct_fails states the failure
     next to the EI and sandwich results.

   The EI and sandwich routes share everything but one step, how an
   enumerable K_of Pred becomes m-complete (K_of_m_complete_EI vs
   K_of_m_complete_sandwich); the rest (the machine connection Hc, the
   enumerability of K_of Pred, the reduction out of K_of Pred) is the
   same lemma in both. The direct route's problems are equalities over a
   fixed carrier (PreKA_EQ, PreKA_EQ_bin) or have the machine's alphabet
   in the instance (UNIV), so they are close to, but not literally, the
   problems of the other two routes. *)

From Stdlib Require Import Unicode.Utf8.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Synthetic Require Undecidability.
From Undecidability.MinskyMachines Require MM2.
Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.Models.EA_L.
Require Import SyntheticComputability.Models.EA_L_Myhill.
Require Import SyntheticComputability.Models.MPFree_L.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Import SyntheticComputability.Synthetic.reductions.
Require Import SyntheticComputability.Axioms.EA.
Require SyntheticComputability.CRM.principles.

Require kacc.CKAUndec.Glue.TLToRTarget kacc.CKAUndec.K.
Require kacc.CKAUndec.KEnumerable kacc.CKAUndec.KMComplete.
Require kacc.CKAUndec.FKAMComplete kacc.DirectUndec.FKALoop.
Require kacc.CKAUndec.Glue.BinaryAlphabetConnection.
Require kacc.CKAUndec.BinaryAlphabetMComplete.
Require kacc.Universality.UnivConnection kacc.Universality.UnivMComplete.
Require kacc.DirectUndec.Undec kacc.DirectUndec.Binary.
Require kacc.DirectUndec.UnivDirect kacc.DirectUndec.SigmaComplete.
Require kacc.DirectUndec.FKAUnivLoop.

Notation MP := SyntheticComputability.CRM.principles.MP.

(** * The one step where EI and sandwich differ *)

(* What the machine connection says about Pred: on halting runs with
   output 0 or 1, output 1 holds iff Pred holds. *)
Definition connection (Pred : nat → Prop) : Prop :=
  ∀ (v : Vector.t nat 2) (m : nat),
    m <= 1 → R_TL v m → (m = 1 ↔ Pred (ps 1 * enc 2 v)).

Lemma K_of_m_complete_sandwich (Pred : nat → Prop) (Hc : connection Pred) :
  CT_L → enumerable (K_of Pred) → m-complete (K_of Pred).
Proof. intros ct Henum. exact (m_complete_K_of ct Pred Hc Henum). Qed.

Lemma K_of_m_complete_EI (Pred : nat → Prop) (Hc : connection Pred) :
  CT_L → MP → enumerable (K_of Pred) → m-complete (K_of Pred).
Proof.
intros ct mp Henum.
exact (m_complete_of_eff_insep_L _ ct mp Henum (eff_insep_K_of_B1_L Hc)).
Qed.

(* KMComplete.v's m_complete_of_K_of with the EI step in place of the
   sandwich step; the reduction f out of K_of Pred is shared. *)
Lemma m_complete_of_K_of_EI {Pred : nat → Prop} {X : Type}
    {P : X → Prop} {f : nat → X} (Hc : connection Pred)
    (Henum : enumerable (K_of Pred)) (Hf : ∀ z, K_of Pred z ↔ P (f z)) :
  CT_L → MP → m-complete P.
Proof.
intros ct mp q Hq.
apply (red_m_transitive (K_of Pred) P).
- exact (K_of_m_complete_EI Hc ct mp Henum Hq).
- exists f. exact Hf.
Qed.

(** * Case study 1: the CKA encoding (machine-specific alphabet) *)

Theorem KA_ineq_m_complete_sandwich :
  CT_L → ∃ c, m-complete (@KEnumerable.KA_ineq c).
Proof. exact KMComplete.KA_ineq_m_complete. Qed.

Theorem KA_ineq_m_complete_EI :
  CT_L → MP → ∃ c, m-complete (@KEnumerable.KA_ineq c).
Proof.
intros ct mp. destruct TLToRTarget.R_TL_R_target_connection as [c Hc].
exists c.
exact (m_complete_of_K_of_EI Hc (KEnumerable.K_enumerable c)
         (KEnumerable.K_to_KA_ineq_spec c) ct mp).
Qed.

Theorem PreKA_EQ_m_complete_direct : CT_L → m-complete Undec.PreKA_EQ.
Proof. exact SigmaComplete.PreKA_EQ_m_complete. Qed.

(* Undecidability, where the routes differ in axioms: the sandwich goes
   through m-completeness (CT_L), EI through creativity (CT_L, no MP),
   the direct route needs nothing. *)

Theorem K_undecidable_sandwich :
  CT_L → ∃ c, ¬ decidable (K.K c).
Proof. exact KMComplete.K_undecidable. Qed.

Theorem K_undecidable_EI : CT_L → ∃ c, ¬ decidable (K.K c).
Proof.
intros ct. destruct (KMComplete.K_creative ct) as [c Hc].
exists c. exact (@creative_undecidable (EA_L ct) _ Hc).
Qed.

Theorem PreKA_EQ_undecidable_direct :
  Undecidability.undecidable Undec.PreKA_EQ.
Proof. exact Undec.PreKA_EQ_undec. Qed.

(** * Case study 1 in KA: the direct route provably fails *)

(* The same encoding with KA derivability (free KA, star induction) in
   place of pre-KA derivability. EI and sandwich go through unchanged,
   since they only ask about halting runs. *)

Theorem KA_ineq_fka_m_complete_sandwich :
  CT_L → ∃ c, m-complete (@FKAMComplete.KA_ineq_fka c).
Proof. exact FKAMComplete.KA_ineq_fka_m_complete. Qed.

Theorem KA_ineq_fka_m_complete_EI :
  CT_L → MP → ∃ c, m-complete (@FKAMComplete.KA_ineq_fka c).
Proof.
intros ct mp.
destruct FKAMComplete.R_TL_R_target_fka_connection as [c Hc].
exists c.
exact (m_complete_of_K_of_EI Hc (FKAMComplete.K_fka_enumerable c)
         (FKAMComplete.K_to_KA_ineq_fka_spec c) ct mp).
Qed.

(* Direct: the map from machines to inequalities is no longer a reduction
   from halting. KA proves the inequality for the two-instruction loop
   [inc_a; dec_a 1], which never halts (DirectUndec/FKALoop.v). *)
Theorem red_leq_fka_direct_fails :
  ¬ (∀ P s1, FKAMComplete.red_leq_fka P s1 → MM2.mm2_terminates P s1).
Proof.
intros H. apply FKALoop.loop_not_terminates.
apply H. exact FKALoop.fka_red_leq_loop.
Qed.

(** * Case study 2: the binary alphabet *)

Theorem KA_ineq_bin_m_complete_sandwich :
  CT_L → m-complete BinaryAlphabetMComplete.KA_ineq_bin.
Proof. exact BinaryAlphabetMComplete.KA_ineq_bin_m_complete. Qed.

Theorem KA_ineq_bin_m_complete_EI :
  CT_L → MP → m-complete BinaryAlphabetMComplete.KA_ineq_bin.
Proof.
intros ct mp.
destruct BinaryAlphabetConnection.R_TL_R_target_connection_bin
  as [c [k [bEnc [Hlen [Hk_pos Hc]]]]].
exact (m_complete_of_K_of_EI Hc
         (BinaryAlphabetMComplete.K_bin_enumerable Hlen Hk_pos)
         (BinaryAlphabetMComplete.K_to_KA_ineq_bin_spec
            (bEnc := bEnc) Hlen Hk_pos) ct mp).
Qed.

Theorem PreKA_EQ_bin_m_complete_direct :
  CT_L → m-complete Binary.PreKA_EQ_bin.
Proof. exact SigmaComplete.PreKA_EQ_bin_m_complete. Qed.

(** * Case study 3: universality *)

(** ** Balanced universality in pre-KA *)

Theorem Univ_m_complete_sandwich :
  CT_L → ∃ c, m-complete (@UnivMComplete.Univ c).
Proof. exact UnivMComplete.Univ_m_complete. Qed.

Theorem Univ_m_complete_EI :
  CT_L → MP → ∃ c, m-complete (@UnivMComplete.Univ c).
Proof.
intros ct mp. destruct UnivConnection.R_TL_R_target_univ_connection as [c Hc].
exists c.
exact (m_complete_of_K_of_EI Hc (UnivMComplete.K_univ_enumerable c)
         (UnivMComplete.K_to_Univ_spec c) ct mp).
Qed.

Theorem UNIV_m_complete_direct : CT_L → m-complete UnivDirect.UNIV.
Proof. exact SigmaComplete.UNIV_m_complete. Qed.

Theorem Univ_bin_m_complete_sandwich :
  CT_L → m-complete UnivMComplete.Univ_bin.
Proof. exact UnivMComplete.Univ_bin_m_complete. Qed.

Theorem Univ_bin_m_complete_EI :
  CT_L → MP → m-complete UnivMComplete.Univ_bin.
Proof.
intros ct mp.
destruct UnivConnection.R_TL_R_target_univ_bin_connection as [c Hc].
exact (m_complete_of_K_of_EI Hc (UnivMComplete.K_univ_bin_enumerable c)
         (UnivMComplete.K_to_Univ_bin_spec c) ct mp).
Qed.

(* No direct counterpart over the binary carrier (not attempted). *)

(** ** Full universality in KA: the direct route provably fails *)

Theorem Univ_top_m_complete_sandwich :
  CT_L → ∃ c, m-complete (@UnivMComplete.Univ_top c).
Proof. exact UnivMComplete.Univ_top_m_complete. Qed.

Theorem Univ_top_m_complete_EI :
  CT_L → MP → ∃ c, m-complete (@UnivMComplete.Univ_top c).
Proof.
intros ct mp.
destruct UnivConnection.R_TL_R_target_univ_top_connection as [c Hc].
exists c.
exact (m_complete_of_K_of_EI Hc (UnivMComplete.K_univ_top_enumerable c)
         (UnivMComplete.K_to_Univ_top_spec c) ct mp).
Qed.

(* Direct: fails. KA proves full universality for FKALoop.v's loop_prog,
   which never halts (DirectUndec/FKAUnivLoop.v), so in KA this encoding
   gives no reduction from halting. *)
Definition Univ_top_direct_fails :=
  FKAUnivLoop.fka_univ_top_not_terminates_fails.

Theorem Univ_top_bin_m_complete_sandwich :
  CT_L → m-complete UnivMComplete.Univ_top_bin.
Proof. exact UnivMComplete.Univ_top_bin_m_complete. Qed.

Theorem Univ_top_bin_m_complete_EI :
  CT_L → MP → m-complete UnivMComplete.Univ_top_bin.
Proof.
intros ct mp.
destruct UnivConnection.R_TL_R_target_univ_top_bin_connection as [c Hc].
exact (m_complete_of_K_of_EI Hc
         (UnivMComplete.K_univ_top_bin_enumerable c)
         (UnivMComplete.K_to_Univ_top_bin_spec c) ct mp).
Qed.

(** * Assumptions *)

Print Assumptions KA_ineq_m_complete_EI.
Print Assumptions KA_ineq_m_complete_sandwich.
Print Assumptions PreKA_EQ_m_complete_direct.
Print Assumptions K_undecidable_EI.
Print Assumptions K_undecidable_sandwich.
Print Assumptions PreKA_EQ_undecidable_direct.
Print Assumptions KA_ineq_fka_m_complete_EI.
Print Assumptions KA_ineq_fka_m_complete_sandwich.
Print Assumptions red_leq_fka_direct_fails.
Print Assumptions Univ_top_bin_m_complete_EI.
Print Assumptions Univ_top_bin_m_complete_sandwich.
Print Assumptions Univ_top_direct_fails.
