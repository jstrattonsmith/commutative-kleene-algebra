(* Sigma^0_1-completeness of the full KA-term inequality relation KA_ineq
   (not just its K-slice), closing the source paper's Theorem 18/19 over
   the machine-specific alphabet under one hypothesis, CT_L (Church's
   Thesis for Rocq's L). Markov's principle is not needed.

   --- 1. K_m_complete: K is sandwiched between the halting sets A0_L and
   B1_L (Models/T_L_Bridge.v's A0_L_subset_K_of and K_of_B1_L_disjoint,
   from CKAUndec/Glue/TLToRTarget.v's connection), and it is enumerable
   (CKAUndec/KEnumerable.v). Models/MPFree_L.v's m_complete_K_of turns
   exactly these facts into m-completeness: every enumerable set between
   A0_L and B1_L is m-complete, by Smullyan's race argument on that pair.
   This does not go through the eff_insep predicate.

   --- 2. KA_ineq_m_complete: K is one slice of KA_ineq, fixing the
   right-hand side to red_ub Prog, whereas the source paper states
   Theorem 18/19 over the full relation {(x,y) | x ⊑ y}.
   CKAUndec/KEnumerable.v's reduction K_to_KA_ineq (K ⪯ₘ KA_ineq) carries
   m-completeness from K to KA_ineq via red_m_transitive. The generic
   m_complete_of_K_of packages steps 1-2 for any K_of Pred, and is reused
   by CKAUndec/BinaryAlphabetMComplete.v and Universality/UnivMComplete.v.

   --- 3. K_creative, a separate result that the above does not use: K's
   effective inseparability from B1_L (CKAUndec/K.v's eff_insep_K_B1_L,
   Theorem 17) gives creativity under CT_L, via Models/EA_L_Myhill.v's
   creative_of_eff_insep_L. EA_L ct is the EA instance, so `creative`
   (stated over an ambient EA's W) and eff_insep (over W_L) talk about the
   same numbering. Going on from creativity to m-completeness by Myhill's
   theorem would need MP: ReducibilityDegrees/MPFree.v shows that
   "creative -> m-complete" is equivalent to MP in general, and
   MPFree_L.v that so is "enumerable and eff_insep from B1_L ->
   m-complete". *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
Require Import ssreflect.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import CKAUndec.K.
From kacc Require Import CKAUndec.KEnumerable.
Require Import SyntheticComputability.Models.EA_L.
Require Import SyntheticComputability.Models.EA_L_Myhill.
Require Import SyntheticComputability.Models.MPFree_L.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.Synthetic.reductions.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.Models.T_L_Uniform.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.

(* The whole route at once: a problem P that K_of Pred reduces to (by f)
   is m-complete under CT_L. Generic over the Prop family Pred, so that
   CKAUndec/BinaryAlphabetMComplete.v and Universality/UnivMComplete.v
   reuse it. *)
Theorem m_complete_of_K_of {Pred : nat -> Prop} {X : Type} {P : X -> Prop}
    {f : nat -> X}
    (Hc : forall (v : Vector.t nat 2) (m : nat),
      (m <= 1)%nat -> R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)))
    (Henum : enumerable (K_of Pred))
    (Hf : forall z, K_of Pred z <-> P (f z)) :
  CT_L -> m-complete P.
Proof.
intros ct q Hq.
apply (red_m_transitive (K_of Pred) P).
- exact (m_complete_K_of ct Pred Hc Henum q Hq).
- by exists f.
Qed.

(* `creative` is stated relative to an ambient EA instance's own
   canonical numbering (simple.v's productive/creative are defined via
   `W`, which is itself EA-instance-relative), so the instance has to be
   in scope before the THEOREM STATEMENT elaborates. `ct : CT_L` supplies
   it (via EA_L), so it is a section Variable and EA_L ct a
   `Local Instance` (a `Let` is not found by typeclass resolution); the
   instance is substituted away when the section closes, giving
   `CT_L -> exists c, creative (CKAUndec.K.K c)`. *)

Section KCreative.

Variable ct : CT_L.
Local Instance EA_inst : EA := EA_L ct.

Theorem K_creative : exists c : nat, creative (CKAUndec.K.K c).
Proof.
destruct eff_insep_K_B1_L as [c Hc].
exists c.
exact (creative_of_eff_insep_L ct (CKAUndec.K.K c) (K_enumerable c) Hc).
Qed.

End KCreative.

Theorem K_m_complete : CT_L -> exists c : nat, m-complete (CKAUndec.K.K c).
Proof.
intros ct. destruct R_TL_R_target_connection as [c Hc].
exists c.
exact (m_complete_K_of ct _ Hc (K_enumerable c)).
Qed.

Theorem KA_ineq_m_complete : CT_L -> exists c : nat, m-complete (@KA_ineq c).
Proof.
intros ct. destruct R_TL_R_target_connection as [c Hc].
exists c.
exact (m_complete_of_K_of Hc (K_enumerable c) (K_to_KA_ineq_spec c) ct).
Qed.

(* Closes the source paper's Theorem 18 analogue over the machine-specific
   alphabet: raw undecidability of K, conditional on CT_L -- via
   ReducibilityDegrees/simple.v's m_complete_undecidable, not a fresh
   argument. Getting from K's hypothetical decision procedure to a
   W_L-index needs CT_L (EA_L is only ever built from it). *)
Theorem K_undecidable : CT_L -> exists c : nat, ~ decidable (CKAUndec.K.K c).
Proof.
intros ct.
destruct (K_m_complete ct) as [c Hc].
exists c.
exact (@m_complete_undecidable (EA_L ct) _ (K_enumerable c) Hc).
Qed.
