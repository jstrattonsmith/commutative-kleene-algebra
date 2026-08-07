(* The payoff of EA_L.v: reuse coq-synthetic-computability's EXISTING,
   already-proven generic machinery (simple.v / EffectiveInseparability.v
   -- productive, creative, eff_insep_to_m_complete) directly, by
   supplying EA_L as the EA instance, instead of re-deriving
   productive/creative/creative_to_m_complete from scratch against W_L.

   Two hypotheses are needed, for two SEPARATE, independent reasons:
   - CT_L (Church's Thesis for L): to build EA_L at all (EA_L.v).
   - MP (Markov's Principle): needed inside eff_insep_to_m_complete
     itself, to convert a `part`-valued/partial separating witness into
     a decidable total one -- this is NOT subsumed by CT_L, it is a
     genuinely separate cost of the underlying Myhill's-theorem-style
     argument, regardless of which numbering is used. *)

From Stdlib Require Import Unicode.Utf8.
From kacc Require Import EA_L.
From kacc Require Import Theorem17_KATerm.
From kacc Require Import Theorem17_Full.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparability.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.

(* --- eff_insep_shape is invariant under replacing W with a pointwise-
   equivalent numbering -- a generic, mechanical transport lemma. --- *)

Lemma eff_insep_shape_W_iff (W1 W2 : nat -> nat -> Prop) (A B : nat -> Prop) :
  (forall c x, W1 c x <-> W2 c x) -> eff_insep_shape W1 A B -> eff_insep_shape W2 A B.
Proof.
intros HW [HAenum [HBenum [Hdisj [f Hf]]]].
split; [exact HAenum |]. split; [exact HBenum |]. split; [exact Hdisj |].
exists f. intros i j Hi Hj Hij.
destruct (Hf i j) as [k [Hk [Hki Hkj]]].
- intros x Hx % Hi. apply HW. exact Hx.
- intros x Hx % Hj. apply HW. exact Hx.
- intros x Hx % HW. intros Hy % HW. exact (Hij x Hx Hy).
- exists k. split; [exact Hk |]. split.
  + intros Hk1 % HW. exact (Hki Hk1).
  + intros Hk2 % HW. exact (Hkj Hk2).
Qed.

Theorem K_m_complete : CT_L -> MP -> exists c : nat, m-complete (K c).
Proof.
intros ct MP_assm.
pose (EA_inst := EA_L ct).
destruct eff_insep_shape_K_B1_L as [c Hc].
exists c.
assert (Hei : eff_insep (K c) B1_L).
{ apply eff_insep_iff_shape.
  eapply eff_insep_shape_W_iff; [| exact Hc].
  intros i x. symmetry. exact (W_psi_L_iff i x). }
exact (eff_insep_to_m_complete MP_assm _ _ Hei).
Qed.
