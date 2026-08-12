(* Generic Myhill's-theorem-style machinery, extracted from
   CKAUndec.KMComplete.v (eff_insep_shape_W_iff) and
   CKAUndec.BinaryAlphabetMComplete.v (formerly its GenericCreative section)
   (creative_of_eff_insep_shape/m_complete_of_eff_insep_shape). Zero
   MM2/KA content: everything here is stated over an arbitrary Prop
   family P, not K or K_bin -- the only CKA-specific step left to the
   caller is which set supplies the eff_insep_shape hypothesis.

   Two hypotheses are needed, for two SEPARATE, independent reasons:
   - CT_L (Church's Thesis for L): to build EA_L at all.
   - MP (Markov's Principle): needed inside eff_insep_to_creative
     itself, to convert a `part`-valued/partial separating witness into
     a decidable total one -- this is NOT subsumed by CT_L, it is a
     genuinely separate cost of the underlying Myhill's-theorem-style
     argument, regardless of which numbering is used. *)

From Stdlib Require Import Unicode.Utf8.
Require Import ssreflect.
From kacc Require Import Computability.EA_L.

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

(* `creative` is stated relative to an ambient EA instance's own
   canonical numbering (simple.v's productive/creative are defined via
   `W`, which is itself EA-instance-relative, resolved through EA's
   `Existing Class` declaration) -- so the instance has to be in scope
   before the THEOREM STATEMENT elaborates, not just inside the proof.
   `ct : CT_L` is what supplies it (via EA_L), so it has to become a
   section Variable here rather than an intro'd hypothesis; this is the
   same shape EA_L.v itself already uses (Section BuildEA_L, Hypothesis
   ct : CT_L). EA_inst itself needs `Local Instance`, not `Let` --
   typeclass resolution auto-registers Variable/Context section
   hypotheses of a Class type, but not plain Let-bound local
   definitions, and a Let here left `creative`'s implicit EA_inst
   argument unresolved even with EA_L ct sitting right there in scope.
   Local Instance forces the registration explicitly; it gets
   substituted away (not re-generalized) when the section closes,
   giving exactly `forall ct : CT_L, forall P, MP -> ... -> creative P`,
   with the EA instance silently EA_L ct throughout. *)

Section GenericCreative.

Variable ct : CT_L.
Local Instance EA_inst : EA := EA_L ct.

Theorem creative_of_eff_insep_shape (P : nat -> Prop) (MP_assm : MP) :
  eff_insep_shape W_L P B1_L -> creative P.
Proof.
intros Hshape.
eapply (eff_insep_to_creative MP_assm).
eapply eff_insep_shape_W_iff; [| exact Hshape].
intros i x. symmetry. exact (W_psi_L_iff i x).
Qed.

End GenericCreative.

Theorem m_complete_of_eff_insep_shape (P : nat -> Prop) :
  CT_L -> MP -> eff_insep_shape W_L P B1_L -> m-complete P.
Proof.
intros ct MP_assm Hshape.
exact (creative_to_m_complete MP_assm _ (creative_of_eff_insep_shape ct MP_assm Hshape)).
Qed.
