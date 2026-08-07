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
Require Import ssreflect.
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

(* K is creative -- an enumerable set whose complement's
   non-enumerability is witnessed by an explicit, effective function
   (simple.v's `creative`). This is the standard textbook notion Myhill's
   theorem (creative_to_m_complete, below) starts from, and is a more
   immediately legible statement of Theorem 17/18's content than
   eff_insep_shape itself for a reader unfamiliar with the effective-
   inseparability idiom: "K is creative" says outright that no algorithm
   enumerating a superset of K's complement can be extended to enumerate
   K's complement exactly, with the extension counterexample computed
   uniformly. *)

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
   giving exactly `CT_L -> MP -> exists c, creative (K c)`, with the EA
   instance silently EA_L ct throughout. *)

Section KCreative.

Variable ct : CT_L.
Local Instance EA_inst : EA := EA_L ct.

Theorem K_creative (MP_assm : MP) : exists c : nat, creative (K c).
Proof.
destruct eff_insep_shape_K_B1_L as [c Hc].
exists c.
eapply (eff_insep_to_creative MP_assm).
apply eff_insep_iff_shape.
eapply eff_insep_shape_W_iff; [| exact Hc].
intros i x. symmetry. exact (W_psi_L_iff i x).
Qed.

End KCreative.

Theorem K_m_complete : CT_L -> MP -> exists c : nat, m-complete (K c).
Proof.
intros ct MP_assm.
destruct (K_creative ct MP_assm) as [c Hc].
exists c.
exact (creative_to_m_complete MP_assm _ Hc).
Qed.

