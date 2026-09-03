(* The final chain from K's bundled effective inseparability from B1_L
   to Sigma^0_1-completeness of the full KA-term inequality relation
   KA_ineq (not just its K-slice) -- the terminal theorem of this
   development, closing the source paper's Theorem 18/19 over the
   machine-specific alphabet, conditional on two hypotheses: CT_L
   (Church's Thesis for Rocq's L) and MP (Markov's Principle).

   --- 1. eff_insep_shape_K_B1_L: upgrades CKAUndec/K.v's eff_insep_core
   result to the fully bundled eff_insep_shape, now that K is known
   enumerable (CKAUndec/KEnumerable.v) -- real, axiom-free effective
   inseparability of K (the actual KA-term/red_leq level set) from B1_L,
   over the same numbering W_L throughout (Kuznetsov's Proposition 9
   applied again, this time with its enumerability hypothesis genuinely
   discharged).

   coq-synthetic-computability's generic EffectiveInseparability.v
   machinery (eff_insep_to_m_complete, Kuznetsov's Proposition 7 /
   Myhill's theorem) is stated relative to that file's own ambient `W`
   (from an arbitrary EA instance's canonical enumerator), not a free
   `W` parameter the way eff_insep_shape is; using it on
   eff_insep_shape_K_B1_L directly would require `W_L ≡ W` (every
   Coq-enumerable set equals W_L i for some i), a Church's-Thesis-for-L
   fact this development does not establish in general.
   coq-synthetic-computability's Models/EA_L.v and Models/EA_L_Myhill.v
   sidestep this by building a genuine EA instance FROM CT_L (via SMN
   for T_L) instead.

   --- 2. K_creative/K_m_complete: instantiate Models/EA_L_Myhill.v's
   generic Myhill's-theorem machinery (eff_insep_shape_W_iff,
   creative_of_eff_insep_shape, m_complete_of_eff_insep_shape) at
   P := K c, supplying EA_L as the EA instance rather than re-deriving
   productive/creative/creative_to_m_complete from scratch against W_L.

   --- 3. KA_ineq_m_complete: K_m_complete only shows m-completeness of
   K itself, a SLICE of the full KA-term inequality relation KA_ineq
   (CKAUndec/KEnumerable.v) -- fixing the right-hand side to one
   specific term, red_ub Prog, and varying only the left -- whereas the
   source paper's own Theorem 18/19 are stated over the full relation
   {(x,y) | x ⊑ y}. CKAUndec/KEnumerable.v already builds the reduction
   K_to_KA_ineq witnessing K ⪯ₘ KA_ineq (used there in the opposite
   direction, to import KA_ineq's enumerability into K); composing
   K_m_complete's hardness with that same reduction via
   red_m_transitive transports m-completeness out of K and into
   KA_ineq. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
Require Import ssreflect.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import CKAUndec.K.
From kacc Require Import CKAUndec.KEnumerable.
Require Import SyntheticComputability.Models.EA_L.
Require Import SyntheticComputability.Models.EA_L_Myhill.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparability.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityTransport.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.
Require Import SyntheticComputability.Synthetic.reductions.

Theorem eff_insep_shape_K_B1_L :
  exists c : nat, eff_insep_shape W_L (CKAUndec.K.K c) B1_L.
Proof.
destruct R_TL_R_target_connection as [c Hc].
exists c.
eapply EffectiveInseparabilityTransport.eff_insep_shape_superset.
- exact eff_insep_A0_B1_L_via_generic.
- exact (K_enumerable c).
- exact (@A0_L_subset_K c Hc).
- exact (@K_B1_L_disjoint c Hc).
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
   giving exactly `CT_L -> MP -> exists c, creative (CKAUndec.K.K c)`, with the EA
   instance silently EA_L ct throughout. *)

Section KCreative.

Variable ct : CT_L.
Local Instance EA_inst : EA := EA_L ct.

Theorem K_creative (MP_assm : MP) : exists c : nat, creative (CKAUndec.K.K c).
Proof.
destruct eff_insep_shape_K_B1_L as [c Hc].
exists c.
exact (creative_of_eff_insep_shape ct MP_assm Hc).
Qed.

End KCreative.

Theorem K_m_complete : CT_L -> MP -> exists c : nat, m-complete (CKAUndec.K.K c).
Proof.
intros ct MP_assm.
destruct (K_creative ct MP_assm) as [c Hc].
exists c.
exact (creative_to_m_complete MP_assm _ Hc).
Qed.

Theorem KA_ineq_m_complete : CT_L -> MP -> exists c : nat, m-complete (@KA_ineq c).
Proof.
intros ct MP_assm.
destruct (K_m_complete ct MP_assm) as [c Hc].
exists c.
intros q Hq.
apply (red_m_transitive (CKAUndec.K.K c) (@KA_ineq c)).
- exact (Hc q Hq).
- exists (K_to_KA_ineq c). exact (K_to_KA_ineq_spec c).
Qed.
