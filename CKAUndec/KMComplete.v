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
   K's m-completeness with that same reduction via red_m_transitive
   transports m-completeness out of K and into KA_ineq. The generic
   m_complete_of_K_of packages this route for any K_of Pred, and is
   reused by CKAUndec/BinaryAlphabetMComplete.v and
   Universality/UnivMComplete.v. *)

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
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityTransport.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.
Require Import SyntheticComputability.Synthetic.reductions.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.Models.T_L_Uniform.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.

(* Generic over the Prop family Pred, so that CKAUndec/BinaryAlphabetMComplete.v
   and Universality/UnivMComplete.v reuse it: eff_insep_shape_superset
   (EffectiveInseparabilityTransport.v) is already generic over any
   A'/enumerability witness, and the only CKA-specific content is bundling
   K_of Pred's own enumerability in. *)
Theorem eff_insep_shape_K_of_B1_L {Pred : nat -> Prop}
    (Hc : forall (v : Vector.t nat 2) (m : nat),
      (m <= 1)%nat -> R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)))
    (Henum : enumerable (K_of Pred)) :
  eff_insep_shape W_L (K_of Pred) B1_L.
Proof.
eapply EffectiveInseparabilityTransport.eff_insep_shape_superset.
- exact eff_insep_A0_B1_L_via_generic.
- exact Henum.
- exact (A0_L_subset_K_of Hc).
- exact (K_of_B1_L_disjoint Hc).
Qed.

(* The whole route at once: a problem P that K_of Pred reduces to (by f)
   is m-complete under CT_L and MP. *)
Theorem m_complete_of_K_of {Pred : nat -> Prop} {X : Type} {P : X -> Prop}
    {f : nat -> X}
    (Hc : forall (v : Vector.t nat 2) (m : nat),
      (m <= 1)%nat -> R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)))
    (Henum : enumerable (K_of Pred))
    (Hf : forall z, K_of Pred z <-> P (f z)) :
  CT_L -> MP -> m-complete P.
Proof.
intros ct MP_assm q Hq.
apply (red_m_transitive (K_of Pred) P).
- exact (m_complete_of_eff_insep_shape ct MP_assm
           (eff_insep_shape_K_of_B1_L Hc Henum) Hq).
- by exists f.
Qed.

Theorem eff_insep_shape_K_B1_L :
  exists c : nat, eff_insep_shape W_L (CKAUndec.K.K c) B1_L.
Proof.
destruct R_TL_R_target_connection as [c Hc].
exists c. exact (eff_insep_shape_K_of_B1_L Hc (K_enumerable c)).
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
intros ct MP_assm. destruct R_TL_R_target_connection as [c Hc].
exists c.
exact (m_complete_of_K_of Hc (K_enumerable c) (K_to_KA_ineq_spec c) ct MP_assm).
Qed.

(* Closes the source paper's Theorem 18 analogue over the machine-specific
   alphabet: raw undecidability of K, conditional on the same two
   hypotheses K_m_complete already needs -- via
   ReducibilityDegrees/simple.v's m_complete_undecidable, not a fresh
   argument. Genuinely conditional, not axiom-free: getting from K's
   hypothetical decision procedure to a W_L-index needs CT_L (EA_L is
   only ever built from it), and the creative-set route
   m_complete_undecidable goes through needs MP too (via
   eff_insep_to_creative's own use of MP_to_MP_partial). *)
Theorem K_undecidable : CT_L -> MP -> exists c : nat, ~ decidable (CKAUndec.K.K c).
Proof.
intros ct MP_assm.
destruct (K_m_complete ct MP_assm) as [c Hc].
exists c.
exact (@m_complete_undecidable (EA_L ct) _ (K_enumerable c) Hc).
Qed.
