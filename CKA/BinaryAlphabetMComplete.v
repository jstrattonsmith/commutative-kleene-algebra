(* Closes task #40 (Arthur's comment 2, fully): mirrors CKA/Glue/
   TLToRTarget.v / CKA/K.v / CKA/KEnumerable.v / CKA/KMComplete.v's
   SUPERSET-transport strategy at the embedded (binary-alphabet) level,
   using CKA/Glue/BinaryAlphabetConnection.v's R_TL_R_target_connection_bin
   in place of the unembedded R_TL_R_target_connection.

   Per the Azevedo de Amorim et al. paper's own Theorem 18/19 proof
   (checked directly): their reduction never characterizes a divergent
   run either -- A/B (Theorem 17) are BOTH defined only over HALTING
   computations, and their A' superset (Theorem 19's proof) only ever
   needs "A subset A'" (halting-and-accepting) and "A' disjoint from B"
   (halting-and-rejecting), never anything about inputs outside A u B.
   This is the SAME strategy this project's own Computability/TL_Bridge.v/
   CKA/K.v already use for the unembedded K. So this file needs NO new
   completeness argument beyond what's already proven -- it strictly
   mirrors the existing chain, plugging in the embedded halting-case
   lemmas in place of the unembedded ones. The genuinely-unprovable
   divergent-run gap documented in CKA/BinaryAlphabet.v is real but not
   on this critical path.

   Sections 2-3 below (GenericK, GenericEnumerable) are GENERALIZATIONS
   of CKA/K.v's Section Splice6 and CKA/KEnumerable.v respectively --
   parametrized over an arbitrary Pred/carrier monoid T rather than the
   specific K/TmMonoid, so both the original (unembedded) K and this
   file's K_bin are ONE-LINE instantiations of the SAME proofs instead
   of two copies. They are kept here rather than pushed further into
   Computability/ (where their genericity would in principle belong,
   matching InseparabilityCore.v/enumerable.v's own content) -- a
   scoped judgment call, not an oversight: K_of depends on z_vec/A0_L/
   B1_L/T_L_Uniform.R_TL (CKA/K.v-adjacent, not yet separately housed),
   and splitting them out would touch CKA/K.v's own z_vec too. Flagged
   as a possible future refinement, not attempted here. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import MM2 MMA.
Import MM2Notations.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
Import vec_notations.
Import Vector.VectorNotations.
From Undecidability.MinskyMachines Require Import mm_defs mma_defs fractran_mma
  mma_utils.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts
  DecidabilityFacts MoreReducibilityFacts.
From stdpp Require base decidable.
From kacc Require Import KA.algebra KA.pre_ka KA.enumerable.
From kacc Require Import CKA.Glue.TLToRTarget Computability.TL_Bridge.
From kacc Require Import Computability.InseparabilityCore.
From kacc Require Import MM2.Simulator MM2.Splice.
From kacc Require Import CKA.Glue.MM2ToKATerm.
From kacc Require Import CKA.BinaryAlphabet.
From kacc Require Import CKA.Glue.BinaryAlphabetConnection.
From kacc Require Import CKA.K CKA.KEnumerable.
From kacc Require Import Computability.EA_L Computability.Myhill.
From kacc Require Import CKA.KMComplete.
Require kacc.CKA.Encoding.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparability.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.
Require Import SyntheticComputability.Synthetic.Definitions
  SyntheticComputability.Synthetic.EnumerabilityFacts
  SyntheticComputability.Synthetic.reductions.
Require Import SyntheticComputability.Shared.embed_nat.

(* algebra.v/pre_ka.v open ka_scope, whose `0`/`1` typeclass-resolved
   literals otherwise hijack every plain nat literal below (vec_nil
   cons cells, MM2 states, etc.) -- re-opening nat_scope last makes it
   win ties for bare numerals, avoiding a %nat annotation on every
   single occurrence. *)
Open Scope nat_scope.

(* --- 2. GENERALIZATION of CKA.K.v's Section Splice6: the
   "connection -> eff_insep_core" argument (A0_L_subset_K/
   K_B1_L_disjoint/eff_insep_K_B1_L there) never actually touches
   R_target/red_leq's own definition -- it only uses the abstract
   Hc-style characterization (m=1 <-> Pred y) as a black box. Pulling
   that out as a lemma over an ARBITRARY Pred : nat -> Prop makes both
   the original (unembedded) K and this file's K_bin ONE-LINE
   instantiations of the SAME proof, instead of two copies of it.
   eff_insep_core_superset (Computability/InseparabilityCore.v) is
   itself already fully generic and reused unchanged underneath. *)

Section GenericK.

Variable (Pred : nat -> Prop).
Hypothesis Hc : forall (v : Vector.t nat 2) (m : nat),
  (m <= 1)%nat -> T_L_Uniform.R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)).

Definition K_of (z : nat) : Prop :=
  Pred (ps 1 * enc 2 (CKA.K.z_vec z)).

Lemma A0_L_subset_K_of (z : nat) : A0_L z -> K_of z.
Proof.
intros HA. apply theta_ours_L_iff in HA.
assert (HR1 : T_L_Uniform.R_TL (CKA.K.z_vec z) 1)
  by (apply R_TL_iff; exact HA).
exact (proj1 (@Hc (CKA.K.z_vec z) 1 (Nat.le_refl 1) HR1) eq_refl).
Qed.

Lemma K_of_B1_L_disjoint (z : nat) : K_of z -> ~ B1_L z.
Proof.
intros HK HB. apply theta_ours_L_iff in HB.
assert (HR0 : T_L_Uniform.R_TL (CKA.K.z_vec z) 0)
  by (apply R_TL_iff; exact HB).
assert (Heq : 0 = 1)
  by (apply (@Hc (CKA.K.z_vec z) 0 (Nat.le_0_l 1) HR0); exact HK).
discriminate Heq.
Qed.

Theorem eff_insep_K_of_B1_L : eff_insep_core W_L K_of B1_L.
Proof.
apply (eff_insep_core_superset (A := A0_L)).
- exact (eff_insep_shape_to_core eff_insep_A0_B1_L_via_generic).
- exact A0_L_subset_K_of.
- exact K_of_B1_L_disjoint.
Qed.

End GenericK.

(* Sanity check: the generalization above is faithful to what
   CKA.K.v already proves for the unembedded K, not a
   different/weaker claim -- K c is DEFINITIONALLY K_of (R_target c). *)
Lemma K_eq_K_of_R_target (c : nat) : CKA.K.K c = K_of (R_target c).
Proof. reflexivity. Qed.

Definition K_bin (c k : nat) (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat) : nat -> Prop :=
  K_of (fun y => red_leq' (c := c) Hlen Hk_pos (1, (y, 0))%nat).

Theorem eff_insep_K_bin_B1_L :
  exists (c k : nat) (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  eff_insep_core W_L (K_bin (c := c) Hlen Hk_pos) B1_L.
Proof.
destruct R_TL_R_target_connection_bin as [c [k [bEnc [Hlen [Hk_pos Hc]]]]].
exists c, k, bEnc, Hlen, Hk_pos.
exact (eff_insep_K_of_B1_L Hc).
Qed.

(* --- 3. GENERALIZATION of CKA.KEnumerable.v: ka_sqsubseteq_enumerable
   (enumerable.v) is already generic over ANY carrier monoid with
   countable, Leibniz-equal ≡. The only CKA-specific content in
   CKA.KEnumerable.v is "K is a fixed-rhs slice of ⊑", a reflexivity-level
   fact -- pulling THAT out generically makes both K and K_bin's
   enumerability one-line instantiations of the same lemma, instead of
   two copies of TmMonoid/Tm_equiv_enumerable/K_to_KA_ineq. *)

Section GenericEnumerable.

Context (T : monoid).

(* NOTE: sqsubseteq/equiv are spelled out (not written via the ⊑/≡
   notations) throughout this section -- those notations live in
   stdpp_scope, which conflicts (hard notation-level clash, not just
   ambiguity) with vec_notations' `##` needed elsewhere in this file
   for the MMA/FRACTRAN Psplice machinery; both can't be Import-opened
   in the same file. `Countable`'s own precondition (EqDecision) must
   already be resolvable BEFORE `Countable` itself is declared below,
   hence HeqT coming first. *)

Context `{HeqT : !base.RelDecision (@Logic.eq (monoid_car T))}.
Context `{!countable.Countable (monoid_car T)}
  (HLeibniz : base.LeibnizEquiv (monoid_car T)).

Instance T_equiv_dec (x y : monoid_car T) : base.Decision (base.equiv x y).
Proof.
destruct (HeqT x y) as [-> | Hne].
- left. reflexivity.
- right. intros Heq. apply Hne.
  exact (@base.leibniz_equiv (monoid_car T) _ HLeibniz x y Heq).
Defined.

Lemma T_equiv_enumerable :
  enumerable (fun p : monoid_car T * monoid_car T => base.equiv (fst p) (snd p)).
Proof.
apply: dec_count_enum.
2: exact (@countable_enumerableT (monoid_car T * monoid_car T) _ _).
exists (fun p => decidable.bool_decide (base.equiv (fst p) (snd p))).
intros p. unfold Undecidability.Synthetic.Definitions.reflects.
symmetry. apply decidable.bool_decide_eq_true.
Qed.

Definition KA_ineq_over : ka_term (monoid_car T) * ka_term (monoid_car T) -> Prop :=
  fun p => base.sqsubseteq (fst p) (snd p).

Theorem KA_ineq_over_enumerable : enumerable KA_ineq_over.
Proof. exact: ka_sqsubseteq_enumerable T_equiv_enumerable. Qed.

Theorem slice_enumerable
    (lhs : nat -> ka_term (monoid_car T)) (rhs : ka_term (monoid_car T)) :
  enumerable (fun z => base.sqsubseteq (lhs z) rhs).
Proof.
apply: (@enumerable_red nat (ka_term (monoid_car T) * ka_term (monoid_car T))
  (fun z => base.sqsubseteq (lhs z) rhs) KA_ineq_over).
- exists (fun z => (lhs z, rhs)). intros z. reflexivity.
- exists (fun n => Some n). intros n. exists n. reflexivity.
- apply: discrete_prod; apply/discrete_iff; constructor; exact: ka_term_eq_dec.
- exact: KA_ineq_over_enumerable.
Qed.

End GenericEnumerable.

Definition Tm_bin : monoid :=
  prod_monoid (list_monoid (option_setoid bool_setoid))
              (list_monoid (option_setoid bool_setoid)).

Instance Tm_bin_eqdec : base.RelDecision (@Logic.eq (monoid_car Tm_bin)).
Proof. apply _. Defined.

Instance Tm_bin_countable : countable.Countable (monoid_car Tm_bin).
Proof. apply _. Defined.

Instance Tm_bin_leibniz : base.LeibnizEquiv (monoid_car Tm_bin).
Proof. apply _. Defined.

Theorem K_bin_enumerable (c k : nat)
    (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat) :
  enumerable (K_bin (c := c) Hlen Hk_pos).
Proof.
have [f Hf] := @slice_enumerable Tm_bin _ _ Tm_bin_leibniz
  (fun z => red_lb' (c := c) bEnc
    (1, (ps 1 * enc 2 (CKA.K.z_vec z), 0))%nat)
  (red_ub' Hlen Hk_pos).
exists f. intros z. rewrite /K_bin /K_of red_leq'_shape. exact: Hf z.
Qed.

(* --- 4. GENERALIZATION of CKA.KMComplete.v: eff_insep_shape_superset
   (EffectiveInseparabilityTransport.v, sibling project) is already
   generic over any A'/enumerability witness -- the only CKA-specific
   content is bundling K_of Pred's own enumerability in. *)

Theorem eff_insep_shape_K_of_B1_L (Pred : nat -> Prop)
    (Hc : forall (v : Vector.t nat 2) (m : nat),
      (m <= 1)%nat -> T_L_Uniform.R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)))
    (Henum : enumerable (K_of Pred)) :
  eff_insep_shape W_L (K_of Pred) B1_L.
Proof.
eapply EffectiveInseparabilityTransport.eff_insep_shape_superset.
- exact eff_insep_A0_B1_L_via_generic.
- exact Henum.
- exact (A0_L_subset_K_of Hc).
- exact (K_of_B1_L_disjoint Hc).
Qed.

Theorem eff_insep_shape_K_bin_B1_L :
  exists (c k : nat) (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  eff_insep_shape W_L (K_bin (c := c) Hlen Hk_pos) B1_L.
Proof.
destruct R_TL_R_target_connection_bin as [c [k [bEnc [Hlen [Hk_pos Hc]]]]].
exists c, k, bEnc, Hlen, Hk_pos.
exact (eff_insep_shape_K_of_B1_L Hc (K_bin_enumerable Hlen Hk_pos)).
Qed.

(* --- 5. GENERALIZATION of EA_L.v/CKA.KMComplete.v: everything
   from eff_insep_to_creative onward is already generic over an
   arbitrary Prop family with the eff_insep_shape property -- the only
   CKA-specific step is which set (K or K_bin) supplies that shape. This
   machinery (creative_of_eff_insep_shape/m_complete_of_eff_insep_shape)
   lives in Computability/Myhill.v and is reused unchanged here. *)

Theorem K_bin_m_complete :
  CT_L -> MP ->
  exists (c k : nat) (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  m-complete (K_bin (c := c) Hlen Hk_pos).
Proof.
intros ct MP_assm.
destruct eff_insep_shape_K_bin_B1_L as [c [k [bEnc [Hlen [Hk_pos Hshape]]]]].
exists c, k, bEnc, Hlen, Hk_pos.
exact (m_complete_of_eff_insep_shape ct MP_assm Hshape).
Qed.

(* --- 6. GENERALIZATION of CKA.KMComplete.v: red_m_transitive is
   generic (pure many-one reduction composition, no enumerability
   side-condition on the target). The only CKA-specific content is the
   trivial (reflexivity) reduction witnessing that a Pred-slice is a
   slice of KA_ineq_over.

   Unlike K_bin (existentially quantified over c/k/bEnc/...), the
   FINAL statement KA_ineq_bin needs no such existential: Tm_bin is a
   single, FIXED carrier (the canonical two-symbol alphabet), the same
   regardless of which machine c is being encoded -- matching exactly
   how the source paper's own Theorem 18 states undecidability of a
   single, fixed T{0,1}/K{0,1}/L{0,1}, not one instance per machine.
   The existentials over c/k/bEnc/Hlen/Hk_pos are used only INSIDE the
   proof, to witness the reduction -- KA_ineq_bin itself doesn't
   mention them. This is the paper's Theorem 18/19 for the actual
   KA-term inequality relation, over the canonical binary alphabet,
   Sigma^0_1-complete, closing Arthur's comment 2 in full. *)

Definition KA_ineq_bin : ka_term (monoid_car Tm_bin) * ka_term (monoid_car Tm_bin) -> Prop :=
  @KA_ineq_over Tm_bin.

Definition K_to_KA_ineq_bin (c k : nat)
    (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat) (z : nat) :
    ka_term (monoid_car Tm_bin) * ka_term (monoid_car Tm_bin) :=
  (red_lb' (c := c) bEnc (1, (ps 1 * enc 2 (CKA.K.z_vec z), 0))%nat,
   red_ub' (c := c) Hlen Hk_pos).

Lemma K_to_KA_ineq_bin_spec (c k : nat)
    (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat) (z : nat) :
  K_bin (c := c) Hlen Hk_pos z <-> KA_ineq_bin (K_to_KA_ineq_bin (bEnc := bEnc) Hlen Hk_pos z).
Proof. rewrite /K_bin /K_of /K_to_KA_ineq_bin /KA_ineq_bin /=. exact: red_leq'_shape. Qed.

Theorem KA_ineq_bin_m_complete : CT_L -> MP -> m-complete KA_ineq_bin.
Proof.
intros ct MP_assm.
destruct (K_bin_m_complete ct MP_assm) as [c [k [bEnc [Hlen [Hk_pos Hc]]]]].
intros q Hq.
apply (red_m_transitive (K_bin (c := c) Hlen Hk_pos) KA_ineq_bin).
- exact (Hc q Hq).
- exists (K_to_KA_ineq_bin (bEnc := bEnc) Hlen Hk_pos).
  exact (K_to_KA_ineq_bin_spec Hlen Hk_pos).
Qed.
