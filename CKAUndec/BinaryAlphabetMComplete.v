(* Closes, in full, the requirement that Theorem 18/19 hold over the
   source paper's own canonical, minimal two-symbol alphabet, not just
   the machine-specific alphabet: mirrors CKAUndec/Glue/TLToRTarget.v /
   CKAUndec/K.v / CKAUndec/KEnumerable.v / CKAUndec/KMComplete.v's
   superset-transport strategy at the embedded (binary-alphabet) level,
   using CKAUndec/Glue/BinaryAlphabetConnection.v's
   R_TL_R_target_connection_bin in place of the unembedded
   R_TL_R_target_connection.

   Per the source paper's own Theorem 18/19 proof: their reduction
   never characterizes a divergent run either -- A/B (Theorem 17) are
   both defined only over halting computations, and their A' superset
   (Theorem 19's proof) only ever needs "A subset A'"
   (halting-and-accepting) and "A' disjoint from B"
   (halting-and-rejecting), never anything about inputs outside A u B
   -- the same strategy coq-synthetic-computability's Models/
   T_L_Bridge.v and CKAUndec/K.v already use for the unembedded K. So
   this file needs no new completeness argument beyond what is already
   proven: it mirrors the existing chain, plugging in the embedded
   halting-case lemmas in place of the unembedded ones. The
   genuinely-unprovable divergent-run gap documented in
   CKAUndec/BinaryAlphabet.v is real but not on this critical path.

   K_bin/K_bin_enumerable are one-line instantiations of two generic
   constructions, imported rather than redefined locally: the
   "connection -> effective inseparability" argument
   (coq-synthetic-computability's Models/T_L_Bridge.v, generalizing
   CKAUndec/K.v's own instantiation) and the enumerability argument
   (KA/enumerable.v). K_eq_K_of_R_target verifies this generic route is
   faithful to CKAUndec/KMComplete.v's argument -- K and the new K_bin
   are proven by the SAME lemmas, not two copies.

   Closes with KA_ineq_bin_m_complete : CT_L -> MP -> m-complete
   KA_ineq_bin -- the final theorem closing the canonical-alphabet
   requirement in full. Unlike KA_ineq_m_complete (one instance per
   machine c), this needs no existential over c: the embedded carrier
   Tm_bin is a single, fixed algebra (the canonical two-symbol
   alphabet), independent of which machine is encoded, exactly matching
   how the source paper states its own Theorem 18 once, not per
   machine. *)

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
From kacc Require Import CKAUndec.Glue.TLToRTarget.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityCore.
From kacc Require Import CKAUndec.BinaryAlphabet.
From kacc Require Import CKAUndec.Glue.BinaryAlphabetConnection.
From kacc Require Import CKAUndec.K CKAUndec.KEnumerable.
Require Import SyntheticComputability.Models.EA_L.
Require Import SyntheticComputability.Models.EA_L_Myhill.
From kacc Require Import CKAUndec.KMComplete.
From kacc Require Import CKAUndec.Encoding.

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

(* --- 2. K_bin: one-line instantiation of Computability/TL_Bridge.v's
   generic K_of at Pred := the embedded red_leq' family. K_of itself is
   DEFINITIONALLY faithful to what CKAUndec.K.v's K does for the
   unembedded case (K c = K_of (R_target c)), so K and K_bin are proven
   by the exact same underlying lemmas, not two copies. *)

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

(* --- 3. K_bin_enumerable: one-line instantiation of KA/enumerable.v's
   generic slice_enumerable (T_equiv_dec/T_equiv_enumerable/
   KA_ineq_over/KA_ineq_over_enumerable/slice_enumerable), already
   generic over ANY carrier monoid with countable, Leibniz-equal ≡ --
   the only CKA-specific content is Tm_bin itself and the "K_bin is a
   fixed-rhs slice of ⊑" fact below. *)

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
    (1, (ps 1 * enc 2 (z_vec z), 0))%nat)
  (red_ub' Hlen Hk_pos).
exists f. intros z. rewrite /K_bin /K_of red_leq'_shape. exact: Hf z.
Qed.

(* --- 4. GENERALIZATION of CKAUndec.KMComplete.v: eff_insep_shape_superset
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

(* --- 5. GENERALIZATION of EA_L.v/CKAUndec.KMComplete.v: everything
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

(* --- 6. GENERALIZATION of CKAUndec.KMComplete.v: red_m_transitive is
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
   Sigma^0_1-complete, closing that requirement in full. *)

Definition KA_ineq_bin : ka_term (monoid_car Tm_bin) * ka_term (monoid_car Tm_bin) -> Prop :=
  @KA_ineq_over Tm_bin.

Definition K_to_KA_ineq_bin (c k : nat)
    (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat) (z : nat) :
    ka_term (monoid_car Tm_bin) * ka_term (monoid_car Tm_bin) :=
  (red_lb' (c := c) bEnc (1, (ps 1 * enc 2 (z_vec z), 0))%nat,
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
