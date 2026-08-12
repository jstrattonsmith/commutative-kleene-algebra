(* Closes task #40 (Arthur's comment 2, fully): mirrors
   TLUniform_Bridge.v / Theorem17_KATerm.v / K_Enumerable.v /
   Theorem19_MComplete.v / Theorem19_Full.v's SUPERSET-transport
   strategy at the embedded (binary-alphabet) level, substituting
   Theorem18_BinaryAlphabet.v's mm2_R_completeness'/mm2_R_soundness'
   (halting-case only, exactly mirroring mm.mm2_R_completeness/
   mm2_R_soundness's own restriction) for the unembedded originals.

   Per the Azevedo de Amorim et al. paper's own Theorem 18/19 proof
   (checked directly): their reduction never characterizes a
   divergent run either -- A/B (Theorem 17) are BOTH defined only over
   HALTING computations, and their A' superset (Theorem 19's proof)
   only ever needs "A subset A'" (halting-and-accepting) and
   "A' disjoint from B" (halting-and-rejecting), never anything about
   inputs outside A u B. This is the SAME strategy this project's own
   A0_L_Prime.v/Theorem17_KATerm.v already use for the unembedded K.
   So this file needs NO new completeness argument beyond what's
   already proven -- it strictly mirrors the existing chain, plugging
   in the embedded halting-case lemmas in place of the unembedded
   ones. The genuinely-unprovable divergent-run gap documented in
   Theorem18_BinaryAlphabet.v is real but not on this critical path.

   Naming note: the binary-alphabet character encoding is named `bEnc`
   throughout (NOT `enc`) to avoid shadowing prime_seq.enc, which this
   file also uses pervasively (`ps 1 * enc 2 v`, from the Psplice
   construction) -- a real name collision caught while drafting this
   file, not a style choice. *)

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

From kacc Require Import algebra pre_ka enumerable.
From kacc Require Import TLUniform_MM2 TLUniform_Bridge A0_L_Prime.
From kacc Require Import EffectiveInseparability_MM2.
From kacc Require Import Theorem18_BinaryAlphabet.
From kacc Require Import Theorem17_KATerm K_Enumerable.
From kacc Require Import Theorem17_Full EA_L Theorem19_MComplete Theorem19_Full.
Require kacc.mm.

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

(* --- 1. Mirror TLUniform_Bridge.v's Psplice_R_target_divides/
   _not_divides/R_TL_R_target_connection, substituting
   mm2_R_completeness'/mm2_R_soundness' for the unembedded originals.
   Reuses A0_L_Prime.v's Psplice_mm2_divides/Psplice_mm2_not_divides
   UNCHANGED -- those are pure MM2-level (rtc) facts, no KA terms
   involved, so nothing about the embedding touches them. *)

Section SpliceBin.

Variable (Q : list (nat * nat)).
Notation QF := (Fin.t (S (S (length (progOf (c_P Q)))))).
Variable (k : nat).
Variable (bEnc : setoid_car (@mm.mm_sym_setoid QF) → list bool).
Variable (HbEnc : ∀ x y, bEnc x = bEnc y → x = y).
Variable (Hlen : ∀ x, length (bEnc x) = k).
Variable (Hk_pos : (0 < k)%nat).

Lemma Psplice_red_leq_bin_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
    (i0 Q, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  red_leq' (c := c_P Q) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat.
Proof.
intros Hc Hd.
apply (mm2_R_completeness' HbEnc Hlen Hk_pos).
apply crt_to_rtc.
apply (@Psplice_mm2_divides Q v b Hc Hd).
Qed.

Lemma Psplice_red_leq_bin_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
    (i0 Q, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ red_leq' (c := c_P Q) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat.
Proof.
intros Hc Hnd Hred.
assert (Hbad : ~ (progOf (c_P Q)) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)))
  by (apply Psplice_mm2_not_divides with (b := b); [exact Hc | exact Hnd]).
assert (Hout : sss_output (@mma_sss 2) (1, Psplice Q)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target Q, 0 ## b ## vec_nil))
  by (apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]).
assert (Hterm : sss_terminates (@mma_sss 2) (1, Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  by (exists (q_target Q, 0 ## b ## vec_nil); exact Hout).
apply (mma_mma2_reduction (Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)) in Hterm.
destruct Hterm as [s2 [Hreach Hstop]].
assert (Hs2 : s2 <> (0, (0, 0))).
{ intros ->. apply Hbad. rewrite progOf_c_P. exact Hreach. }
rewrite <- progOf_c_P in Hreach, Hstop.
apply crt_to_rtc in Hreach.
assert (Hred' : red_leq' (c := c_P Q) Hlen Hk_pos
    (mma_mm2_state (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))).
{ rewrite mma_mm2_state_22. exact Hred. }
assert (Hsound : s2 = (0, (0, 0))).
{ eapply (mm2_R_soundness' HbEnc); [exact Hreach | exact Hstop | exact Hred']. }
exact (Hs2 Hsound).
Qed.

End SpliceBin.

Theorem R_TL_R_target_connection_bin :
  exists (c k : nat) (bEnc : setoid_car (@mm.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  forall (v : Vector.t nat 2) (m : nat),
    (m <= 1)%nat -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> red_leq' (c := c) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat).
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
destruct (binary_encoding_exists (c_P Q)) as [k [bEnc [HbEnc [Hlen Hk_pos]]]].
exists (c_P Q), k, bEnc, Hlen, Hk_pos.
intros v m Hm1 HR.
apply HQ in HR.
destruct HR as [b [Hcompute [Hdiv1 Hdiv2]]].
split.
- intros ->.
  assert (Hdb : divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
  exact (Psplice_red_leq_bin_divides HbEnc Hlen Hk_pos Hcompute Hdb).
- intros HRt.
  destruct (Nat.eq_dec m 0) as [-> | Hne]; [| lia].
  exfalso.
  assert (Hndb : ~ divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
  exact (Psplice_red_leq_bin_not_divides HbEnc Hcompute Hndb HRt).
Qed.

(* --- 2. GENERALIZATION of Theorem17_KATerm.v's Section Splice6: the
   "connection -> eff_insep_core" argument (A0_L_subset_K/
   K_B1_L_disjoint/eff_insep_K_B1_L there) never actually touches
   R_target/red_leq's own definition -- it only uses the abstract
   Hc-style characterization (m=1 <-> Pred y) as a black box. Pulling
   that out as a lemma over an ARBITRARY Pred : nat -> Prop makes both
   the original (unembedded) K and this file's K_bin ONE-LINE
   instantiations of the SAME proof, instead of two copies of it.
   eff_insep_core_superset (Theorem17_KATerm.v) is itself already
   fully generic and reused unchanged underneath. *)

Section GenericK.

Variable (Pred : nat -> Prop).
Hypothesis Hc : forall (v : Vector.t nat 2) (m : nat),
  (m <= 1)%nat -> T_L_Uniform.R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)).

Definition K_of (z : nat) : Prop :=
  Pred (ps 1 * enc 2 (Theorem17_KATerm.z_vec z)).

Lemma A0_L_subset_K_of (z : nat) : A0_L z -> K_of z.
Proof.
intros HA. apply theta_ours_L_iff in HA.
assert (HR1 : T_L_Uniform.R_TL (Theorem17_KATerm.z_vec z) 1)
  by (apply R_TL_iff; exact HA).
exact (proj1 (@Hc (Theorem17_KATerm.z_vec z) 1 (Nat.le_refl 1) HR1) eq_refl).
Qed.

Lemma K_of_B1_L_disjoint (z : nat) : K_of z -> ~ B1_L z.
Proof.
intros HK HB. apply theta_ours_L_iff in HB.
assert (HR0 : T_L_Uniform.R_TL (Theorem17_KATerm.z_vec z) 0)
  by (apply R_TL_iff; exact HB).
assert (Heq : 0 = 1)
  by (apply (@Hc (Theorem17_KATerm.z_vec z) 0 (Nat.le_0_l 1) HR0); exact HK).
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
   Theorem17_KATerm.v already proves for the unembedded K, not a
   different/weaker claim -- K c is DEFINITIONALLY K_of (R_target c). *)
Lemma K_eq_K_of_R_target (c : nat) : Theorem17_KATerm.K c = K_of (R_target c).
Proof. reflexivity. Qed.

Definition K_bin (c k : nat) (bEnc : setoid_car (@mm.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat) : nat -> Prop :=
  K_of (fun y => red_leq' (c := c) Hlen Hk_pos (1, (y, 0))%nat).

Theorem eff_insep_K_bin_B1_L :
  exists (c k : nat) (bEnc : setoid_car (@mm.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  eff_insep_core W_L (K_bin (c := c) Hlen Hk_pos) B1_L.
Proof.
destruct R_TL_R_target_connection_bin as [c [k [bEnc [Hlen [Hk_pos Hc]]]]].
exists c, k, bEnc, Hlen, Hk_pos.
exact (eff_insep_K_of_B1_L Hc).
Qed.



