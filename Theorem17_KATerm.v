(* Closes the project's Theorem 17 analogue: the KA-term-level set K
   (an actual red_lb/red_ub inequality, i.e. a bona fide statement about
   validity of a KA-term ordering, via mm.v's R_target) is effectively
   inseparable from B1_L.

   Key structural point (traced through both source papers): NO
   numbering change is needed, and the transport lemma this file builds
   (eff_insep_core_superset, a Proposition-9-style superset transport)
   does not need any new "reduction transports eff_insep to a different
   W" machinery layered on top. Kuznetsov's own argument (ICTAC 2023,
   Section 4, Propositions 7-9) settles this directly: K, B1_L, A0_L are
   ALL subsets of the SAME domain (nat, indexed by z), and Proposition 9
   is simply reapplied with A0_L as the known subset and K as the new
   superset. Azevedo de Amorim et al.'s own Theorem 17 (CSL 2025) is
   itself stated exactly this way -- disjointness plus a witness
   function, with NO enumerability of the sets baked in.

   The one genuine obstacle: the *library's* eff_insep_shape bundles
   `enumerable A` into its own definition (for Proposition 7's
   convenience, not because Definition 5/Theorem 17 require it), and K
   (defined via R_target, a semantic KA-term inequality) is not known to
   be enumerable in this codebase -- that would need a *separate*
   argument (K's r.e.-ness would come from a finitary axiomatisation /
   proof-search argument, matching Kuznetsov's remark that "the upper
   Sigma^0_1 bound follows from a finitary axiomatisation", which is not
   yet formalised here). Rather than force that extra, unrelated
   development, this file works with the *unbundled* notion
   (eff_insep_core below, matching both papers' own Definition 5 / "there
   exists a partial computable f..." verbatim) and transports along
   that instead. This delivers exactly the paper's Theorem 17 statement
   for the KA-term-level set K; K's enumerability (needed to strengthen
   this to the fully bundled eff_insep_shape) is picked up in
   K_Enumerable.v/Theorem17_Full.v.

   File structure: sections 0-1 (eff_insep_core, eff_insep_core_superset)
   are fully generic -- parametrized over an arbitrary numbering W and
   sets A/B/A', reusable for any effective-inseparability argument that
   wants the unbundled (no-enumerability-required) notion. Sections 2-3
   are the CKA-specific instantiation: K itself, and its effective
   inseparability from B1_L. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Shared.Libs.DLW Require Import vec.
Import vec_notations.
From kacc Require Import TLUniform_Bridge.
From kacc Require Import EffectiveInseparability_MM2.
From kacc Require Import A0_L_Prime.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.

(* --- 0. The unbundled notion of effective inseparability (Kuznetsov's
   Definition 5 / Azevedo de Amorim et al.'s Theorem 17 statement,
   verbatim): disjointness plus a witness function, no enumerability. *)

Definition eff_insep_core (W : nat -> nat -> Prop) (A B : nat -> Prop) : Prop :=
  (forall x, A x -> ~ B x) /\
  exists f : nat -> nat -> part nat,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k, hasvalue (f i j) k /\ ~ W i k /\ ~ W j k.

Lemma eff_insep_shape_to_core (W : nat -> nat -> Prop) (A B : nat -> Prop) :
  eff_insep_shape W A B -> eff_insep_core W A B.
Proof.
intros [_ [_ [Hdisj [f Hf]]]]. split; [exact Hdisj |]. exists f. exact Hf.
Qed.

(* --- 1. Proposition 9 / eff_insep_shape_superset, unbundled: no
   enumerability hypothesis on the new superset A'. Same proof shape as
   EffectiveInseparabilityTransport.v's eff_insep_shape_superset, just
   without the enumerable A' plumbing. GENERIC. *)

Lemma eff_insep_core_superset (W : nat -> nat -> Prop) (A B A' : nat -> Prop) :
  eff_insep_core W A B ->
  (forall x, A x -> A' x) ->
  (forall x, A' x -> ~ B x) ->
  eff_insep_core W A' B.
Proof.
intros [Hdisj [f Hf]] Hsub Hdisj'.
split; [exact Hdisj' |].
exists f. intros i j Hi Hj Hij.
apply Hf.
- intros x Hx. apply Hi, Hsub, Hx.
- exact Hj.
- exact Hij.
Qed.

(* --- 2. K: the actual KA-term-level set, via R_target/red_leq -- a
   genuine red_lb ⊑ red_ub statement (mm.v), not a detour through
   Theta_ours_MM2. Fixed once via R_TL_R_target_connection's witness c. *)

(* A0_L_Prime.v's own z_vec is `Let`-scoped inside its Section Splice3
   and does not survive past it; redefine identically here. *)
Definition z_vec (z : nat) : Vector.t nat 2 :=
  fst (unembed z) ## snd (unembed z) ## vec_nil.

Section Splice6.

Variable (c : nat).
Hypothesis Hc : forall (v : Vector.t nat 2) (m : nat),
  m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R_target c (ps 1 * enc 2 v)).

Definition K (z : nat) : Prop := R_target c (ps 1 * enc 2 (z_vec z)).

Lemma A0_L_subset_K (z : nat) : A0_L z -> K z.
Proof.
intros HA. apply theta_ours_L_iff in HA.
assert (HR1 : T_L_Uniform.R_TL (z_vec z) 1) by (apply R_TL_iff; exact HA).
exact (proj1 (@Hc (z_vec z) 1 (Nat.le_refl 1) HR1) eq_refl).
Qed.

Lemma K_B1_L_disjoint (z : nat) : K z -> ~ B1_L z.
Proof.
intros HK HB. apply theta_ours_L_iff in HB.
assert (HR0 : T_L_Uniform.R_TL (z_vec z) 0) by (apply R_TL_iff; exact HB).
assert (Heq : 0 = 1)
  by (apply (@Hc (z_vec z) 0 (Nat.le_0_l 1) HR0); exact HK).
discriminate Heq.
Qed.

End Splice6.

(* --- 3. The deliverable: K (the KA-term-level set) is effectively
   inseparable (unbundled sense) from B1_L. This is the project's
   Theorem 17 analogue at the actual KA-term/red_leq level. *)

Theorem eff_insep_K_B1_L :
  exists c : nat, eff_insep_core W_L (K c) B1_L.
Proof.
destruct R_TL_R_target_connection as [c Hc].
exists c.
apply (eff_insep_core_superset (A := A0_L)).
- exact (eff_insep_shape_to_core eff_insep_A0_B1_L_via_generic).
- exact (@A0_L_subset_K c Hc).
- exact (@K_B1_L_disjoint c Hc).
Qed.
