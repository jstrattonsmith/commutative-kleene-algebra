(* Closes the project's Theorem 17 analogue: the KA-term-level set K
   (an actual red_lb/red_ub inequality, i.e. a bona fide statement about
   validity of a KA-term ordering, via Encoding.v's R_target) is effectively
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
   CKAUndec.KEnumerable.v/CKAUndec.KMComplete.v.

   The generic unbundled machinery (eff_insep_core,
   eff_insep_shape_to_core, eff_insep_core_superset) has been extracted
   to Computability/InseparabilityCore.v, and the "connection ->
   eff_insep_core" argument itself (z_vec, K_of,
   A0_L_subset_K_of/K_of_B1_L_disjoint/eff_insep_K_of_B1_L, generic over
   an arbitrary Pred) has been further extracted to
   Computability/TL_Bridge.v -- this file is now just the CKA-specific
   instantiation at Pred := R_target c: K itself, and its effective
   inseparability from B1_L. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Shared.Libs.DLW Require Import vec.
Import vec_notations.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import CKAUndec.Glue.MM2ToKATerm.
Require Import SyntheticComputability.Models.T_L_Bridge.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityCore.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.

(* --- 2. K: the actual KA-term-level set, via R_target/red_leq -- a
   genuine red_lb ⊑ red_ub statement (Encoding.v), not a detour through
   Theta_ours_MM2. Fixed once via R_TL_R_target_connection's witness c.
   One-line instantiation of Computability/TL_Bridge.v's generic K_of at
   Pred := R_target c. *)

Section Splice6.

Variable (c : nat).
Hypothesis Hc : forall (v : Vector.t nat 2) (m : nat),
  m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R_target c (ps 1 * enc 2 v)).

Definition K (z : nat) : Prop := K_of (R_target c) z.

Lemma A0_L_subset_K (z : nat) : A0_L z -> K z.
Proof. intros HA. exact (A0_L_subset_K_of Hc HA). Qed.

Lemma K_B1_L_disjoint (z : nat) : K z -> ~ B1_L z.
Proof. intros HK. exact (K_of_B1_L_disjoint Hc HK). Qed.

End Splice6.

(* --- 3. The deliverable: K (the KA-term-level set) is effectively
   inseparable (unbundled sense) from B1_L. This is the project's
   Theorem 17 analogue at the actual KA-term/red_leq level.
   One-line instantiation of Computability/TL_Bridge.v's generic
   eff_insep_K_of_B1_L. *)

Theorem eff_insep_K_B1_L :
  exists c : nat, eff_insep_core W_L (K c) B1_L.
Proof.
destruct R_TL_R_target_connection as [c Hc].
exists c. exact (eff_insep_K_of_B1_L Hc).
Qed.
