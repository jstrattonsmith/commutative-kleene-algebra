(* Upgrades Theorem17_KATerm.v's eff_insep_core result to the fully
   bundled eff_insep_shape: K is now genuinely enumerable (K_Enumerable.v
   closes the gap Theorem17_KATerm.v flagged), so this is real,
   axiom-free effective inseparability of K (the actual KA-term/red_leq
   level set) from B1_L, over the SAME numbering W_L throughout --
   Kuznetsov's Proposition 9 applied once more, this time with its
   enumerability hypothesis genuinely discharged rather than dropped.

   A further step was attempted and deliberately NOT included here:
   coq-synthetic-computability's EffectiveInseparability.v proves
   eff_insep_to_m_complete (eff_insep A B -> m-complete A, i.e. genuine
   Sigma^0_1-hardness, matching Kuznetsov's Proposition 7 / Myhill's
   theorem), but its `eff_insep` is tied to THAT file's own ambient `W`
   (built from an arbitrary `EA_inst : EA` instance's canonical
   enumerator), not to a free `W` parameter the way eff_insep_shape is.
   Using it on eff_insep_shape_K_B1_L below would require `W_L ≡ W`
   (every Coq-enumerable set equals W_L i for some i) -- which is
   exactly the Church's-Thesis-for-L style fact that
   project_ka_eq_phase2_blocker's "take 1" got stuck on and this whole
   "take 3" route was built to avoid. So the m-complete upgrade is NOT
   a small follow-on to this file; it would resurrect that earlier
   blocker (on top of costing Markov's Principle too). Flagged rather
   than attempted. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From kacc Require Import TLUniform_Bridge.
From kacc Require Import Theorem17_KATerm.
From kacc Require Import K_Enumerable.

Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityTransport.

Theorem eff_insep_shape_K_B1_L :
  exists c : nat, eff_insep_shape W_L (K c) B1_L.
Proof.
destruct R_TL_R_target_connection as [c Hc].
exists c.
eapply EffectiveInseparabilityTransport.eff_insep_shape_superset.
- exact eff_insep_A0_B1_L_via_generic.
- exact (K_enumerable c).
- exact (@A0_L_subset_K c Hc).
- exact (@K_B1_L_disjoint c Hc).
Qed.
