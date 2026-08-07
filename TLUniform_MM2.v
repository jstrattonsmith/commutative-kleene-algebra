(* Phase 2, take 3 -- uniform T_L bridge. Compiles
   coq-synthetic-computability's Models/T_L_Uniform.v's L_computable_closed_R_TL
   (a SINGLE L term taking (c,x) as RUNTIME bound variables, realizing
   "T_L c x eventually outputs m" for ANY c,x -- not a per-instance
   construction) through the SAME axiom-free chain used by
   EffectiveInseparability_MM2_Race.v's R_race, producing ONE genuine MM2
   program realizing the whole T_L family. This supersedes
   TLBridge_MM2.v's per-instance version for the purposes of building the
   η reduction (Tasks #5-6): no choice/Sigma-unraveling is needed here,
   since there is exactly one program, not one per (c,x) pair. *)

From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

From kacc Require Import FRACTRAN_computable_to_MM2_computable.

Require Import SyntheticComputability.Models.T_L_Uniform.

Lemma R_TL_MM2_computable : MM2_computable R_TL.
Proof.
apply mma2_computable_to_mm2_computable.
apply fractran_computable_to_mma2_computable.
apply MM_computable_to_FRACTRAN_computable.
apply BSM_computable_to_MM_computable.
apply TM_computable_to_BSM_computable.
apply MMA_computable_to_TM_computable.
apply L_computable_closed_to_MMA_computable.
exact L_computable_closed_R_TL.
Qed.
