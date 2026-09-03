(* Compiles coq-synthetic-computability's Models/T_L_Uniform.v's
   L_computable_closed_R_TL (a single L term taking (c,x) as runtime
   bound variables, realizing "T_L c x eventually outputs m" for any
   c,x) through the same axiom-free chain used by
   EffectiveInseparability_MM2_Race.v's R_race, producing one genuine
   MM2_computable witness for the whole T_L family.

   Not used by the main argument: this witness's MM2_computable/
   MMA2_computable conclusion is Qed-opaque about exactly where the
   compiled program stops, and CKAUndec/Glue/TLToRTarget.v's splice
   construction needs that stop position exposed, not just known to
   exist. CKAUndec/Glue/TLToRTarget.v re-derives the fact directly with
   the stop position pinned from the start instead of strengthening this
   proof to expose it. *)

From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

From Undecidability.MinskyMachines.Reductions Require Import FRACTRAN_computable_to_MM2_computable.

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
