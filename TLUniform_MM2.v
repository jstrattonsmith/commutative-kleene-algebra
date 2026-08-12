(* Compiles coq-synthetic-computability's Models/T_L_Uniform.v's
   L_computable_closed_R_TL (a SINGLE L term taking (c,x) as RUNTIME
   bound variables, realizing "T_L c x eventually outputs m" for ANY
   c,x -- not a per-instance construction) through the same axiom-free
   chain used by EffectiveInseparability_MM2_Race.v's R_race, producing
   ONE genuine, fully-packaged MM2_computable witness for the whole T_L
   family (no choice/Sigma-unraveling needed, since there is exactly one
   program, not one per (c,x) pair).

   Kept despite being unused by the main Theorem17-19 argument: this is
   the direct, intended predecessor to CKA.Glue.TLToRTarget.v's own pinned
   re-derivation of the same fact. The reason it went unused is itself
   informative -- R_TL_MM2_computable's MM2_computable/MMA2_computable
   conclusion is an opaque existential (Qed-opaque about exactly where
   the compiled program stops), and CKA.Glue.TLToRTarget.v's splice
   construction needs that stop position exposed, not just known to
   exist, to know where to append its divides-test code. Rather than
   strengthen this proof to expose it, CKA.Glue.TLToRTarget.v re-derives the
   fact directly with the stop position pinned from the start. Kept
   around as a candidate for a simpler fix and as a possible paper
   narrative beat about this specific opacity trap. *)

From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

From kacc Require Import MM2.FractranCompiler.

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
