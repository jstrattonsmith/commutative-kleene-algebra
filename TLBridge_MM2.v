(* Phase 2, take 3 -- per-instance bridge (Task #3). Compiles
   coq-synthetic-computability's Models/PerInstanceGuard.v's per-(c_L,x_L)
   L_computable_closed witness through the SAME axiom-free chain already
   used by EffectiveInseparability_MM2_Race.v's R_race (Synthetic/
   Models_Equivalent.v's L_computable_closed -> MMA_computable ->
   TM_computable -> BSM_computable -> MM_computable -> FRACTRAN_computable
   cycle, composed with kacc's own FRACTRAN_computable_to_MM2_computable.v),
   producing a genuine MM2 program realizing "T_L c_L x_L eventually
   outputs m", for any FIXED, already-known c_L / x_L pair (no MM2-native
   race construction needed -- this is a PLAIN, per-instance reduction,
   not a uniform "works for every runtime input" program). *)

From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

From kacc Require Import FRACTRAN_computable_to_MM2_computable.

Require Import SyntheticComputability.Models.PerInstanceGuard.
Require Import SyntheticComputability.Models.CT.
Require Import Undecidability.L.L.

Lemma R_TL_MM2_computable (c_L x_L : nat) (t_c : term)
  (Ht_c : closed t_c) (Henum : enum_closed c_L = Some t_c) :
  MM2_computable
    (fun _ : Vector.t nat 0 => fun m => exists n, T_L c_L x_L n = Some m).
Proof.
apply mma2_computable_to_mm2_computable.
apply fractran_computable_to_mma2_computable.
apply MM_computable_to_FRACTRAN_computable.
apply BSM_computable_to_MM_computable.
apply TM_computable_to_BSM_computable.
apply MMA_computable_to_TM_computable.
apply L_computable_closed_to_MMA_computable.
exact (@R_TL_L_computable_closed c_L x_L t_c Ht_c Henum).
Qed.
