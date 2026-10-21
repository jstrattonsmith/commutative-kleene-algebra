(* The binary-alphabet analogue of CKAUndec/Glue/TLToRTarget.v's
   R_TL_R_target_connection: instantiates TLToRTarget.v's
   R_TL_connection_gen at red_leq', with CKAUndec/BinaryAlphabet.v's
   mm2_R_completeness'/mm2_R_soundness' (halting-case only, exactly
   mirroring Encoding.mm2_R_completeness/mm2_R_soundness's own
   restriction) in place of the unembedded originals. The binary
   encoding is chosen after the machine c, which is why this uses
   R_TL_connection_gen (c independent of the predicate) rather than
   R_TL_connection_of. Feeds CKAUndec/BinaryAlphabetMComplete.v's
   superset-transport argument.

   Naming note: the binary-alphabet character encoding is named `bEnc`
   throughout (not `enc`) -- a genuine collision with prime_seq.enc,
   which this file also uses pervasively (`ps 1 * enc 2 v`, from the
   Psplice construction), not a style choice. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability.MinskyMachines Require Import MM2 MMA.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From kacc Require Import KA.algebra KA.pre_ka KA.preka_enumerable.
From kacc Require Import CKAUndec.Glue.TLToRTarget.
From kacc Require Import CKAUndec.BinaryAlphabet.

(* algebra.v/pre_ka.v open ka_scope, whose `0`/`1` typeclass-resolved
   literals otherwise hijack every plain nat literal below (vec_nil
   cons cells, MM2 states, etc.) -- re-opening nat_scope last makes it
   win ties for bare numerals, avoiding a %nat annotation on every
   single occurrence. *)
Open Scope nat_scope.

Theorem R_TL_R_target_connection_bin :
  exists (c k : nat) (bEnc : setoid_car (@Encoding.mm_sym_setoid _) → list bool)
    (Hlen : ∀ x, length (bEnc x) = k) (Hk_pos : (0 < k)%nat),
  forall (v : Vector.t nat 2) (m : nat),
    (m <= 1)%nat -> T_L_Uniform.R_TL v m ->
    (m = 1 <-> red_leq' (c := c) Hlen Hk_pos (1, (ps 1 * enc 2 v, 0))%nat).
Proof.
destruct R_TL_connection_gen as [c Hc].
destruct (binary_encoding_exists c) as [k [bEnc [HbEnc [Hlen Hk_pos]]]].
exists c, k, bEnc, Hlen, Hk_pos.
apply Hc; [exact (mm2_R_completeness' HbEnc Hlen Hk_pos) |
           exact (@mm2_R_soundness' c k bEnc HbEnc Hlen Hk_pos)].
Qed.
