(* A direct attempt at EXP_K on literally 2 registers (r = pos0, the
   countdown; v = pos1, the accumulator), mirroring mma_exp_cst's template
   from MM2_Universality_Pilot.v exactly, but WITHOUT a 3rd register for
   the inner multiply's scratch. The point: show concretely, in Rocq, that
   this isn't just "harder" -- the very first precondition you need
   becomes unsatisfiable, not merely inconvenient.

   Conclusion up front: this file does NOT produce EXP_K. It formalizes
   exactly why not, as directly as possible, rather than re-arguing it in
   prose. See the final remark for what this rules out and doesn't. *)

From Stdlib Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import pos vec subcode sss.
From Undecidability.MinskyMachines Require Import mma_defs.
From Undecidability.MinskyMachines.MMA Require Import mma_utils.

Import vec_notations.

Section attempt.

Variable (k i : nat).

(* Exactly mma_exp_cst's template (decrement r, jump to the multiply body,
   jump back), but at pos 2 instead of pos 3 -- so the multiply's own
   scratch argument "z" has nowhere left to point except r or v
   themselves. We try z := r (pos0), the only register other than v
   available at all. *)

Definition mma_exp2_attempt : list (mm_instr (pos 2)) :=
  mm_dec pos0 (3+i) ::
  mma_jump (13+k+i) pos0 ++
  mma_mult_cst_with_zero pos1 pos0 k (3+i) ++
  mma_jump i pos0.

(* Try to prove the exact analogue of mma_exp_cst_progress. Get as far as
   possible; the inductive step's multiply call needs
   `vec_pos v z = 0`, i.e. here `vec_pos (rv0'##vv0##vec_nil) pos0 = 0`,
   i.e. `rv0' = 0` -- but rv0' is universally quantified over all of nat
   by the induction, so this is NOT derivable in general. Recorded as an
   admitted gap on purpose, at exactly the one point that cannot close,
   rather than faked. *)

Lemma mma_exp2_attempt_progress (rv0 vv0 : nat) :
  sss_progress (@mma_sss 2) (i, mma_exp2_attempt)
    (i, rv0 ## vv0 ## vec_nil)
    (13+k+i, 0 ## (vv0 * k^rv0) ## vec_nil).
Proof.
revert vv0.
induction rv0 as [| rv0' IH]; intros vv0; unfold mma_exp2_attempt.
- mma sss DEC zero with pos0 (3+i); rew vec.
  apply sss_progress_compute.
  apply subcode_sss_progress with
    (P := (1+i, mma_jump (13+k+i) pos0)); auto.
  apply mma_jump_progress.
  rewrite Nat.pow_0_r, Nat.mul_1_r; reflexivity.
- mma sss DEC S with pos0 (3+i) rv0'; rew vec.
  apply sss_compute_trans with
    (st2 := (8+k+(3+i), rv0' ## (vv0*k) ## vec_nil)).
  + apply sss_progress_compute.
    apply subcode_sss_progress with
      (P := (3+i, mma_mult_cst_with_zero pos1 pos0 k (3+i))).
    * exists (mm_dec pos0 (3+i) :: mma_jump (13+k+i) pos0), (mma_jump i pos0).
      split; [reflexivity | simpl length; lia].
    * apply (mma_mult_cst_with_zero_progress (n := 2) (x := pos1) (z := pos0)).
      -- discriminate.
      -- (* NEEDS EXACTLY: vec_pos (rv0' ## vv0 ## vec_nil) pos0 = 0,
            i.e. rv0' = 0. Not available: rv0' ranges over all of nat
            here (this is the inductive step, for an ARBITRARY
            predecessor). This is the precise point -- not a
            proof-engineering gap, a genuine one -- where the 2-register
            construction is unsatisfiable, matching
            [[project_ka_eq_phase2_take3_minsky_universality_result_2026-08-06]]'s
            mechanism-level argument exactly: mma_mult_cst_with_zero's own
            precondition demands its scratch register already be 0, and
            here the scratch IS the live loop counter -- which is only 0
            in the base case, never mid-loop, i.e. exactly when this step
            actually needs to fire. *)
         admit.
      -- reflexivity.
  + apply sss_compute_trans with (st2 := (i, rv0' ## (vv0*k) ## vec_nil)).
    * apply sss_progress_compute.
      apply subcode_sss_progress with (P := (8+k+(3+i), mma_jump i pos0)).
      -- exists (mm_dec pos0 (3+i) :: mma_jump (13+k+i) pos0 ++
                  mma_mult_cst_with_zero pos1 pos0 k (3+i)), (@nil (mm_instr (pos 2))).
         split.
         ++ rewrite app_nil_r. reflexivity.
         ++ rewrite length_cons, length_app,
              (mma_mult_cst_with_zero_length pos1 pos0 k (3+i)).
            simpl length. lia.
      -- apply mma_jump_progress; auto.
    * apply sss_progress_compute.
      specialize (IH (vv0*k)).
      rewrite (Nat.pow_succ_r' k rv0'), Nat.mul_assoc.
      exact IH.
Admitted.

End attempt.

(* Remark: this Admitted is not "haven't finished the proof" -- the
   `admit` sits exactly at `vec_pos (rv0'##vv0##vec_nil) pos0 = 0`, which
   is FALSE whenever rv0' > 0, i.e. on every iteration except the last.
   There is no way to discharge it, not a missing lemma. Swapping which
   register plays "z" doesn't help: the ONLY two registers available are
   r (the live countdown, nonzero mid-loop) and v (the live accumulator,
   also generally nonzero) -- there is no register left that is
   guaranteed 0 partway through, which is exactly what
   mma_mult_cst_with_zero (and every other multiply/divide-by-constant
   combinator in this library) requires of its scratch argument. *)
