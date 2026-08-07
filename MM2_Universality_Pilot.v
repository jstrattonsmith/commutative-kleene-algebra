(* A first, deliberately small, concrete instance of "the Minsky
   universality technique" for MM2 (Phase 2, take 3, post-2026-08-06night
   finding): build a genuine 3-register (mma_instr (pos 3)) program that
   computes v := v * k^r from (r, v, 0), where NO register-count trick is
   needed at all (3 registers is enough for a completely ordinary
   "decrement + inner multiply with a scratch" loop) -- then push this
   through coq-library-undecidability's OWN general k-registers-to-2
   compiler (`mma_k_mma_2_compiler`, via `godel_coding_235`, i.e. exactly
   Minsky's theorem, instantiated), and finally through `MMA2_to_MM2` (as
   in SMN_MM2.v) to get a genuine, native MM2 program.

   The point of this file is NOT to solve task #28's raw-y bootstrap --
   last night's research
   ([[project_ka_eq_phase2_take3_minsky_universality_result_2026-08-06]]
   in project memory) established that Minsky's own theorem requires the
   PACKED value as its starting state, not raw y, and this file's final
   theorem states that precondition HONESTLY (its hypothesis is that the
   MM2 register already holds `2^r * 3^v`, not that it holds raw r). The
   point is to actually implement the technique end-to-end, once,
   concretely, as real reusable infrastructure and a real "look what we
   built" artifact -- validating that the pipeline (write an n-register
   program with ordinary reasoning -> compile via the library's own
   Gödel-packing compiler -> convert to native mm2_instr) works cleanly in
   this project's setup, before attempting the much larger 6-or-so-register
   race-interleaving construction that task #28 actually needs. *)

From Stdlib Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import pos vec subcode sss godel_coding.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler_correction.
From Undecidability.MinskyMachines Require Import MM2 mma_defs.
From Undecidability.MinskyMachines.MMA Require Import mma_utils mma_k_mma_2_compiler.

Import vec_notations.

(* --- 0. The 3-register program: v := v * k^r, using z as scratch ------ *)

Section mma_exp_cst.

Variable (k i : nat).

Definition mma_exp_cst : list (mm_instr (pos 3)) :=
  mm_dec pos0 (3+i) ::
  mma_jump (13+k+i) pos0 ++
  mma_mult_cst_with_zero pos1 pos2 k (3+i) ++
  mma_jump i pos0.

Fact mma_exp_cst_length : length mma_exp_cst = 13+k.
Proof.
unfold mma_exp_cst.
rewrite length_cons, !length_app.
rewrite (mma_mult_cst_with_zero_length pos1 pos2 k (3+i)).
simpl length.
lia.
Qed.

Fact pos1_neq_pos2 : (pos1 : pos 3) <> pos2.
Proof. intros H; inversion H. Qed.

Lemma mma_exp_cst_progress (rv0 vv0 : nat) :
  sss_progress (@mma_sss 3) (i, mma_exp_cst)
    (i, rv0 ## vv0 ## 0 ## vec_nil)
    (13+k+i, 0 ## (vv0 * k^rv0) ## 0 ## vec_nil).
Proof.
revert vv0.
induction rv0 as [| rv0' IH]; intros vv0; unfold mma_exp_cst.
- mma sss DEC zero with pos0 (3+i); rew vec.
  apply sss_progress_compute.
  apply subcode_sss_progress with
    (P := (1+i, mma_jump (13+k+i) pos0)); auto.
  apply mma_jump_progress.
  rewrite Nat.pow_0_r, Nat.mul_1_r; reflexivity.
- mma sss DEC S with pos0 (3+i) rv0'; rew vec.
  apply sss_compute_trans with
    (st2 := (11+k+i, rv0' ## (vv0*k) ## 0 ## vec_nil)).
  + apply sss_progress_compute.
    apply subcode_sss_progress with
      (P := (3+i, mma_mult_cst_with_zero pos1 pos2 k (3+i))).
    * exists (mm_dec pos0 (3+i) :: mma_jump (13+k+i) pos0), (mma_jump i pos0).
      split; [reflexivity | simpl length; lia].
    * apply (mma_mult_cst_with_zero_progress pos1_neq_pos2).
      -- rew vec.
      -- f_equal; [lia | apply vec_pos_ext; intros p; analyse pos p; simpl; nia].
  + apply sss_compute_trans with
      (st2 := (i, rv0' ## (vv0*k) ## 0 ## vec_nil)).
    * apply sss_progress_compute.
      apply subcode_sss_progress with (P := (11+k+i, mma_jump i pos0)).
      -- exists (mm_dec pos0 (3+i) :: mma_jump (13+k+i) pos0 ++
                  mma_mult_cst_with_zero pos1 pos2 k (3+i)), (@nil (mm_instr (pos 3))).
         split.
         ++ rewrite app_nil_r. reflexivity.
         ++ rewrite length_cons, length_app,
              (mma_mult_cst_with_zero_length pos1 pos2 k (3+i)).
            simpl length. lia.
      -- apply mma_jump_progress; auto.
    * apply sss_progress_compute.
      specialize (IH (vv0*k)).
      rewrite (Nat.pow_succ_r' k rv0'), Nat.mul_assoc.
      exact IH.
Qed.

End mma_exp_cst.

(* --- 1. Compile to 2 registers, via the library's own general
   Gödel-packing compiler (`mma_k_mma_2_compiler`), instantiated at k=3
   with `godel_coding_235` -- this IS Minsky's own theorem, applied. ---- *)

Section mma_exp_cst_mma2.

Variable (k i : nat).

(* mma_k_mma_2_compiler's own "n" (the number of pass-through registers
   beyond the k being packed) is 0 here: we're packing ALL 3 registers. *)

Definition exp_cst_compiler := mma_k_mma_2_compiler godel_coding_235 0.

(* The resulting 2-register program, and its correctness, both come
   directly from the generic `compiler_t` record -- no new proof needed
   at this level, only instantiation. *)

Definition mma_exp_cst_2reg : list (mm_instr (pos 2)) :=
  gc_code exp_cst_compiler (i, mma_exp_cst k i) i.

Theorem mma_exp_cst_2reg_correct (rv0 vv0 : nat) :
  sss_output (@mma_sss 2) (i, mma_exp_cst_2reg)
    (i, 0 ## gc_enc godel_coding_235 (rv0 ## vv0 ## 0 ## vec_nil) ## vec_nil)
    (code_end (i, mma_exp_cst_2reg),
     0 ## gc_enc godel_coding_235 (0 ## (vv0*k^rv0) ## 0 ## vec_nil) ## vec_nil).
Proof.
unfold mma_exp_cst_2reg.
assert (Hout_code : out_code (13+k+i) (i, mma_exp_cst k i)).
{ red; unfold code_end; simpl fst; simpl snd; rewrite mma_exp_cst_length; lia. }
assert (Houtput : sss_output (@mma_sss 3) (i, mma_exp_cst k i)
                    (i, rv0 ## vv0 ## 0 ## vec_nil)
                    (13+k+i, 0 ## (vv0*k^rv0) ## 0 ## vec_nil)).
{ split; [apply sss_progress_compute, mma_exp_cst_progress | exact Hout_code]. }
edestruct (compiler_t_output_sound' exp_cst_compiler
             (P := (i, mma_exp_cst k i)) i
             (v := rv0 ## vv0 ## 0 ## vec_nil)
             (0 ## gc_enc godel_coding_235 (rv0 ## vv0 ## 0 ## vec_nil) ## vec_nil))
  as [w' [Hout Hsim]].
- simpl; split; reflexivity.
- exact Houtput.
- change (vec nat (2+0)) with (vec nat 2) in *.
  change (mma_sss (n:=2+0)) with (mma_sss (n:=2)) in *.
  simpl in Hsim. destruct Hsim as [Hw1 _].
  assert (Heta : w' = w'#>pos0 ## w'#>pos1 ## vec_nil).
  { rewrite (vec_head_tail w') at 1.
    rewrite (vec_head_tail (vec_tail w')).
    rewrite vec_pos0, vec_pos1.
    f_equal; f_equal.
    generalize (vec_tail (vec_tail w')); intros v0.
    apply vec_pos_ext; intros p; destruct (pos_O_inv p). }
  rewrite Heta, Hw1 in Hout. exact Hout.
Qed.

End mma_exp_cst_mma2.

(* --- 2. Convert to native mm2_instr, exact-value-preserving, exactly as
   SMN_MM2.v already does for its own MMA2-level prefix. ---------------- *)

From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.
From Stdlib Require Import Relations.Relation_Operators.
Import MM2Notations.

Definition mm2_exp_cst (k i : nat) : list mm2_instr :=
  List.map mma_mm2_instr (mma_exp_cst_2reg k i).

(* Final theorem, stated honestly: the MM2 program below computes
   v = v0 * k^r GIVEN the register already holds the Gödel-packed value
   2^r * 3^v0 -- exactly Minsky's own theorem's precondition, not raw r. *)

(* Stated via the abstract godel_coding_235 packing interface directly,
   rather than expanding it to its concrete 2^_*3^_ formula: the compiler
   theorem `godel_coding_235` is opaque (proved via Qed, matching the
   library's own convention of only exposing the abstract `gc_enc`/
   `gc_pr`/`gc_succ` interface, never a concrete formula to compute
   with) -- so this is the honest, library-idiomatic way to state the
   precondition, not a simplification we're choosing for convenience. *)

Theorem mm2_exp_cst_correct (k rv0 vv0 : nat) :
  clos_refl_trans (nat * (nat * nat)) (mm2_step (mm2_exp_cst k 1))
    (1, (0, gc_enc godel_coding_235 (rv0 ## vv0 ## 0 ## vec_nil)))
    (1 + length (mm2_exp_cst k 1),
     (0, gc_enc godel_coding_235 (0 ## (vv0*k^rv0) ## 0 ## vec_nil))).
Proof.
generalize (MMA2_to_MM2.mma_mm2_compute_equiv (mma_exp_cst_2reg k 1)
              (1, 0 ## gc_enc godel_coding_235 (rv0##vv0##0##vec_nil) ## vec_nil)
              (code_end (1, mma_exp_cst_2reg k 1),
               0 ## gc_enc godel_coding_235 (0 ## (vv0*k^rv0) ## 0 ## vec_nil) ## vec_nil)).
intros [Hfwd _].
unfold mm2_exp_cst.
specialize (Hfwd (proj1 (mma_exp_cst_2reg_correct k 1 rv0 vv0))).
unfold code_end in Hfwd.
simpl in Hfwd.
rewrite length_map.
exact Hfwd.
Qed.
