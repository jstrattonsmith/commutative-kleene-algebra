(* Bridges T_L (Rocq's own L-interpreter, compiled via the library's
   FRACTRAN->MMA2 chain) to EffectiveInseparability_MM2.v's own
   Theta_ours_MM2/A0_MM2/R_target convention (halt EXACTLY at (0,(0,0))).

   The two conventions genuinely don't align on their own:
   MMA2_computable-style programs halt by "running off the end" (landing
   at some position i with out_code i P, concretely length P + 1 for this
   specific FRACTRAN->MMA2 compiler step -- confirmed directly from
   fractran_mma_sound's own statement), while mm.v's whole undecidability
   argument (mm2_R_soundness/completeness, hence R_target/red_leq) is
   specifically about reaching (0,(0,0)) -- that's baked into how the
   MM2-halting-problem gets encoded into KA-term inequalities, not a
   choice EffectiveInseparability_MM2.v made. So a splice is needed: run
   the compiled program, then test whether the output register is
   divisible by qs 1 (the only test we ever need, since our relation
   only outputs m in {0,1}), and redirect to (0,(0,0)) iff so.

   File structure (generic machinery first, CKA/T_L-specific glue after):

   - GENERIC: FRACTRAN_computable_to_MMA2_pinned re-derives the library's
     own fractran_computable_to_mma2_computable with a PINNED stop
     position (length (fractran_mma Q) + 1 exactly, instead of an
     abstract existential i) -- needed so the splice below can reliably
     append code right after the compiled program. The existing
     MMA2_computable/MM2_computable theorems don't expose this pinned
     fact even though their own proofs establish it internally
     (Qed-opacity, see TLUniform_MM2.v's header for the fuller story of
     why this file doesn't just reuse that packaged form); this
     re-derives it directly from the same underlying lemmas
     (fractran_mma_sound, eval_iff, sss_output_fun) the library's own
     proof already uses. Parametric in any FRACTRAN-computable R, not
     tied to T_L or KACC at all.

   - CKA/T_L-SPECIFIC: R_TL_FRACTRAN_computable (compiling T_L itself),
     Section Splice (building the actual divides-test-and-redirect
     program, Psplice, and connecting it to mm.v's R_target), and the
     closing R_TL_R_target_connection. *)

From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia Relations.
From Undecidability Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import MM MM2 MMA Util.MM2_facts.
Import MM2Notations.

From Undecidability.Shared.Libs.DLW Require Import gcd pos vec.
Import vec_notations.
Import Vector.VectorNotations.

From Undecidability.MinskyMachines Require Import mm_defs mma_defs fractran_mma mma_utils.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.

From kacc Require Import MM2.FractranCompiler MM2.Simulator.
From kacc Require Import EffectiveInseparability_MM2.
Require kacc.mm.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

Lemma FRACTRAN_computable_to_MMA2_pinned {k} (R : Vector.t nat k -> nat -> Prop) :
  FRACTRAN_computable R ->
  exists (Q : list (nat * nat)),
    forall (v : Vector.t nat k) (m : nat),
      R v m <->
      exists b,
        sss_compute (@mma_sss 2) (1, fractran_mma Q)
          (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
          (length (fractran_mma Q) + 1, b ## 0 ## vec_nil) /\
        divides (qs 1 ^ m) b /\
        ~ divides (qs 1 ^ (S m)) b.
Proof.
move=> [Q [Qreg rest]].
exists Q.
move=> v m; rewrite {}rest; split.
- move=> [j [/eval_iff H Hdiv]].
  move: H => [Hcompute Hstop].
  exists (j * qs 1 ^ m).
  split; first exact: (fractran_mma_sound Qreg Hcompute Hstop).
  split; first (rewrite Nat.mul_comm; apply divides_left).
  rewrite Nat.mul_comm.
  have qs_not_0 : qs 1 ≠ 0 by rewrite /= nthprime_3.
  apply (not_div _ _ qs_not_0 Hdiv).
- move=> [b [Hcompute [Hdiv1 Hdiv2]]].
  have Hout : sss_output (@mma_sss 2) (1, fractran_mma Q)
                (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
                (length (fractran_mma Q) + 1, b ## 0 ## vec_nil).
  { split; first exact Hcompute. rewrite /out_code /=; lia. }
  have Hterm : sss_terminates (@mma_sss 2) (1, fractran_mma Q)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil).
  { exists (length (fractran_mma Q) + 1, b ## 0 ## vec_nil). exact Hout. }
  apply fractran_mma_reduction in Hterm; last exact Qreg.
  destruct Hterm as [j [Hcompute' Hstop']].
  have Hbeqj : b = j.
  { have Hreach : sss_compute (@mma_sss 2) (1, fractran_mma Q)
                    (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
                    (length (fractran_mma Q) + 1, j ## 0 ## vec_nil)
      by exact: (fractran_mma_sound Qreg Hcompute' Hstop').
    have Hout2 : sss_output (@mma_sss 2) (1, fractran_mma Q)
                   (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
                   (length (fractran_mma Q) + 1, j ## 0 ## vec_nil).
    { split; first exact Hreach. rewrite /out_code /=; lia. }
    have Hdet : forall (instr : mm_instr (pos 2)) s t1 t2,
        mma_sss instr s t1 -> mma_sss instr s t2 -> t1 = t2 by eapply mma_sss_fun; eauto.
    have Heq := sss_output_fun _ Hout Hout2.
    have {}Heq := Heq Hdet.
    by case: Heq.
  }
  subst b.
  case: Hdiv1 => j0 Hj0.
  exists j0.
  split; first by rewrite -{}Hj0; apply eval_iff; split.
  move=> [d Hd].
  apply Hdiv2.
  exists d.
  rewrite Hj0 Hd Nat.pow_succ_r'.
  lia.
Qed.

(* --- CKA/T_L-specific from here on. --- *)

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import SyntheticComputability.Models.T_L_Uniform.
From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

Lemma R_TL_FRACTRAN_computable : FRACTRAN_computable T_L_Uniform.R_TL.
Proof.
apply MM_computable_to_FRACTRAN_computable.
apply BSM_computable_to_MM_computable.
apply TM_computable_to_BSM_computable.
apply MMA_computable_to_TM_computable.
apply L_computable_closed_to_MMA_computable.
exact T_L_Uniform.L_computable_closed_R_TL.
Qed.

(* --- The splice itself -------------------------------------------------
   Appends, right after the pinned stop position i0 = length P0 + 1, a
   check "does qs 1 divide the output register (pos0)" (mma_mod_cst,
   already in the library, built for exactly this kind of divisibility
   test), then redirects: on divides (m=1 case), drain the scratch
   register (pos1, left holding the output value by mma_mod_cst) via
   mma_null, then jump unconditionally to 0 via mma_jump, landing at
   EXACTLY (0,(0,0)); on not-divides (m=0 case), just fall off the very
   end of the combined program, landing at (q_target,(0,b)) with
   q_target <> 0, automatically a stop state, automatically not
   (0,(0,0)) regardless of b. *)

Lemma pos01_neq : (pos0 : pos 2) <> pos1.
Proof. discriminate. Qed.

Lemma qs1_pos : 0 < qs 1.
Proof. rewrite /=. generalize (nthprime_3). lia. Qed.

Section Splice.

Variable (Q : list (nat * nat)).

Definition P0 : list (mm_instr (pos 2)) := fractran_mma Q.

(* i0 is the pinned stop position of P0 (see R_TL_MMA2_pinned/
   FRACTRAN_computable_to_MMA2_pinned above) -- the spliced-on code below
   starts exactly here. *)
Definition i0 : nat := length P0 + 1.

(* Length of the mma_mod_cst block that tests "does qs 1 divide the
   output register (pos0)", written into pos1 as a byproduct. Fixed at
   6 + 4*(qs 1) instructions by mma_mod_cst's own definition
   (mma_mod_cst_length) -- not a free parameter, just inlined here so
   p_target/q_target can be stated as plain nat additions instead of a
   call to List.length. *)
Definition modblock_len : nat := 6 + 4 * (qs 1).

(* Where control lands after the mod-test: on "divides", mma_mod_cst
   leaves the quotient in pos1 and falls through to here, which is the
   start of divide_block below. *)
Definition p_target : nat := i0 + modblock_len.

(* One past the end of the whole spliced program (divide_block is
   mma_null ++ mma_jump, 3 instructions) -- the position control falls
   off the end into on "not divides", i.e. the natural MM2-halting stop
   state for the m=0 case. *)
Definition q_target : nat := p_target + 3.

Definition divide_block : list (mm_instr (pos 2)) :=
  mma_null pos1 p_target ++ mma_jump 0 pos0.

Definition Psplice : list (mm_instr (pos 2)) :=
  P0 ++ mma_mod_cst pos0 pos1 p_target q_target (qs 1) i0 ++ divide_block.

Lemma Psplice_len : q_target = length Psplice + 1.
Proof.
unfold Psplice.
rewrite List.length_app.
rewrite List.length_app.
rewrite mma_mod_cst_length.
unfold divide_block.
rewrite List.length_app.
unfold mma_null, mma_jump. cbn [length].
unfold q_target, p_target, i0, modblock_len.
generalize (qs 1); generalize (length P0); intros; lia.
Qed.

Lemma P0_subcode : (1, P0) <sc (1, Psplice).
Proof. unfold Psplice; auto. Qed.

Lemma modcst_subcode : (i0, mma_mod_cst pos0 pos1 p_target q_target (qs 1) i0) <sc (1, Psplice).
Proof. unfold Psplice, i0; auto. Qed.

Lemma divide_block_subcode : (p_target, divide_block) <sc (1, Psplice).
Proof.
assert (Hlen : length (@mma_mod_cst 2 pos0 pos1 p_target q_target (qs 1) i0) = modblock_len)
  by apply mma_mod_cst_length.
unfold Psplice.
change p_target with (i0 + modblock_len) at 1.
rewrite <- Hlen.
unfold i0.
auto.
Qed.

Lemma Psplice_progress_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  sss_compute (@mma_sss 2) (1, Psplice) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (0, 0 ## 0 ## vec_nil).
Proof.
intros Hcompute [a Ha].
apply sss_progress_compute.
apply sss_compute_progress_trans with (i0, b ## 0 ## vec_nil).
{ eapply subcode_sss_compute; [exact P0_subcode | exact Hcompute]. }
assert (Hmod : sss_progress (@mma_sss 2) (i0, mma_mod_cst pos0 pos1 p_target q_target (qs 1) i0)
                 (i0, b ## 0 ## vec_nil) (p_target, 0 ## b ## vec_nil)).
{ apply (mma_mod_cst_divides_progress pos01_neq q_target i0 qs1_pos) with (a := a).
  - exact Ha.
  - simpl. now rewrite Nat.add_0_r. }
apply sss_progress_trans with (p_target, 0 ## b ## vec_nil).
{ eapply subcode_sss_progress; [exact modcst_subcode | exact Hmod]. }
assert (Hnull : sss_progress (@mma_sss 2) (p_target, mma_null pos1 p_target)
                  (p_target, 0 ## b ## vec_nil) (p_target + 1, 0 ## 0 ## vec_nil)).
{ apply mma_null_progress. simpl. f_equal. lia. }
assert (Hnull_sub : (p_target, mma_null pos1 p_target) <sc (1, Psplice)).
{ apply subcode_trans with (2 := divide_block_subcode).
  unfold divide_block; auto. }
apply sss_progress_trans with (p_target + 1, 0 ## 0 ## vec_nil).
{ eapply subcode_sss_progress; [exact Hnull_sub | exact Hnull]. }
assert (Hjump : sss_progress (@mma_sss 2) (p_target + 1, mma_jump 0 pos0)
                  (p_target + 1, 0 ## 0 ## vec_nil) (0, 0 ## 0 ## vec_nil)).
{ apply mma_jump_progress; reflexivity. }
assert (Hjump_sub : (p_target + 1, mma_jump 0 pos0) <sc (1, Psplice)).
{ apply subcode_trans with (2 := divide_block_subcode).
  unfold divide_block.
  apply subcode_right; auto. }
eapply subcode_sss_progress; [exact Hjump_sub | exact Hjump].
Qed.

Lemma Psplice_progress_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  sss_output (@mma_sss 2) (1, Psplice) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target, 0 ## b ## vec_nil).
Proof.
intros Hcompute Hndiv.
pose proof qs1_pos as Hk.
pose proof (Nat.div_mod_eq b (qs 1)) as Hdm.
pose proof (Nat.mod_upper_bound b (qs 1) (Nat.neq_sym _ _ (Nat.lt_neq _ _ Hk))) as Hmod.
assert (Hr0 : b mod qs 1 <> 0).
{ intros E. apply Hndiv. exists (b / qs 1). lia. }
set (a := b / qs 1) in *.
set (r := b mod qs 1) in *.
assert (Hbeq : b = a * qs 1 + r) by lia.
assert (Hr1 : 0 < r) by lia.
assert (Hr2 : r < qs 1) by lia.
split.
- apply sss_progress_compute.
  apply sss_compute_progress_trans with (i0, b ## 0 ## vec_nil).
  { eapply subcode_sss_compute; [exact P0_subcode | exact Hcompute]. }
  eapply subcode_sss_progress; [exact modcst_subcode |].
  apply (mma_mod_cst_not_divides_progress pos01_neq p_target i0 qs1_pos) with (a := a) (b := r).
  + exact Hbeq.
  + split; [exact Hr1 | exact Hr2].
  + simpl. now rewrite Nat.add_0_r.
- rewrite /out_code /=.
  pose proof Psplice_len as HL. lia.
Qed.

(* Bridge between Coq's Relation_Operators.clos_refl_trans (what
   MMA2_to_MM2.v's `↠` notation for MM2 uses) and stdpp's relations.rtc
   (what mm.v's mm2_R_soundness/completeness, hence R_target, are stated
   over) -- standard equivalence of reflexive-transitive closures over
   the same base relation, not exposed as a ready-made lemma anywhere in
   scope. *)

Lemma crt_to_rtc {A} (R : A -> A -> Prop) (x y : A) :
  clos_refl_trans _ R x y -> relations.rtc R x y.
Proof.
induction 1 as [x y Hxy | x | x y z Hxy IHxy Hyz IHyz].
- eapply relations.rtc_l; [exact Hxy | apply relations.rtc_refl].
- apply relations.rtc_refl.
- eapply relations.rtc_transitive; eassumption.
Qed.

Definition c_P : nat := codeOf (List.map mma_mm2_instr Psplice).

(* Explicit type ascription matters here: without it, the inferred type
   would state progOf (codeOf (...)) = ... with codeOf left unfolded,
   rather than folded to c_P -- which then makes `rewrite progOf_c_P`
   fail downstream (Computability/TL_Bridge.v) since the goal mentions c_P, not its
   unfolded codeOf form, and rewrite's matching doesn't delta-unfold to
   find it. *)
Definition progOf_c_P : progOf c_P = List.map mma_mm2_instr Psplice :=
  progOf_codeOf (List.map mma_mm2_instr Psplice).

Lemma Psplice_mm2_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  (progOf c_P) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)).
Proof.
intros Hc Hd.
rewrite progOf_c_P.
apply (mma_mma2_zero_reduction Psplice (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)).
split.
- now apply Psplice_progress_divides with (b := b).
- unfold out_code; cbn; left; lia.
Qed.

Lemma Psplice_mm2_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ (progOf c_P) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)).
Proof.
intros Hc Hnd Hbad.
rewrite progOf_c_P in Hbad.
apply (mma_mma2_zero_reduction Psplice (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)) in Hbad.
assert (Hout : sss_output (@mma_sss 2) (1, Psplice)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target, 0 ## b ## vec_nil)).
{ apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hdet : forall (instr : mm_instr (pos 2)) s t1 t2,
    mma_sss instr s t1 -> mma_sss instr s t2 -> t1 = t2) by (eapply mma_sss_fun; eauto).
pose proof (sss_output_fun Hdet Hout Hbad) as Heq.
pose proof Psplice_len as HL.
inversion Heq as [Heq0].
lia.
Qed.

(* --- Final step: connect to mm.v's own R_target directly (bypassing
   Theta_ours_MM2 entirely -- R_target c y := red_leq (progOf c) (1,(y,0))
   is already stated for ANY program via mm2_R_completeness/soundness,
   generalized over P inside mm.v's own MM2Adapter section). *)

Lemma Psplice_R_target_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  R_target c_P (ps 1 * enc 2 v).
Proof.
intros Hc Hd.
unfold R_target.
apply mm.mm2_R_completeness.
apply crt_to_rtc.
apply Psplice_mm2_divides with (b := b); [exact Hc | exact Hd].
Qed.

Lemma Psplice_R_target_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  ~ R_target c_P (ps 1 * enc 2 v).
Proof.
intros Hc Hnd Hred.
assert (Hbad : ~ (progOf c_P) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0))).
{ apply Psplice_mm2_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hout : sss_output (@mma_sss 2) (1, Psplice)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target, 0 ## b ## vec_nil)).
{ apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]. }
assert (Hterm : sss_terminates (@mma_sss 2) (1, Psplice) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  by (exists (q_target, 0 ## b ## vec_nil); exact Hout).
apply (mma_mma2_reduction Psplice (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)) in Hterm.
destruct Hterm as [s2 [Hreach Hstop]].
assert (Hs2 : s2 <> (0, (0, 0))).
{ intros ->. apply Hbad. rewrite progOf_c_P. exact Hreach. }
apply crt_to_rtc in Hreach.
assert (Hred' : red_leq (List.map mma_mm2_instr Psplice)
                  (mma_mm2_state (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))).
{ unfold R_target in Hred. rewrite progOf_c_P in Hred. exact Hred. }
assert (Hsound : s2 = (0, (0, 0))).
{ eapply mm.mm2_R_soundness; [exact Hreach | exact Hstop | exact Hred']. }
exact (Hs2 Hsound).
Qed.

End Splice.

Definition R_TL_MMA2_pinned := FRACTRAN_computable_to_MMA2_pinned R_TL_FRACTRAN_computable.

(* --- Payoff: R_TL bridged all the way to mm.v's own R_target.

   The `m <= 1` hypothesis is not a limitation of the splice construction
   itself (Psplice/the divides-test above works for any m, distinguishing
   "m = 0" from "m > 0" via a single divisibility check) -- it's here
   because it's all A0_L/B1_L (Theorem17_KATerm.v, Computability/TL_Bridge.v) ever
   need: those sets only ever ask about R_TL's outputs 0 and 1, never
   larger m. Stating the connection only for m <= 1 keeps this theorem's
   proof from having to characterize what happens for m >= 2 (which the
   divides-test alone doesn't determine, since divides (qs 1 ^ m) is not
   injective across m without the accompanying ~divides (qs 1 ^ (S m))
   bound also pinning m from above). *)

Theorem R_TL_R_target_connection :
  exists c : nat, forall (v : Vector.t nat 2) (m : nat),
    m <= 1 -> T_L_Uniform.R_TL v m -> (m = 1 <-> R_target c (ps 1 * enc 2 v)).
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
exists (c_P Q).
intros v m Hm1 HR.
apply HQ in HR.
destruct HR as [b [Hcompute [Hdiv1 Hdiv2]]].
split.
- intros ->.
  assert (Hdb : divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
  apply Psplice_R_target_divides with (b := b); [exact Hcompute | exact Hdb].
- intros HRt.
  destruct (Nat.eq_dec m 0) as [-> | Hne]; [| lia].
  exfalso.
  assert (Hndb : ~ divides (qs 1) b)
    by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
  assert (Hcontra : ~ R_target (c_P Q) (ps 1 * enc 2 v))
    by (apply Psplice_R_target_not_divides with (b := b); assumption).
  exact (Hcontra HRt).
Qed.
