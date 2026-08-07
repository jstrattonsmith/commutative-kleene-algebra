(* Phase 2 take 3 -- Task #5. Defines A0_L' as a superset of A0_L,
   disjoint from B1_L, enumerable -- built directly on top of
   R_TL_R_target_connection (Task #4, TLUniform_Bridge.v).

   Key design point: R_target/red_leq is a KA-term-level *safety*
   statement (a language-containment fact), not directly a termination
   witness -- it does NOT, by itself, imply the underlying MM2 program
   halts (mm2_R_completeness only goes halts-at-(0,0) -> red_leq; there's
   no direct red_leq -> halts implication in mm.v, and there shouldn't
   be one, since that would make R_target decidable, contradicting the
   whole undecidability result). So A0_L' is NOT defined directly via
   R_target (that wouldn't obviously be enumerable). Instead it's defined
   via Theta_ours_MM2/A0_MM2 (EffectiveInseparability_MM2.v), whose
   enumerability is already proven there (step-indexed search, same
   shape as Theta_ours_L/A0_L) -- R_target only comes in later (Task #6)
   via the EASY direction (halted-at-(0,0) -> red_leq), which is all a
   reduction to R_target actually needs. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM2 MMA mm_defs mma_defs fractran_mma mma_utils.
Import MM2Notations.
From Undecidability.Shared.Libs.DLW Require Import gcd pos vec sss subcode.
Import vec_notations.
From kacc Require Import TLUniform_MM2.
From kacc Require Import TLUniform_Bridge.
From kacc Require Import EffectiveInseparability_MM2.
Require kacc.mm.
From Undecidability.MinskyMachines.Reductions Require Import MMA2_to_MM2.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
Require Import SyntheticComputability.Axioms.EA.

(* --- 0. rtc -> a concrete step count, via mm2_iter ---------------------
   The converse of mm2_iter_rtc: reachability (rtc, used by
   mm2_R_completeness/soundness) is witnessed by SOME finite number of
   mm2_step_total iterations (mm2_iter, used by mm2_haltedAt/
   mm2_outcome_at/Theta_ours_MM2's own step-indexed search). Not exposed
   anywhere in scope as a ready lemma; standard fact given mm2_step's own
   functionality (mm.mm2_step_fun_spec). *)

Lemma rtc_to_iter (P : list mm2_instr) (s0 s1 : mm2_state) :
  relations.rtc (mm2_step P) s0 s1 -> exists n, mm2_iter P n s0 = s1.
Proof.
induction 1 as [s0 | s0 s0' s1 Hstep Hrtc IH].
- exists 0. reflexivity.
- destruct IH as [n Hn].
  exists (S n).
  unfold mm2_iter.
  rewrite Nat.iter_succ_r.
  apply mm.mm2_step_fun_spec in Hstep.
  unfold mm2_step_total.
  rewrite Hstep.
  fold (mm2_iter P n s0').
  exact Hn.
Qed.

(* --- 1. Connect the splice's MM2-level facts (TLUniform_Bridge.v)
   directly to Theta_ours_MM2/A0_MM2, bypassing R_target entirely (that
   detour is only needed later, for Task #6's actual KA-term reduction).
   (0,(0,0)) is always mm2_stop (index 0 has no instruction), so once
   rtc_to_iter gives a concrete step count reaching it, mm2_haltedAt/
   mm2_outcome_at fire immediately. *)

Lemma mm2_step_fun_zero (P : list mm2_instr) : mm.mm2_step_fun P (0, (0, 0)) = None.
Proof. reflexivity. Qed.

Lemma mma_mm2_state_22 (i x y : nat) : mma_mm2_state (i, x ## y ## vec_nil) = (i, (x, y)).
Proof. reflexivity. Qed.

Section Splice2.

Variable (Q : list (nat * nat)).

Lemma Psplice_theta_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0 Q, b ## 0 ## vec_nil) ->
  divides (qs 1) b ->
  Θ_ours_MM2 (c_P Q) (ps 1 * enc 2 v) =! 1.
Proof.
intros Hc Hd.
pose proof (@Psplice_mm2_divides Q v b Hc Hd) as Hreach.
apply crt_to_rtc in Hreach.
destruct (@rtc_to_iter _ _ _ Hreach) as [n Hn].
apply seval_hasvalue. exists n.
rewrite seval_Theta_ours_MM2. unfold mm2_outcome_at.
assert (Hhalted : mm2_haltedAt (progOf (c_P Q)) n (1, (ps 1 * enc 2 v, 0)) = true).
{ unfold mm2_haltedAt. rewrite Hn. now rewrite mm2_step_fun_zero. }
rewrite Hhalted, Hn.
now rewrite (proj2 (mm2_state_eqb_true (0, (0, 0)) (0, (0, 0))) eq_refl).
Qed.

Lemma Psplice_theta_not_divides (v : Vector.t nat 2) (b : nat) :
  sss_compute (@mma_sss 2) (1, P0 Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (i0 Q, b ## 0 ## vec_nil) ->
  ~ divides (qs 1) b ->
  Θ_ours_MM2 (c_P Q) (ps 1 * enc 2 v) =! 0.
Proof.
intros Hc Hnd.
assert (Hbad : ~ (progOf (c_P Q)) // (1, (ps 1 * enc 2 v, 0)) ↠ (0, (0, 0)))
  by (apply Psplice_mm2_not_divides with (b := b); [exact Hc | exact Hnd]).
assert (Hout : sss_output (@mma_sss 2) (1, Psplice Q)
                 (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) (q_target Q, 0 ## b ## vec_nil))
  by (apply Psplice_progress_not_divides with (b := b); [exact Hc | exact Hnd]).
assert (Hterm : sss_terminates (@mma_sss 2) (1, Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil))
  by (exists (q_target Q, 0 ## b ## vec_nil); exact Hout).
apply (mma_mma2_reduction (Psplice Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)) in Hterm.
destruct Hterm as [s2 [Hreach Hstop]].
assert (Hs2 : s2 <> (0, (0, 0))).
{ intros ->. apply Hbad. rewrite progOf_c_P. exact Hreach. }
apply crt_to_rtc in Hreach.
destruct (@rtc_to_iter _ _ _ Hreach) as [n Hn].
rewrite mma_mm2_state_22 in Hn.
apply seval_hasvalue. exists n.
rewrite seval_Theta_ours_MM2. unfold mm2_outcome_at.
assert (Hhalted : mm2_haltedAt (progOf (c_P Q)) n (1, (ps 1 * enc 2 v, 0)) = true).
{ unfold mm2_haltedAt. rewrite progOf_c_P, Hn.
  destruct (mm.mm2_step_fun (List.map mma_mm2_instr (Psplice Q)) s2) as [s'|] eqn:E; [| reflexivity].
  exfalso. apply Hstop with (s' := s'). apply mm.mm2_step_fun_spec. exact E. }
rewrite Hhalted, progOf_c_P, Hn.
destruct (mm2_state_eqb s2 (0, (0, 0))) eqn:Es; [| reflexivity].
exfalso. apply Hs2. apply mm2_state_eqb_true. exact Es.
Qed.

(* --- 2. A0_L' itself: reuses A0_MM2's own enumerability shape directly
   (Theta_ours_MM2's step-indexed search), just aimed at (c_P Q, ps1*enc2
   (i,j)) instead of an arbitrary (c,y) pair. *)

Definition A0_L' (z : nat) : Prop :=
  Θ_ours_MM2 (c_P Q) (ps 1 * enc 2 (fst (unembed z) ## snd (unembed z) ## vec_nil)) =! 1.

Lemma A0_L'_enumerable : enumerable A0_L'.
Proof.
apply (proj2 (enum_iff A0_L')).
exists (fun z n =>
  match partial.seval
          (Θ_ours_MM2 (c_P Q) (ps 1 * enc 2 (fst (unembed z) ## snd (unembed z) ## vec_nil))) n
  with Some v => Nat.eqb v 1 | None => false end).
intros z. unfold A0_L'. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct (partial.seval
    (Θ_ours_MM2 (c_P Q) (ps 1 * enc 2 (fst (unembed z) ## snd (unembed z) ## vec_nil))) n)
    as [v0|] eqn:E; [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

End Splice2.

(* --- 3. Connect A0_L/B1_L (Theta_ours_L, i.e. T_L) to R_TL (T_L_Uniform.v)
   -- both are ultimately just "T_L i j eventually outputs m", but phrased
   through different scaffolding (Theta_ours_L's plain hasvalue vs R_TL's
   mu-search over TL_bit), so need an explicit bridge, including finding
   a LEAST witness n for the mu-search side (T_L is monotonic, so once it
   outputs Some m at any n it does so at all larger n too, but the search
   specifically wants the first such n). *)

Lemma theta_ours_L_iff (c y v : nat) : Θ_ours_L c y =! v <-> exists n, T_L c y n = Some v.
Proof. unfold Θ_ours_L, θ_L, hasvalue. reflexivity. Qed.

Lemma T_L_first_or_none (c y n : nat) :
  (forall k, k <= n -> T_L c y k = None) \/
  (exists n0 v0, n0 <= n /\ T_L c y n0 = Some v0 /\ forall k, k < n0 -> T_L c y k = None).
Proof.
induction n as [| n' [IHnone | [n0 [v0 [Hn0 [Hval Hmin]]]]]].
- destruct (T_L c y 0) as [v0|] eqn:E0.
  + right. exists 0, v0. repeat split; auto; intros k Hk; lia.
  + left. intros k Hk. assert (k = 0) by lia. congruence.
- destruct (T_L c y (S n')) as [v0|] eqn:ES.
  + right. exists (S n'), v0. repeat split; auto.
    intros k Hk. apply IHnone. lia.
  + left. intros k Hk. destruct (Nat.eq_dec k (S n')) as [-> | Hne]; [exact ES |].
    apply IHnone. lia.
- right. exists n0, v0. repeat split; auto; lia.
Qed.

Lemma T_L_least_witness (c y v : nat) :
  (exists n, T_L c y n = Some v) ->
  exists n, T_L c y n = Some v /\ forall k, k < n -> T_L c y k = None.
Proof.
intros [n Hn].
destruct (T_L_first_or_none c y n) as [Hnone | [n0 [v0 [Hn0 [Hval Hmin]]]]].
- exfalso. specialize (Hnone n (le_n n)). congruence.
- exists n0. split; [| exact Hmin].
  pose proof (@monotonic_T_L c y) as Hmono.
  specialize (@Hmono n0 v0 Hval n Hn0).
  congruence.
Qed.

Lemma R_TL_iff (v : Vector.t nat 2) (m : nat) :
  T_L_Uniform.R_TL v m <->
  exists n, T_L (Vector.hd v) (Vector.hd (Vector.tl v)) n = Some m.
Proof.
unfold T_L_Uniform.R_TL.
set (i := Vector.hd v). set (j := Vector.hd (Vector.tl v)).
rewrite TL_val_iff.
split.
- intros [n [_ [_ Hn]]]. exists n. rewrite <- (@T_L'_eq i j n). exact Hn.
- intros Hex.
  destruct (@T_L_least_witness i j m Hex) as [n [Hn Hmin]].
  exists n. repeat split.
  + unfold TL_bit. rewrite (@T_L'_eq i j n), Hn. reflexivity.
  + intros k Hk. unfold TL_bit. rewrite (@T_L'_eq i j k), (Hmin k Hk). reflexivity.
  + rewrite (@T_L'_eq i j n). exact Hn.
Qed.

(* --- 4. Put it together: A0_L subset, disjoint from B1_L, enumerable. -- *)

Section Splice3.

Variable (Q : list (nat * nat)).
Hypothesis HQ : forall (v : Vector.t nat 2) (m : nat),
  T_L_Uniform.R_TL v m <->
  exists b,
    sss_compute (@mma_sss 2) (1, fractran_mma Q) (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
      (length (fractran_mma Q) + 1, b ## 0 ## vec_nil) /\
    divides (qs 1 ^ m) b /\ ~ divides (qs 1 ^ (S m)) b.

Let z_vec (z : nat) : Vector.t nat 2 := fst (unembed z) ## snd (unembed z) ## vec_nil.

Lemma A0_L_subset (z : nat) : A0_L z -> A0_L' Q z.
Proof.
intros HA. apply theta_ours_L_iff in HA.
assert (HR1 : T_L_Uniform.R_TL (z_vec z) 1) by (apply R_TL_iff; exact HA).
apply HQ in HR1. destruct HR1 as [b [Hcompute [Hdiv1 Hdiv2]]].
assert (Hdb : divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv1).
unfold A0_L'. apply Psplice_theta_divides with (b := b); exact Hcompute || exact Hdb.
Qed.

Lemma A0_L'_B1_L_disjoint (z : nat) : A0_L' Q z -> ~ B1_L z.
Proof.
intros HA' HB. apply theta_ours_L_iff in HB.
assert (HR0 : T_L_Uniform.R_TL (z_vec z) 0) by (apply R_TL_iff; exact HB).
apply HQ in HR0. destruct HR0 as [b [Hcompute [Hdiv1 Hdiv2]]].
assert (Hndb : ~ divides (qs 1) b) by (rewrite <- (Nat.pow_1_r (qs 1)); exact Hdiv2).
assert (HB0 : Θ_ours_MM2 (c_P Q) (ps 1 * enc 2 (z_vec z)) =! 0)
  by (apply Psplice_theta_not_divides with (b := b); exact Hcompute || exact Hndb).
unfold A0_L' in HA'.
pose proof (hasvalue_det HA' HB0) as Heq.
discriminate Heq.
Qed.

End Splice3.

(* --- Task #5's deliverable. --- *)

Theorem A0_L_prime_exists :
  exists A0Lp : nat -> Prop,
    (forall z, A0_L z -> A0Lp z) /\
    (forall z, A0Lp z -> ~ B1_L z) /\
    enumerable A0Lp.
Proof.
destruct R_TL_MMA2_pinned as [Q HQ].
exists (A0_L' Q).
split; [| split].
- exact (@A0_L_subset Q HQ).
- exact (@A0_L'_B1_L_disjoint Q HQ).
- exact (@A0_L'_enumerable Q).
Qed.
