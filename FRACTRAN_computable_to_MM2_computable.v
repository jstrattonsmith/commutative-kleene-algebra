From Stdlib Require Import Unicode.Utf8 ssreflect Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.MinskyMachines Require Import MM MM2 MMA Util.MM2_facts.
From Undecidability.MinskyMachines.Reductions Require Import MM_to_MMA2 MMA2_to_MM2.
Import MM2Notations.

From Undecidability.Shared.Libs.DLW Require Import (* utils  pos  subcode sss  *)
  gcd pos vec godel_coding compiler_correction.
Import vec_notations.

Import Vector.VectorNotations.

From Undecidability.MinskyMachines Require Import mm_defs mma_defs fractran_mma mma_utils.
From Undecidability.FRACTRAN Require Import fractran_utils prime_seq mm_fractran.
From Undecidability.Shared.Libs.DLW Require Import utils sss subcode.


Definition MMA2_computable {k} (R : Vector.t nat k -> nat -> Prop) :=
  ∃ (P : list (mm_instr (pos 2))), ∀ (v : vec nat k) (m : nat),
    R v m <-> exists i b,
          sss_output ( @mma_sss _ ) (1, P) (1, (ps 1 * enc 2 v)##0##vec_nil) (i, b##0##vec_nil) /\
          divides (qs 1 ^ m) b /\
          ~ divides (qs 1 ^ (S m)) b.

Definition MM2_computable {k} (R : Vector.t nat k -> nat -> Prop) :=
  exists P : list mm2_instr,
    forall v : Vector.t nat k, forall m,
      R v m <->
        exists i b,
          P // (1, (ps 1 * enc 2 v, 0)) ↠ (i, (b, 0)) /\
          mm2_stop P (i, (b, 0)) /\
          divides (qs 1 ^ m) b /\
          ~ divides (qs 1 ^ (S m)) b.

Lemma not_div x y : x ≠ 0 -> (¬ divides x y) -> ∀ m, ¬ divides (x^(S m)) ((x ^ m) * y).
Proof.
move=> Hx0 notDiv.
elim => [|m IH] /=; first by rewrite Nat.mul_1_r Nat.add_0_r.
rewrite -Nat.pow_succ_r'.
move=> [k Hk]; apply: IH; move: Hk.
exists k.
move: Hk.
rewrite [X in _ = X]Nat.mul_comm Nat.pow_succ_r' Nat.mul_assoc.
move=> ?; rewrite [X in _ = X]Nat.mul_comm.
apply (Nat.mul_cancel_l _ _ _ Hx0); lia.
Qed.

Theorem fractran_computable_to_mma2_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  FRACTRAN_computable R -> MMA2_computable R.
Proof.
  move=> [P [Preg rest]].
  exists (fractran_mma P).
  move=> v m; rewrite {}rest; split.
  - move=> [j [/eval_iff H Hdiv]].
    move: H => [Hcompute Hstop].
    eexists; eexists.
    split.
    + split; first apply (fractran_mma_sound Preg Hcompute Hstop).
      rewrite /=; right; lia.
    + split; first (rewrite Nat.mul_comm; apply divides_left).
      rewrite Nat.mul_comm.
      have qs_not_0 : qs 1 ≠ 0 by rewrite /= nthprime_3.
      apply (not_div _ _ qs_not_0 Hdiv).
  -
    move=> [i [b [Hout [Hdiv1 Hdiv2]]]].
    have Hterm : sss_terminates (@mma_sss 2) (1, fractran_mma P)
                   (1, (ps 1 * enc 2 v) ## 0 ## vec_nil).
    { destruct Hout as [Hcompute Hcode].
      exists (i, b ## 0 ## vec_nil).
      exact: conj Hcompute Hcode. }
    apply fractran_mma_reduction in Hterm; last exact Preg.
    destruct Hterm as [j [Hcompute Hstop]].
    have Hbeqj : b = j.
    { have Hreach : sss_compute (@mma_sss 2) (1, fractran_mma P)
                    (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
                    (length (fractran_mma P) + 1, j ## 0 ## vec_nil).
      { apply (fractran_mma_sound Preg Hcompute Hstop). }
      have Hout2 : sss_output (@mma_sss 2) (1, fractran_mma P)
                     (1, (ps 1 * enc 2 v) ## 0 ## vec_nil)
                     (length (fractran_mma P) + 1, j ## 0 ## vec_nil).
      { split; first exact: Hreach.
        rewrite /=; lia. }
      have Hdet : forall (instr : mm_instr (pos 2)) s t1 t2,
          mma_sss instr s t1 -> mma_sss instr s t2 -> t1 = t2 by eapply mma_sss_fun; eauto.
      have Heq := sss_output_fun _ Hout Hout2.
      have {}Heq := Heq Hdet.
      by case: Heq.
    }
    subst b.
    case: Hdiv1 => j0 Hj0.
    exists j0.
    split; first by rewrite -{}Hj0; apply eval_iff; by split.
    move=> [d Hd].
    apply Hdiv2.
    exists d.
    rewrite Hj0 Hd Nat.pow_succ_r'.
    lia.
Qed.

Lemma mma_mm2_state_inv (sf : mm2_state) : ∃ sf', sf = mma_mm2_state sf'.
Proof.
case: sf => a [b1 b2].
by exists (a, b1##b2##vec_nil).
Qed.

Theorem mma2_computable_to_mm2_computable {k} (R : Vector.t nat k -> nat -> Prop) :
  MMA2_computable R -> MM2_computable R.
Proof.
rewrite /MMA2_computable /MM2_computable.
move=> [P rest].
exists (List.map mma_mm2_instr P).
move=> v ?.
Local Definition mm2_mma_state (x: (nat*(nat*nat))):=
    match x with
    | (ii, (ia, ib)) => (ii, ia##ib##vec_nil) end.
  (* TODO: this should come from theories/MinskyMachines/Reductions/MMA2_to_MM2.v on line 70 instead. *)
have mm2_mma_mm2_state s : mm2_mma_state (mma_mm2_state s) = s.
{
  destruct s as (i,v').
    vec split v' with a.
    vec split v' with b.
    vec nil v'.
    trivial.
}
rewrite {}rest; split.
- (* → : MMA2 output -> MM2 run *)
  move=> [i [b [Hout [Hdiv1 Hdiv2]]]].
  exists i, b.
  destruct Hout as [Hcompute Hcode].
  split.
  (* repeat split; auto; clear Hdiv1 Hdiv2. *)
  + apply MMA2_to_MM2.mma_mm2_compute_equiv in Hcompute.
    rewrite /mma_mm2_state /= in Hcompute.
    exact Hcompute.
  + (split; last by (split; [exact Hdiv1 | exact Hdiv2])); clear Hdiv1 Hdiv2.
    have [sf [Hreach' Hstop']] :
      mm2_terminates (ListDef.map mma_mm2_instr P)
                     (mma_mm2_state (1, [ps 1 * enc 2 v; 0])).
    { apply mma_mm2_terminates.
      exists (i, b ## 0 ## vec_nil).
      exact: conj Hcompute Hcode. }
    have Hsfval : mm2_mma_state sf = (i, b ## 0 ## vec_nil).
    {
      have [sf' Hsf'] : ∃ sf', sf = mma_mm2_state sf' by apply mma_mm2_state_inv.
      rewrite Hsf' in Hreach'.
      apply MMA2_to_MM2.mma_mm2_compute_equiv  in Hreach'.
      have Hcode' : out_code (fst sf') (1, P).
      {
        rewrite mm2_stop_index_iff in Hstop'.
        destruct sf as [??];
        destruct sf' as [??].
        rewrite /= in Hsf'.
        case: Hsf'.
        case: Hstop' => /= [H | H]; move=> <- _; first by left; rewrite H.
        right; rewrite List.length_map in H; lia.
      }
      rewrite ( @sss_compute_fun _ _ _ _ _ _ _ _ Hcode Hcode' Hcompute Hreach');
        first by apply mma_sss_fun.
      by rewrite Hsf' mm2_mma_mm2_state.
    }
    have Hsfval2 : sf = (i, (b, 0)).
    { move: Hsfval. case sf => n [a b'] //=.
      by case; move=> -> -> ->. }
    subst sf; exact Hstop'.
- move=> [i [b [Hreach [Hstop [Hdiv1 Hdiv2]]]]].
  exists i, b.
  (split; last by (split; [exact Hdiv1 | exact Hdiv2])); clear Hdiv1 Hdiv2.
  have Hmm2term : mm2_terminates (List.map mma_mm2_instr P) (1, (ps 1 * enc 2 v, 0)).
  { exists (i, (b, 0)); split; [exact Hreach | exact Hstop]. }
  apply mm2_mma_terminates in Hmm2term.
  move: Hmm2term.
  have <- : mm2_mma_state (1, (ps 1 * enc 2 v, 0)) =
                  (1, (ps 1 * enc 2 v) ## 0 ## vec_nil) by done.
  move=> [sf [Hreach' Hcode']].
  split; first by apply MMA2_to_MM2.mma_mm2_compute_equiv;
    rewrite /mma_mm2_state /=;
    exact: Hreach.
  rewrite mm2_stop_index_iff in Hstop.
  move: Hstop; rewrite /mm2_stop_index_iff /=; move=> [-> | H]; first by left.
  right; rewrite List.length_map in H; lia.
Qed.