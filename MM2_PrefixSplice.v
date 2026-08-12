(* General "specialize an MM2 program by splicing a prefix in front of it"
   interface. Decoupled from any specific prefix construction: this file
   knows nothing about pair_xy, mma_mult_cst_with_zero, or any other
   register-arithmetic combinator. It only knows how to splice an arbitrary
   prefix program in front of an arbitrary program, shift the prefix's own
   jump targets accordingly, and transport `mm2_outcome_at` across the
   splice given a black-box "the prefix, run from (1,(y,0)), reaches
   (1+len(Pre), (f y, 0))" spec for the prefix's own input/output relation
   `f : nat -> nat`.

   Lifted out of SMN_MM2.v, whose own `mm2_prefix` (computing
   `pair_xy x _`) is exactly one instance of `Pre`/`f` here -- see
   SMN_MM2.v for that instantiation. The point of splitting this out:
   this splicing engine is reusable for ANY compile-time-constant-indexed
   prefix, e.g. an EXP_K-style combinator (raw register ->
   K^(register)) would be expected to be another instance, not a
   variant that needs its own copy of this reasoning. *)

From Stdlib Require Import Arith List Lia.
From Stdlib Require Import Relations.Relation_Operators.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

From kacc.MM2 Require Import Stepper.
From kacc Require Import CKA.Encoding.
From kacc Require Import MM2.Simulator.
From kacc Require Import EffectiveInseparability_MM2.

(* --- 0. Splicing a prefix in front of a program, with jump targets
   shifted accordingly. -------------------------------------------------- *)

Definition shift_instr (L : nat) (i : mm2_instr) : mm2_instr :=
  match i with
  | mm2_dec_a q => mm2_dec_a (match q with 0 => 0 | _ => q + L end)
  | mm2_dec_b q => mm2_dec_b (match q with 0 => 0 | _ => q + L end)
  | _ => i
  end.

Definition shift_state (L : nat) (s : nat * (nat * nat)) : nat * (nat * nat) :=
  match s with (p,(a,b)) => (match p with 0 => 0 | _ => p + L end, (a,b)) end.

Definition splice (Pre M : list mm2_instr) : list mm2_instr :=
  Pre ++ List.map (shift_instr (length Pre)) M.

Lemma mm2_atom_fun_shift (L i : nat) (rho : mm2_instr) (a b : nat) :
  mm2_atom_fun (shift_instr L rho) (shift_state L (S i, (a, b)))
  = shift_state L (mm2_atom_fun rho (S i, (a, b))).
Proof.
destruct rho as [ | | q | q]; simpl; try reflexivity.
- destruct a as [| a]; reflexivity.
- destruct b as [| b]; reflexivity.
Qed.

Lemma mm2_step_fun_shift (Pre M : list mm2_instr) (s : nat * (nat * nat)) :
  mm2_step_fun (splice Pre M) (shift_state (length Pre) s)
  = option_map (shift_state (length Pre)) (mm2_step_fun M s).
Proof.
destruct s as [[| i] [a b]]; [reflexivity |].
unfold shift_state.
replace (S i + length Pre) with (S (i + length Pre)) by lia.
unfold mm2_step_fun, splice; simpl.
rewrite nth_error_app2; [| lia].
replace (i + length Pre - length Pre) with i by lia.
rewrite nth_error_map.
destruct (nth_error M i) as [rho |] eqn:E; simpl; [| reflexivity].
f_equal.
apply (mm2_atom_fun_shift (length Pre) i rho a b).
Qed.

Lemma mm2_step_total_shift (Pre M : list mm2_instr) (s : nat * (nat * nat)) :
  mm2_step_total (splice Pre M) (shift_state (length Pre) s)
  = shift_state (length Pre) (mm2_step_total M s).
Proof.
unfold mm2_step_total.
rewrite mm2_step_fun_shift.
destruct (mm2_step_fun M s); reflexivity.
Qed.

Lemma mm2_iter_shift (Pre M : list mm2_instr) (n : nat) (s : nat * (nat * nat)) :
  mm2_iter (splice Pre M) n (shift_state (length Pre) s)
  = shift_state (length Pre) (mm2_iter M n s).
Proof.
induction n as [| n IH].
- reflexivity.
- rewrite !mm2_iter_S, IH. apply mm2_step_total_shift.
Qed.

Lemma mm2_haltedAt_shift (Pre M : list mm2_instr) (n : nat) (s : nat * (nat * nat)) :
  mm2_haltedAt (splice Pre M) n (shift_state (length Pre) s)
  = mm2_haltedAt M n s.
Proof.
unfold mm2_haltedAt.
rewrite mm2_iter_shift, mm2_step_fun_shift.
destruct (mm2_step_fun M (mm2_iter M n s)); reflexivity.
Qed.

Lemma shift_state_eqb_zero (L : nat) (s : nat * (nat * nat)) :
  mm2_state_eqb (shift_state L s) (0, (0, 0)) = mm2_state_eqb s (0, (0, 0)).
Proof.
destruct s as [[| p] [a b]]; unfold shift_state, mm2_state_eqb; simpl.
- reflexivity.
- destruct (p + L) eqn:E; [lia | reflexivity].
Qed.

(* --- 1. Relational-to-step-count conversion, and prefix composability -- *)

Lemma mm2_iter_add (P : list mm2_instr) (n1 n2 : nat) (s : nat * (nat * nat)) :
  mm2_iter P (n1 + n2) s = mm2_iter P n2 (mm2_iter P n1 s).
Proof.
unfold mm2_iter. rewrite Nat.add_comm. apply Nat.iter_add.
Qed.

Lemma clos_refl_trans_to_iter_strong (P : list mm2_instr) (x y : nat * (nat * nat)) :
  clos_refl_trans _ (mm2_step P) x y ->
  exists n, mm2_iter P n x = y
            /\ (forall k, k < n -> mm2_step_fun P (mm2_iter P k x) <> None).
Proof.
induction 1 as [x y Hxy | x | x y z H1 IH1 H2 IH2].
- exists 1. split.
  + unfold mm2_iter. simpl. unfold mm2_step_total.
    apply mm2_step_fun_spec in Hxy. rewrite Hxy. reflexivity.
  + intros k Hk. assert (k = 0) by lia. subst k.
    unfold mm2_iter. simpl.
    apply mm2_step_fun_spec in Hxy. rewrite Hxy. discriminate.
- exists 0. split; [reflexivity | intros k Hk; lia].
- destruct IH1 as [n1 [Hn1 Hnh1]].
  destruct IH2 as [n2 [Hn2 Hnh2]].
  exists (n1 + n2). split.
  + rewrite mm2_iter_add, Hn1. exact Hn2.
  + intros k Hk.
    destruct (Compare_dec.lt_dec k n1) as [Hlt | Hge].
    * apply Hnh1. exact Hlt.
    * assert (Hk' : k = n1 + (k - n1)) by lia.
      rewrite Hk', mm2_iter_add, Hn1.
      apply Hnh2. lia.
Qed.

Lemma mm2_step_fun_app_l (Pre Rest : list mm2_instr) (p a b : nat) :
  1 <= p -> p <= length Pre ->
  mm2_step_fun (Pre ++ Rest) (p, (a, b)) = mm2_step_fun Pre (p, (a, b)).
Proof.
intros Hp1 Hp2.
destruct p as [| i]; [lia |].
unfold mm2_step_fun; simpl.
rewrite nth_error_app1; [reflexivity | lia].
Qed.

Lemma mm2_step_fun_app_l_state (Pre Rest : list mm2_instr) (s : nat * (nat * nat)) :
  1 <= fst s -> fst s <= length Pre ->
  mm2_step_fun (Pre ++ Rest) s = mm2_step_fun Pre s.
Proof.
destruct s as [p [a b]]; simpl; apply mm2_step_fun_app_l.
Qed.

Lemma mm2_step_fun_some_range (P : list mm2_instr) (s s' : nat * (nat * nat)) :
  mm2_step_fun P s = Some s' -> 1 <= fst s /\ fst s <= length P.
Proof.
intros H.
destruct s as [p [a b]]; simpl in *.
destruct p as [| i]; [discriminate |].
unfold mm2_step_fun in H. simpl in H.
destruct (nth_error P i) as [rho |] eqn:Eni; simpl in H; [| discriminate].
split; [lia |].
assert (Hlt : i < length P) by (apply nth_error_Some; rewrite Eni; discriminate).
lia.
Qed.

Lemma mm2_iter_app_l (Pre Rest : list mm2_instr) (n : nat) (y0 : nat) :
  (forall k, k < n -> mm2_step_fun Pre (mm2_iter Pre k (1, (y0, 0))) <> None) ->
  mm2_iter (Pre ++ Rest) n (1, (y0, 0)) = mm2_iter Pre n (1, (y0, 0)).
Proof.
induction n as [| n IH]; intros Hnh.
- reflexivity.
- assert (Hn : mm2_iter (Pre ++ Rest) n (1, (y0, 0)) = mm2_iter Pre n (1, (y0, 0))).
  { apply IH. intros k Hk. apply Hnh. lia. }
  rewrite mm2_iter_S, Hn.
  unfold mm2_step_total.
  assert (Hne := Hnh n (Nat.lt_succ_diag_r n)).
  destruct (mm2_step_fun Pre (mm2_iter Pre n (1, (y0, 0)))) as [s' |] eqn:E;
    [| congruence].
  rewrite mm2_iter_S.
  unfold mm2_step_total.
  assert (Hrange := mm2_step_fun_some_range E).
  rewrite (mm2_step_fun_app_l_state Rest (proj1 Hrange) (proj2 Hrange)).
  rewrite E. reflexivity.
Qed.

(* --- 2. The specialization interface ----------------------------------- *)

Definition specialize_prog (Pre : list mm2_instr) (c : nat) : list mm2_instr :=
  splice Pre (progOf c).

Definition specialize (Pre : list mm2_instr) (c : nat) : nat :=
  codeOf (specialize_prog Pre c).

Lemma progOf_specialize (Pre : list mm2_instr) (c : nat) :
  progOf (specialize Pre c) = specialize_prog Pre c.
Proof. unfold specialize. apply progOf_codeOf. Qed.

Lemma splice_prefix_reaches (Pre : list mm2_instr) (f : nat -> nat)
  (Hspec : forall y, clos_refl_trans _ (mm2_step Pre) (1, (y, 0))
                        (1 + length Pre, (f y, 0)))
  (y : nat) (M : list mm2_instr) :
  exists k0,
    mm2_iter (splice Pre M) k0 (1, (y, 0))
      = shift_state (length Pre) (1, (f y, 0))
    /\ (forall k, k < k0 ->
          mm2_step_fun (splice Pre M)
            (mm2_iter (splice Pre M) k (1, (y, 0))) <> None).
Proof.
destruct (clos_refl_trans_to_iter_strong (Hspec y)) as [k0 [H1 H2]].
exists k0. split.
- unfold splice.
  rewrite (mm2_iter_app_l (List.map (shift_instr (length Pre)) M) H2).
  rewrite H1. unfold shift_state. reflexivity.
- intros k Hk.
  assert (Hk' : forall k', k' < k ->
    mm2_step_fun Pre (mm2_iter Pre k' (1, (y, 0))) <> None).
  { intros k' Hk''. apply H2. lia. }
  unfold splice.
  rewrite (mm2_iter_app_l (List.map (shift_instr (length Pre)) M) Hk').
  assert (Hne := H2 k Hk).
  destruct (mm2_step_fun Pre (mm2_iter Pre k (1, (y, 0))))
    as [s' |] eqn:Es; [| congruence].
  assert (Hrange := mm2_step_fun_some_range Es).
  rewrite (mm2_step_fun_app_l_state (List.map (shift_instr (length Pre)) M)
             (proj1 Hrange) (proj2 Hrange)).
  rewrite Es. congruence.
Qed.

Theorem specialize_correct (Pre : list mm2_instr) (f : nat -> nat)
  (Hspec : forall y, clos_refl_trans _ (mm2_step Pre) (1, (y, 0))
                        (1 + length Pre, (f y, 0)))
  (c y v : nat) :
  (exists n, mm2_outcome_at c (f y) n = Some v)
  <-> (exists n, mm2_outcome_at (specialize Pre c) y n = Some v).
Proof.
destruct (splice_prefix_reaches Hspec y (progOf c)) as [k0 [Hk0 Hnh]].
split.
- intros [n Hn]. exists (k0 + n).
  unfold mm2_outcome_at, mm2_haltedAt in *.
  rewrite progOf_specialize. unfold specialize_prog.
  rewrite mm2_iter_add, Hk0, mm2_iter_shift, mm2_step_fun_shift, shift_state_eqb_zero.
  destruct (mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1, (f y, 0))))
    as [s' |] eqn:E; simpl; exact Hn.
- intros [n2 Hn2].
  unfold mm2_outcome_at, mm2_haltedAt in Hn2.
  rewrite progOf_specialize in Hn2. unfold specialize_prog in Hn2.
  assert (Hge : k0 <= n2).
  { destruct (Compare_dec.le_lt_dec k0 n2) as [Hle | Hlt]; [exact Hle |].
    exfalso.
    assert (Hne := Hnh n2 Hlt).
    destruct (mm2_step_fun (splice Pre (progOf c))
                (mm2_iter (splice Pre (progOf c)) n2 (1, (y, 0))))
      as [s' |] eqn:E.
    - simpl in Hn2. discriminate.
    - congruence. }
  exists (n2 - k0).
  assert (Hn2' : n2 = k0 + (n2 - k0)) by lia.
  rewrite Hn2' in Hn2.
  unfold mm2_outcome_at, mm2_haltedAt in *.
  rewrite mm2_iter_add, Hk0, mm2_iter_shift, mm2_step_fun_shift, shift_state_eqb_zero
    in Hn2.
  destruct (mm2_step_fun (progOf c)
              (mm2_iter (progOf c) (n2 - k0) (1, (f y, 0))))
    as [s' |] eqn:E; simpl in Hn2 |- *; exact Hn2.
Qed.
