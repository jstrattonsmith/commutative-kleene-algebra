Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import list .
From Stdlib Require Import Relations Transitive_Closure.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

Definition mm2_run_step (P : list mm2_instr) (s : mm2_state) :=
  match s.1 with
  | 0 => None
  | S _ => match nth_error P (pred s.1) with
    | Some instr => match instr, s with
      | mm2_inc_a,   (i, (  a,   b)) => Some (S i, (S a,   b))
      | mm2_inc_b,   (i, (  a,   b)) => Some (S i, (  a, S b))
      | mm2_dec_a j, (i, (S a,   b)) => Some (  j, (  a,   b))
      | mm2_dec_b j, (i, (  a, S b)) => Some (  j, (  a,   b))
      | mm2_dec_a _, (i, (  0,   b)) => Some (S i, (  0,   b))
      | mm2_dec_b _, (i, (  a,   0)) => Some (S i, (  a,   0))
      end
    | None => None
    end
  end.

Lemma nth_error_iff_instr_at P (i : nat) (ρ : mm2_instr) (Hi : i ≠ 0) :
  nth_error P (pred i) = Some ρ ↔ mm2_instr_at ρ i P.
Proof.
rewrite /mm2_instr_at. split.
- move=> HE.
  apply nth_error_split in HE as [l [r [-> Hlen]]].
  exists l, r. split; [auto | lia].
- move=> [l [r [-> Hlen]]].
  have -> : pred i = length l by lia.
  by rewrite nth_error_app2 // Nat.sub_diag.
Qed.

Lemma mm2_run_step_spec (P : list mm2_instr) (s s' : mm2_state) :
  mm2_run_step P s = Some s' ↔ mm2_step P s s'.
Proof.
rewrite /mm2_run_step /mm2_step.
split.
- destruct s as [i [a b]].
  destruct i as [| i]; first by discriminate.
  case E : (nth_error P i) => [ρ |]; last by discriminate.
  have Hat : mm2_instr_at ρ (S i) P
    by apply (nth_error_iff_instr_at P (S i) ρ); [lia | exact E].
  destruct ρ, a, b; move=> [<-];
    (eexists; split; [exact Hat | constructor]).
- move=> [ρ [Hat Hatom]].
  have Hi : s.1 ≠ 0.
  { rewrite /mm2_instr_at in Hat.
    destruct Hat as [? [? [_ ?]]]. lia. }
  destruct s.1 as [| i] eqn:Hs; first by contradiction.
  have -> : nth_error P i = Some ρ
    by apply (nth_error_iff_instr_at P (S i) ρ Hi).
  by inversion Hatom; subst.
Qed.

Fixpoint mm2_run_n_steps P s n : option mm2_state :=
  match n with
  | 0    => Some s
  | S n' => match mm2_run_step P s with
             | Some s'' => mm2_run_n_steps P s'' n'
             | None     => None
             end
  end.

Lemma mm2_run_n_steps_concat P s s'' n1 n2 :
  mm2_run_n_steps P s n1 = Some s'' →
  mm2_run_n_steps P s (n1 + n2) = mm2_run_n_steps P s'' n2.
Proof.
induction n1 as [| ??] in s |- *; simpl; first by move=> [<-].
case: (mm2_run_step P s) => //=.
Qed.

Lemma mm2_run_n_step_spec P s s' :
  (exists n, mm2_run_n_steps P s n = Some s') ↔ P // s ↠ s'.
Proof.
split.
- move=> [n].
  induction n as [| n IH] in s |- *;
  first by move=> /= [<-]; apply rt_refl.
  rewrite /=.
  case Estep: (mm2_run_step P s) => [s'' |] //= Hn.
  apply rt_trans with (y := s''); last by apply IH.
  apply rt_step. by apply mm2_run_step_spec.
- move=> Hrt. induction Hrt as [s s' Hstep | s | s smid s' Hrt1 IH1 Hrt2 IH2].
  + exists 1. simpl.
    by apply mm2_run_step_spec in Hstep as ->.
  + exists 0. reflexivity.
  + destruct IH1 as [n1 Hn1], IH2 as [n2 Hn2].
    exists (n1 + n2).
    by rewrite (mm2_run_n_steps_concat P s smid n1 n2 Hn1).
Qed.

Definition run fuel P s : option bool :=
  match mm2_run_n_steps P s fuel with
  | Some (0, _) => Some true
  | Some _      => Some false
  | None        => None
  end.