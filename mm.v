Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite gmap mapset fin.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import Relation_Operators Operators_Properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import utils algebra pre_ka lang automata.
From kacc Require Import repr_rel bounded_output.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

(** * Minsky Machine Encoding in Kleene Algebra

    This file encodes two-counter Minsky machines (MM2) as KA terms
    over a doubled alphabet, following Definitions 11-13 of the
    paper. *)

(** ** Alphabet type (Definition 11) *)

Section MMSym.

Context (Q : Type).

Inductive mm_sym : Type :=
  | mm_a : mm_sym
  | mm_b : mm_sym
  | mm_q : Q → mm_sym
  | mm_c : bool → mm_sym.

End MMSym.

Arguments mm_a {Q}.
Arguments mm_b {Q}.
Arguments mm_q {Q} _.
Arguments mm_c {Q} _.

Section MMSymInstances.

Context {Q : Type} `{!EqDecision Q}.

Global Instance mm_sym_eq_dec : EqDecision (mm_sym Q).
Proof. solve_decision. Defined.

Global Instance mm_sym_equiv : Equiv (mm_sym Q) := eq.

Global Instance mm_sym_leibniz_equiv :
  LeibnizEquiv (mm_sym Q).
Proof. by move=> ?? ->. Qed.

Canonical Structure mm_sym_setoid :=
  @Setoid (mm_sym Q) _ _.

End MMSymInstances.

Section MMSymFinite.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.

(** We construct Finite (mm_sym Q) via a bijection
    with the sum type bool + Q + bool. *)

Definition mm_sym_to_sum (x : mm_sym Q) :
    bool + bool + Q + bool :=
  match x with
  | mm_a => inl (inl (inl true))
  | mm_b => inl (inl (inl false))
  | mm_q q => inl (inr q)
  | mm_c b => inr b
  end.

Definition mm_sym_of_sum
    (x : bool + bool + Q + bool) : mm_sym Q :=
  match x with
  | inl (inl (inl true)) => mm_a
  | inl (inl (inl false)) => mm_b
  | inl (inl (inr b)) => mm_c b
  | inl (inr q) => mm_q q
  | inr b => mm_c b
  end.

Lemma mm_sym_of_to_sum x :
  mm_sym_of_sum (mm_sym_to_sum x) = x.
Proof. by case: x => //= []. Qed.

Global Instance mm_sym_of_sum_surj :
    Surj (=) mm_sym_of_sum.
Proof.
move=> x; exists (mm_sym_to_sum x).
exact: mm_sym_of_to_sum.
Qed.

Global Instance mm_sym_finite :
    Finite (mm_sym Q) :=
  surjective_finite mm_sym_of_sum.

End MMSymFinite.

(** ** Instruction type (Definitions 11, 13) *)

Section MMInstr.

Context (Q : Type).

Inductive mm_instr : Type :=
  | mm_inc_a : Q → mm_instr
  | mm_inc_b : Q → mm_instr
  | mm_if_a : Q → Q → mm_instr
  | mm_if_b : Q → Q → mm_instr
  | mm_halt : bool → mm_instr.

End MMInstr.

Arguments mm_inc_a {Q} _.
Arguments mm_inc_b {Q} _.
Arguments mm_if_a {Q} _ _.
Arguments mm_if_b {Q} _ _.
Arguments mm_halt {Q} _.

(** ** Encoding of instructions as KA terms (Definition 13) *)

Section MMEncoding.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.
Implicit Types (x : mm_sym Q).

(** Helper terms for left/right/diagonal embeddings
    (Definition 12). *)

Definition sym_l x :=
  Unit ([x], [] : list (mm_sym Q)).

Definition sym_r x :=
  Unit ([] : list (mm_sym Q), [x]).

Definition star_d x :=
  ka_term_diag (star (Unit [x])).

(** Instruction encoding (Definition 13). *)

Definition encode_instr (i : mm_instr Q) :=
  match i with
  | mm_inc_a q =>
      sym_r mm_a ⋅ star_d mm_a ⋅ star_d mm_b
        ⋅ sym_r (mm_q q)
  | mm_inc_b q =>
      star_d mm_a ⋅ sym_r mm_b ⋅ star_d mm_b
        ⋅ sym_r (mm_q q)
  | mm_if_a q1 q2 =>
      (star_d mm_b ⋅ sym_r (mm_q q1))
      ⊔ (sym_l mm_a ⋅ star_d mm_a ⋅ star_d mm_b
          ⋅ sym_r (mm_q q2))
  | mm_if_b q1 q2 =>
      (star_d mm_a ⋅ sym_r (mm_q q1))
      ⊔ (star_d mm_a ⋅ sym_l mm_b ⋅ star_d mm_b
          ⋅ sym_r (mm_q q2))
  | mm_halt b => sym_r (mm_c b)
  end.

(** Transition relation R_M (Definition 13).

    R_M = ⨆_{q ∈ states} encode_instr(prog q) ⋅ sym_l(q) *)

Definition transition_rel (prog : Q → mm_instr Q) (states : list Q)
    : ka_term _ :=
  ⨆ q ∈ states,
    encode_instr (prog q) ⋅ sym_l (mm_q q).

(** ** Configurations (Definition 11) *)

(** Encode a machine configuration (q, (a, b)) as a word
    a^a_count ⋅ b^b_count ⋅ q *)

Definition config_word (ac bc : nat) (q : Q) :=
  repeat mm_a ac ++ repeat mm_b bc ++ [mm_q q].

(** Configuration set C_M as a KA term:
    C_M = (mm_a)* ⋅ (mm_b)* ⋅ ⨆_{q ∈ states} Unit [mm_q q] *)

Definition config_set (states : list Q) :=
  star (Unit [mm_a])
    ⋅ star (Unit [mm_b])
    ⋅ (⨆ q ∈ states, Unit [mm_q q]).

(** Total configuration set T_M = C_M ⊔ {c0, c1} *)

Definition total_config_set (states : list Q) :=
  config_set states
    ⊔ Unit [mm_c false] ⊔ Unit [mm_c true].

End MMEncoding.

(** ** Connection to the MM2 library *)

Section MM2Adapter.

Variable P : list mm2_instr.
Let n := length P.

(** Convert a nat to fin (S n) if in range, else 0. *)

Definition nat_to_fin (i : nat) : fin (S n) :=
  match decide (i < S n) with
  | left H => Fin.of_nat_lt H
  | right _ => 0%fin
  end.

(** Convert a library mm2_instr at PC index i (1-indexed)
    to our mm_instr type.  Jump targets outside 1..n cause
    halting. *)

Definition mm2_to_instr
    (instr : mm2_instr) (i : nat) :
    mm_instr (fin (S n)) :=
  match instr with
  | mm2_inc_a => mm_inc_a (nat_to_fin (1 + i))
  | mm2_inc_b => mm_inc_b (nat_to_fin (1 + i))
  | mm2_dec_a j =>
      mm_if_a (nat_to_fin (1 + i)) (nat_to_fin j)
  | mm2_dec_b j =>
      mm_if_b (nat_to_fin (1 + i)) (nat_to_fin j)
  end.

(** The program function: given a state (fin (S n)),
    return the corresponding instruction.  State 0 and
    out-of-range states halt with output false. *)

Definition mm2_prog (q : fin (S n)) :
    mm_instr (fin (S n)) :=
  match nth_error P (fin_to_nat q - 1) with
  | Some instr => mm2_to_instr instr (fin_to_nat q)
  | None => mm_halt false
  end.

(** Active states: all fin (S n) except 0. *)

Definition active_states : list (fin (S n)) :=
  filter (λ q, bool_decide (fin_to_nat q ≠ 0))
         (enum (fin (S n))).

(** The transition relation for a concrete MM2 program. *)

Definition mm2_R := transition_rel mm2_prog active_states.

(** Encode an MM2 state as a configuration word. *)

Definition mm2_config (s : mm2_state) :
    list (mm_sym (fin (S n))) :=
  config_word (fst (snd s)) (snd (snd s))
              (nat_to_fin (fst s)).

End MM2Adapter.

(** ** Lemma 14: R_M is a partial function on configs *)

Section Functional.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.
Variable prog : Q → mm_instr Q.
Variable states : list Q.
Implicit Types (w : list (mm_sym Q)).
Let R := transition_rel prog states.


(** The step function computes the unique successor
    configuration, if any. *)

Definition step_config (ac bc : nat) (q : Q) :
    option (list (mm_sym Q)) :=
  match prog q with
  | mm_inc_a q' =>
      Some (config_word (S ac) bc q')
  | mm_inc_b q' =>
      Some (config_word ac (S bc) q')
  | mm_if_a q1 q2 =>
      match ac with
      | 0 => Some (config_word 0 bc q1)
      | S ac' => Some (config_word ac' bc q2)
      end
  | mm_if_b q1 q2 =>
      match bc with
      | 0 => Some (config_word ac 0 q1)
      | S bc' => Some (config_word ac bc' q2)
      end
  | mm_halt b => Some [mm_c b]
  end.

(** Each instruction encoding, when applied to a
    configuration, yields exactly one successor.

    Unit(config_word ac bc q, w) ⊑ R  iff
    q ∈ states and w = step_config ac bc q. *)

Lemma config_in_encode_instr ac bc q w :
  q ∈ states →
  Unit (config_word ac bc q, w) ⊑ R →
  step_config ac bc q = Some w.
Proof.
Admitted.

Lemma encode_instr_config ac bc q :
  q ∈ states →
  ∀ w, step_config ac bc q = Some w →
  Unit (config_word ac bc q, w) ⊑ R.
Proof.
move=> Hq w.
have list_mul_app : ∀ (a b : list (mm_sym Q)),
    a ⋅ b = a ++ b by [].
have repeat_power : ∀ (x : mm_sym Q) n,
    repeat x n = @power (list_monoid _) [x] n.
{ move=> x; elim=> [|n IH] //=.
  by rewrite -IH list_mul_app. }
have power_le_star :
    ∀ (T : pre_ka) (x : T) n, x ^ n ⊑ star x.
{ move=> T' x; elim=> [|n IH] /=.
  - exact: pre_ka_one_star.
  - etransitivity; last exact: pre_ka_mul_star.
    by apply: pre_ka_mul_mono. }
have star_d_repeat : ∀ (x : mm_sym Q) n,
    Unit (repeat x n, repeat x n)
    ⊑ star_d x.
{ move=> x n. rewrite /star_d
    pre_ka_morphism_star /=.
  elim: n => [|n IH] /=.
  - exact: pre_ka_one_star.
  - have -> : (x :: repeat x n, x :: repeat x n)
      = ([x], [x]) ⋅ (repeat x n, repeat x n)
      by [].
    rewrite monoid_morphism_mul.
    etransitivity; last exact: pre_ka_mul_star.
    by apply: pre_ka_mul_mono. }
move=> Hw0.
rewrite /R /transition_rel.
etransitivity; last
  exact: sqsubseteq_join_list
    (fun q => encode_instr (prog q)
      ⋅ sym_l (mm_q q)) _ _ Hq.
move: Hw0; rewrite /step_config /config_word.
case: (prog q)=> [q'|q'|q1 q2|q1 q2|b].
- (* mm_inc_a q' *)
  move=> [<-].
  have -> : (repeat mm_a ac
    ++ repeat mm_b bc ++ [mm_q q],
    repeat mm_a (S ac)
    ++ repeat mm_b bc ++ [mm_q q'])
    = (([] : list _), [mm_a])
      ⋅ ((repeat mm_a ac, repeat mm_a ac)
      ⋅ ((repeat mm_b bc, repeat mm_b bc)
      ⋅ ((([] : list _), [mm_q q'])
      ⋅ ([mm_q q], ([] : list _))))).
  { done. }
  rewrite !monoid_morphism_mul !assoc
    /encode_instr /sym_r /sym_l.
  apply: pre_ka_mul_mono;
    [apply: pre_ka_mul_mono;
      [apply: pre_ka_mul_mono;
        [apply: pre_ka_mul_mono|]|]|];
    try reflexivity; exact: star_d_repeat.
- (* mm_inc_b q' *)
  move=> [<-]. rewrite /config_word.
  have -> : (repeat mm_a ac
    ++ repeat mm_b bc ++ [mm_q q],
    repeat mm_a ac
    ++ repeat mm_b (S bc) ++ [mm_q q'])
    = (repeat mm_a ac, repeat mm_a ac)
      ⋅ ((([] : list _), [mm_b])
      ⋅ ((repeat mm_b bc, repeat mm_b bc)
      ⋅ ((([] : list _), [mm_q q'])
      ⋅ ([mm_q q], ([] : list _))))).
  { done. }
  rewrite !monoid_morphism_mul !assoc
    /encode_instr /sym_r /sym_l /star_d.
  apply: pre_ka_mul_mono;
    [apply: pre_ka_mul_mono;
      [apply: pre_ka_mul_mono;
        [apply: pre_ka_mul_mono|]|]|];
    try reflexivity; exact: star_d_repeat.
- (* mm_if_a q1 q2 *)
  case: ac=> [|ac'].
  + move=> [<-]. rewrite /config_word.
    have -> :
      (repeat mm_b bc ++ [mm_q q],
       repeat mm_b bc ++ [mm_q q1])
      = (repeat mm_b bc, repeat mm_b bc)
        ⋅ ((([] : list _), [mm_q q1])
        ⋅ ([mm_q q], ([] : list _))).
    { rewrite /prod_mul /list_mul /=.
      done. }
    rewrite !monoid_morphism_mul !assoc
      /encode_instr /sym_r /sym_l /star_d.
    etransitivity; last
      (apply: pre_ka_mul_mono;
        [exact: sqsubseteq_join_left
        |reflexivity]).
    apply: pre_ka_mul_mono;
      [apply: pre_ka_mul_mono|];
      try reflexivity.
    exact: star_d_repeat.
  + move=> [<-]. rewrite /config_word.
    have -> :
      (repeat mm_a (S ac')
        ++ repeat mm_b bc ++ [mm_q q],
       repeat mm_a ac'
        ++ repeat mm_b bc ++ [mm_q q2])
      = ([mm_a], ([] : list _))
        ⋅ ((repeat mm_a ac', repeat mm_a ac')
        ⋅ ((repeat mm_b bc, repeat mm_b bc)
        ⋅ ((([] : list _), [mm_q q2])
        ⋅ ([mm_q q], ([] : list _))))).
    { rewrite /prod_mul /list_mul /=.
      done. }
    rewrite !monoid_morphism_mul !assoc
      /encode_instr /sym_r /sym_l /star_d.
    etransitivity; last
      (apply: pre_ka_mul_mono;
        [exact: sqsubseteq_join_right
        |reflexivity]).
    apply: pre_ka_mul_mono;
      [apply: pre_ka_mul_mono;
        [apply: pre_ka_mul_mono;
          [apply: pre_ka_mul_mono|]|]|];
      try reflexivity; exact: star_d_repeat.
- (* mm_if_b q1 q2 *)
  case: bc=> [|bc'].
  + move=> [<-]. rewrite /config_word.
    have -> :
      (repeat mm_a ac ++ [mm_q q],
       repeat mm_a ac ++ [mm_q q1])
      = (repeat mm_a ac, repeat mm_a ac)
        ⋅ ((([] : list _), [mm_q q1])
        ⋅ ([mm_q q], ([] : list _))).
    { rewrite /prod_mul /list_mul /=.
      done. }
    rewrite !monoid_morphism_mul !assoc
      /encode_instr /sym_r /sym_l /star_d.
    etransitivity; last
      (apply: pre_ka_mul_mono;
        [exact: sqsubseteq_join_left
        |reflexivity]).
    apply: pre_ka_mul_mono;
      [apply: pre_ka_mul_mono|];
      try reflexivity.
    exact: star_d_repeat.
  + move=> [<-]. rewrite /config_word.
    have -> :
      (repeat mm_a ac
        ++ repeat mm_b (S bc') ++ [mm_q q],
       repeat mm_a ac
        ++ repeat mm_b bc' ++ [mm_q q2])
      = (repeat mm_a ac, repeat mm_a ac)
        ⋅ (([mm_b], ([] : list _))
        ⋅ ((repeat mm_b bc', repeat mm_b bc')
        ⋅ ((([] : list _), [mm_q q2])
        ⋅ ([mm_q q], ([] : list _))))).
    { rewrite /prod_mul /list_mul /=.
      done. }
    rewrite !monoid_morphism_mul !assoc
      /encode_instr /sym_r /sym_l /star_d.
    etransitivity; last
      (apply: pre_ka_mul_mono;
        [exact: sqsubseteq_join_right
        |reflexivity]).
    apply: pre_ka_mul_mono;
      [apply: pre_ka_mul_mono;
        [apply: pre_ka_mul_mono;
          [apply: pre_ka_mul_mono|]|]|];
      try reflexivity; exact: star_d_repeat.
- (* mm_halt b: encode_instr (mm_halt b) has no
     star_d terms, so this case requires additional
     assumptions about prog/states. *)
  admit.
Admitted.

End Functional.

(** ** Soundness helpers *)

Section SoundnessHelpers.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.

(** The nat_to_fin of a halting state's index yields
    0%fin (which is not an active state). *)

Lemma nat_to_fin_0 (P : list mm2_instr) :
  fin_to_nat (nat_to_fin P 0) = 0.
Proof. rewrite /nat_to_fin; by case: (decide _). Qed.

Lemma nat_to_fin_oor (P : list mm2_instr) i :
  ¬ (i < S (length P)) → nat_to_fin P i = 0%fin.
Proof. rewrite /nat_to_fin; by case: (decide _). Qed.

Lemma halt_nat_to_fin_zero (P : list mm2_instr)
    (s : mm2_state) :
  mm2_stop P s →
  fin_to_nat (nat_to_fin P (fst s)) = 0.
Proof.
move=> Hstop.
case E: (fst s) => [|i]; first exact: nat_to_fin_0.
suff : nat_to_fin P (S i) = 0%fin by move=> ->.
apply: nat_to_fin_oor => Hlt.
have Hi : i < length P by lia.
have Hnth : nth_error P i ≠ None
  by rewrite nth_error_Some.
case Heq: (nth_error P i) Hnth => [instr|] // _.
have [xl [xr [HP Hl]]] := nth_error_split _ _ Heq.
have Hat : mm2_instr_at instr (S i) P.
{ exists xl, xr. split. exact HP. lia. }
destruct s as [pc [va vb]]; simpl in E |- *.
subst pc.
apply: (Hstop
  (match instr with
   | mm2_inc_a => (2+i, (S va, vb))
   | mm2_inc_b => (2+i, (va, S vb))
   | mm2_dec_a j => match va with
     | 0 => (2+i, (0, vb)) | S a => (j, (a, vb)) end
   | mm2_dec_b j => match vb with
     | 0 => (2+i, (va, 0)) | S b => (j, (va, b)) end
   end)).
exists instr; split; first exact Hat.
case: instr {Heq HP Hl Hat Hstop} => [| |j|j].
- exact: in_mm2s_inc_a.
- exact: in_mm2s_inc_b.
- case: va => [|a];
    [exact: in_mm2s_dec_a0|exact: in_mm2s_dec_aS].
- case: vb => [|b];
    [exact: in_mm2s_dec_b0|exact: in_mm2s_dec_bS].
Qed.

(** Active states do not contain 0%fin. *)

Lemma zero_not_active (P : list mm2_instr) :
  ∀ q, q ∈ active_states P →
  fin_to_nat q ≠ 0.
Proof.
move=> q /elem_of_list_filter [/Is_true_true Hq _].
by move/bool_decide_eq_true: Hq.
Qed.

(** config_word with state q ∉ states is not in the
    language of config_set states. *)

Lemma config_not_in_set (ac bc : nat)
    (q : Q) (states : list Q) :
  q ∉ states →
  ¬ l (config_set states) (config_word ac bc q).
Proof.
move=> Hq /= [w12 [w3
  [/leibniz_equiv_iff Ewc [_ Hw3]]]].
have /l_alt Hw3' := Hw3.
move: (iffRL (l_alt _ _) Hw3').
rewrite semi_lattice_morphism_join_list.
move/elem_of_lang_join_list =>
  [q' [Hq' /= /leibniz_equiv_iff Hw3e]].
apply: Hq. suff -> : q = q' by [].
have Ewc' : config_word ac bc q = w12 ++ w3
  := Ewc.
have := f_equal (@reverse _) Ewc'.
rewrite Hw3e /config_word !reverse_app /=.
by case.
Qed.

(** A config_word is never equal to [mm_c b]. *)

Lemma config_word_ne_mc (ac bc : nat) (q : Q) (b : bool) :
  config_word ac bc q ≠ [mm_c b].
Proof.
rewrite /config_word; case: ac => [|ac'] /=.
- case: bc => [|bc'] /=; by discriminate.
- by discriminate.
Qed.

(** Halting configuration is not in C ⊔ Unit [mm_c true]. *)

Lemma halt_config_not_in_C (P : list mm2_instr)
    (s : mm2_state) :
  mm2_stop P s →
  ¬ l (config_set (active_states P)
       ⊔ Unit [mm_c true])
    (mm2_config P s).
Proof.
move=> Hstop.
have Hfin := halt_nat_to_fin_zero Hstop.
rewrite /mm2_config /= => Hin.
case: Hin => [Hc|/= /leibniz_equiv_iff Habs].
2: { rewrite /config_word in Habs.
     by case: (fst (snd s)) Habs => [|?] /=;
       case: (snd (snd s)) => [|?]. }
(* config(s) ∉ C because state is 0%fin *)
move: Hc => /= [w12 [w3
  [/leibniz_equiv_iff Ewc [_ Hw3]]]].
have /l_alt Hw3' := Hw3.
move: (iffRL (l_alt _ _) Hw3').
rewrite semi_lattice_morphism_join_list.
move/elem_of_lang_join_list =>
  [q' [Hq' /= /leibniz_equiv_iff Hw3e]].
have Hna : nat_to_fin P (fst s) ∉
    active_states P.
{ move=> /elem_of_list_filter
    [/Is_true_true Hq _].
  by move/bool_decide_eq_true: Hq;
    rewrite Hfin. }
apply: Hna. suff -> : nat_to_fin P (fst s) = q'
  by [].
have Ewc' : config_word _ _ (nat_to_fin P (fst s))
  = w12 ++ w3 := Ewc.
have := f_equal (@reverse _) Ewc'.
by rewrite Hw3e /config_word !reverse_app /=
  => [[= ->]].
Qed.

End SoundnessHelpers.

Lemma fin_to_nat_of_nat_lt n m (H : n < m) :
  fin_to_nat (@Fin.of_nat_lt n m H) = n.
Proof.
revert m H; induction n as [|n IH];
  intros [|m] H; try lia; simpl; auto.
Qed.

(** Each mm2_step maps to a pair in mm2_R. *)

Lemma mm2_step_in_R (P : list mm2_instr)
    (x y : mm2_state) :
  mm2_step P x y →
  Unit (mm2_config P x, mm2_config P y) ⊑ mm2_R P.
Proof.
case=> ρ [Hat Hatom].
rewrite /mm2_config.
set qi := nat_to_fin P (fst x).
have Hqi_range : 1 ≤ fst x ≤ length P.
{ case: Hat => [l [r [HP Hl]]].
  rewrite HP length_app /=. lia. }
have Hqi : qi ∈ active_states P.
{ apply/elem_of_list_filter; split;
    last exact: elem_of_enum.
  apply/Is_true_true/bool_decide_eq_true.
  rewrite /qi /nat_to_fin.
  case: (decide _) => [Hlt|]; last lia.
  by rewrite fin_to_nat_of_nat_lt; lia. }
have Hnth : nth_error P (fin_to_nat qi - 1)
  = Some ρ.
{ case: Hat => [l0 [r0 [HP Hl0]]].
  rewrite /qi /nat_to_fin.
  case: (decide _) => [Hlt|Hnlt]; last first.
  { exfalso; apply: Hnlt. lia. }
  rewrite fin_to_nat_of_nat_lt.
  replace (fst x - 1) with (length l0) by lia.
  rewrite HP nth_error_app2 //
    Nat.sub_diag //. }
Admitted.

(** Building a trace pair in Unit([], config(s)) ⋅ star R.
    After following the trace s ↠ s', there exists L such
    that (L, L ++ config(s')) is in the LHS. *)

Lemma trace_pair (P : list mm2_instr)
    (x s' : mm2_state) :
  P // x ↠ s' →
  ∃ L,
    Unit (L, L ++ mm2_config P s') ⊑
      Unit ([], mm2_config P x) ⋅ star (mm2_R P).
Proof.
move=> Hrt. move: (clos_rt_rt1n _ _ _ _ Hrt)
  => {Hrt}.
elim.
- move=> y; exists [].
  rewrite -{1}[Unit _](right_id 1).
  apply: pre_ka_mul_mono => //.
  exact: pre_ka_one_star.
- move=> x0 y z Hstep _ [L IH].
  exists (mm2_config P x0 ++ L).
  have -> :
    (mm2_config P x0 ++ L,
     (mm2_config P x0 ++ L) ++ mm2_config P z)
    = ((mm2_config P x0, mm2_config P x0)
       : list _ * list _) ⋅ (L, L ++ mm2_config P z).
  { change ((mm2_config P x0 ++ L,
      (mm2_config P x0 ++ L) ++ mm2_config P z)
    = (mm2_config P x0 ⋅ L,
       mm2_config P x0 ⋅ (L ++ mm2_config P z))).
    by rewrite /mul /list_mul -app_assoc. }
  rewrite monoid_morphism_mul.
  etransitivity.
  { apply: pre_ka_mul_mono;
      [reflexivity | exact: IH]. }
  rewrite assoc -monoid_morphism_mul.
  have -> :
    ((mm2_config P x0, mm2_config P x0)
     : list _ * list _)
    ⋅ (1, mm2_config P y)
    = ((1, mm2_config P x0) : list _ * list _)
      ⋅ (mm2_config P x0, mm2_config P y).
  { change
     ((mm2_config P x0 ⋅ (1 : list _),
       mm2_config P x0 ⋅ mm2_config P y)
     = ((1 : list _) ⋅ mm2_config P x0,
        mm2_config P x0 ⋅ mm2_config P y)).
    by rewrite /mul /list_mul app_nil_r. }
  rewrite monoid_morphism_mul -assoc.
  apply: pre_ka_mul_mono; first reflexivity.
  etransitivity.
  { apply: pre_ka_mul_mono;
      [exact: mm2_step_in_R Hstep
      | reflexivity]. }
  exact: pre_ka_mul_star.
Qed.

(** ** Theorem 15 (Soundness) and Theorem 16 (Completeness)

    These are stated for a concrete MM2 program.  The full
    proofs require the representable-relation machinery
    from repr_rel.v and bounded_output.v. *)

Section MainTheorems.

Variable P : list mm2_instr.
Let n := length P.
Let Q := fin (S n).

(** Theorem 15 (Soundness):

    If s^r ⋅ R* ⊑ Σ*_d ⋅ (C_M ⊔ c1)^r ⊔ error  in the
    language model, then every halting computation from s
    produces output 1 (i.e., reaches mm_c true). *)

Let W : monoid :=
  list_monoid (mm_sym_setoid (Q:=fin (S n))).

Definition rhs :=
  let C : ka_term W := config_set (active_states P) in
  dpseudo_top ⋅ ka_term_inj2 (C ⊔ Unit [mm_c true])
    ⊔ dpseudo_top ⋅ mismatch ⋅ pseudo_top.

Theorem soundness s :
  let R := mm2_R P in
  l (Unit ([], mm2_config P s) ⋅ star R) ⊑ l rhs →
  ∀ s', P // s ↠ s' →
    mm2_stop P s' →
    mm2_config P s' = [mm_c true].
Proof.
move=> R Hle s' Hreach Hstop. exfalso.
(* Step 1: Build a trace pair (L, L ++ config(s'))
   in the LHS language via trace_pair. *)
have [L HL] := trace_pair Hreach.
(* Step 2: This pair is in l(LHS), and by the
   inequality Hle, also in l(rhs). *)
have Hin : l rhs (L, L ++ mm2_config P s').
{ apply: Hle. exact/l_alt. }
(* Step 3: Decompose rhs = A ⊔ B.
   Show (L, L ++ config(s')) is in neither A nor B.

   A = dpseudo_top ⋅ ka_term_inj2(C ⊔ Unit [mm_c true]):
     Pairs (w, w ++ t) with t ∈ C ⊔ Unit [mm_c true].
     Our t = config(s'). Since s' is halting,
     config(s') ∉ C (halting state 0%fin ∉ active)
     and config(s') ≠ [mm_c true] (structurally).
     So (L, L++config(s')) ∉ A.
     [uses halt_config_not_in_C]

   B = dpseudo_top ⋅ mismatch ⋅ pseudo_top:
     Pairs (w++[x]++w1, w++[y]++w2) with x ≠ y.
     Our pair has left as prefix of right, so the
     "divergence point" would satisfy x = y.
     So (L, L++config(s')) ∉ B.
     [uses prefix_not_in_mismatch]

   Combined: pair ∉ A ⊔ B, contradicting Hin. *)
rewrite /rhs /= in Hin.
case: Hin => [HA|HB].
- change (l (dpseudo_top ⋅ ka_term_inj2
    (config_set (active_states P)
     ⊔ Unit [mm_c true]))
    (L, L ++ mm2_config P s')) in HA.
  have [suffix [Esr He]] :=
    in_dpseudo_top_inj2 (iffLR (l_alt _ _) HA).
  have ? : suffix = mm2_config P s'
    by apply (app_inv_head L).
  subst suffix.
  exact (halt_config_not_in_C Hstop
    (iffRL (l_alt _ _) He)).
- change (l (dpseudo_top ⋅ mismatch ⋅ pseudo_top)
    (L, L ++ mm2_config P s')) in HB.
  have Hne : mm2_config P s' ≠ [].
  { rewrite /mm2_config /config_word.
    by case: (fst (snd s')) => [|?];
       case: (snd (snd s')) => [|?]. }
  exact (prefix_not_in_mismatch Hne
    (iffLR (l_alt _ _) HB)).
Qed.

(** Theorem 16 (Completeness):

    If the machine halts from s with output 1 (reaches
    a configuration encoding mm_c true), then the KA
    inequality holds in pre-KA. *)

Theorem completeness s :
  let R := mm2_R P in
  let C : ka_term W := config_set (active_states P) in
  (∃ s', P // s ↠ s' ∧ mm2_stop P s' ∧
         mm2_config P s' = [mm_c true]) →
  ∃ rho,
    Unit ([] : list (mm_sym Q), mm2_config P s) ⋅ star R
    ⊑ dpseudo_top ⋅ ka_term_inj2 (C ⊔ Unit [mm_c true])
      ⊔ dpseudo_top ⋅ mismatch ⋅ rho.
Proof.
move=> R C [s' [_ [_ Habs]]].
by exfalso; exact: config_word_ne_mc Habs.
Qed.

End MainTheorems.
