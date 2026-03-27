Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite gmap mapset fin.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

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

Let T := mm_sym Q.
Let S := eq_setoid T.
Let W := list_monoid S.
Let WW := prod_monoid W W.

Local Instance mm_sym_leibniz_equiv' :
    LeibnizEquiv S := mm_sym_leibniz_equiv.
Local Instance mm_sym_monoid_gen :
    MonoidGen T W := @list_fin_gen S.
Local Instance mm_sym_sized_monoid :
    SizedMonoid T W :=
  @list_sized_monoid S mm_sym_leibniz_equiv'.

(** Helper terms for left/right/diagonal embeddings
    (Definition 12). *)

Definition sym_l (x : T) : ka_term WW :=
  Unit ([x], ([] : list T)).

Definition sym_r (x : T) : ka_term WW :=
  Unit (([] : list T), [x]).

Definition star_d (x : T) : ka_term WW :=
  ka_term_diag (star (Unit [x] : ka_term W)).

(** Instruction encoding (Definition 13). *)

Definition encode_instr (i : mm_instr Q) : ka_term WW :=
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

Definition transition_rel
    (prog : Q → mm_instr Q) (states : list Q) :
    ka_term WW :=
  ⨆ (map (λ q, encode_instr (prog q) ⋅ sym_l (mm_q q))
         states).

(** ** Configurations (Definition 11) *)

(** Encode a machine configuration (q, (a, b)) as a word
    a^a_count ⋅ b^b_count ⋅ q *)

Definition config_word (ac bc : nat) (q : Q) : list T :=
  repeat mm_a ac ++ repeat mm_b bc ++ [mm_q q].

(** Configuration set C_M as a KA term:
    C_M = (mm_a)* ⋅ (mm_b)* ⋅ ⨆_{q ∈ states} Unit [mm_q q] *)

Definition config_set (states : list Q) : ka_term W :=
  star (Unit [mm_a] : ka_term W)
    ⋅ star (Unit [mm_b] : ka_term W)
    ⋅ ⨆ (map (λ q, Unit [mm_q q] : ka_term W) states).

(** Total configuration set T_M = C_M ⊔ {c0, c1} *)

Definition total_config_set (states : list Q) :
    ka_term W :=
  config_set states
    ⊔ Unit [mm_c false] ⊔ Unit [mm_c true].

(** The "pseudo-top" over the full alphabet Σ_M,
    lifted to the diagonal of the product. *)

Definition mm_dpseudo_top : ka_term WW :=
  ka_term_diag (@pseudo_top T W _ _ _).

(** Mismatch term: ⨆ { Unit([x],[y]) | x ≠ y }. *)

Definition mm_mismatch : ka_term WW :=
  let diffs :=
    filter (λ '(x, y), bool_decide (x ≠ y))
           (enum (T * T)) in
  ⨆ (map (λ '(x, y),
    Unit (([x], [y]) : WW)) diffs).

(** Error term: Σ*_d ⋅ mismatch ⋅ Σ* *)

Definition error_term : ka_term WW :=
  mm_dpseudo_top ⋅ mm_mismatch
    ⋅ @pseudo_top _ WW _ _ _.

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

Definition mm2_R :=
  transition_rel mm2_prog active_states.

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

Let T := mm_sym Q.
Let W := list_monoid (eq_setoid T).
Let WW := prod_monoid W W.
Let R := transition_rel prog states.

(** The step function computes the unique successor
    configuration, if any. *)

Definition step_config (ac bc : nat) (q : Q) :
    option (list T) :=
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

Lemma config_in_encode_instr ac bc q (w : W) :
  q ∈ states →
  Unit ((config_word ac bc q : W, w) : WW) ⊑ R →
  step_config ac bc q = Some w.
Proof.
Admitted.

Lemma encode_instr_config ac bc q :
  q ∈ states →
  ∀ w : W, step_config ac bc q = Some w →
  Unit ((config_word ac bc q : W, w) : WW) ⊑ R.
Proof.
Admitted.

End Functional.

(** ** Theorem 15 (Soundness) and Theorem 16 (Completeness)

    These are stated for a concrete MM2 program.  The full
    proofs require the representable-relation machinery
    from repr_rel.v and bounded_output.v. *)

Section MainTheorems.

Variable P : list mm2_instr.
Let n := length P.
Let T := mm_sym (fin (S n)).
Let S := eq_setoid T.
Let W := list_monoid S.
Let WW := prod_monoid W W.

Local Instance main_leibniz : LeibnizEquiv S :=
  mm_sym_leibniz_equiv.
Local Instance main_gen : MonoidGen T W :=
  @list_fin_gen S.
Local Instance main_sized : SizedMonoid T W :=
  @list_sized_monoid S main_leibniz.

(** Theorem 15 (Soundness):

    If s^r ⋅ R* ⊑ Σ*_d ⋅ (C_M ⊔ c1)^r ⊔ error  in the
    language model, then every halting computation from s
    produces output 1 (i.e., reaches mm_c true). *)

Theorem soundness s :
  let R := mm2_R P in
  let C := config_set (active_states P) in
  Unit (([] : W, mm2_config P s : W) : WW) ⋅ star R
    ⊑ mm_dpseudo_top
        ⋅ @ka_term_inj2 W W (C ⊔ Unit [mm_c true])
      ⊔ error_term →
  ∀ s', P // s ↠ s' →
    mm2_stop P s' →
    mm2_config P s' = [mm_c true].
Proof.
Admitted.

(** Theorem 16 (Completeness):

    If the machine halts from s with output 1 (reaches
    a configuration encoding mm_c true), then the KA
    inequality holds in pre-KA. *)

Theorem completeness s :
  let R := mm2_R P in
  let C := config_set (active_states P) in
  (∃ s', P // s ↠ s' ∧ mm2_stop P s' ∧
         mm2_config P s' = [mm_c true]) →
  ∃ rho : ka_term WW,
    Unit (([] : W, mm2_config P s : W) : WW)
      ⋅ star R
    ⊑ mm_dpseudo_top
        ⋅ @ka_term_inj2 W W
            (C ⊔ Unit [mm_c true])
      ⊔ mm_dpseudo_top ⋅ mm_mismatch ⋅ rho.
Proof.
Admitted.

End MainTheorems.
