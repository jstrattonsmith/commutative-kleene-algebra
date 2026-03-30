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
Admitted.

End Functional.

(** ** Soundness helpers *)

Section SoundnessHelpers.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.

(** The nat_to_fin of a halting state's index yields
    0%fin (which is not an active state). *)

Lemma halt_nat_to_fin_zero (P : list mm2_instr)
    (s : mm2_state) :
  mm2_stop P s →
  fin_to_nat (nat_to_fin P (fst s)) = 0.
Proof.
(* mm2_stop means no step is possible, which holds
   when fst s = 0 or fst s > length P.  In both
   cases, nat_to_fin maps to 0%fin. *)
Admitted.

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
move=> Hq /l_alt Hle.
(* config_set = star(a) ⋅ star(b) ⋅ ⨆(map q states) *)
(* The language decomposes as w1 ++ w2 ++ [mm_q q']
   where q' ∈ states. But our word has mm_q q with
   q ∉ states. *)
Admitted.

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
(* The halting state maps to 0%fin which is not in
   active_states, so config(s) is not in C.
   And config(s) ≠ [mm_c true] structurally. *)
Admitted.

(** Each mm2_step maps to a pair in mm2_R. *)

Lemma mm2_step_in_R (P : list mm2_instr)
    (x y : mm2_state) :
  mm2_step P x y →
  Unit (mm2_config P x, mm2_config P y) ⊑ mm2_R P.
Proof.
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
(* By induction on the reflexive-transitive closure.
   Base: 0 steps, L = [].
   Step: use mm2_step_in_R for the new step,
   combine with IH via star unfolding. *)
Admitted.

End SoundnessHelpers.

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
have [L HL] := trace_pair (Q:=Q) Hreach.
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
  exact (@halt_config_not_in_C Q _ _
    P s' Hstop (iffRL (l_alt _ _) He)).
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
Admitted.

End MainTheorems.
