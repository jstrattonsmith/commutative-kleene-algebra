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
  | mm_q : Q → mm_sym.

End MMSym.

Arguments mm_a {Q}.
Arguments mm_b {Q}.
Arguments mm_q {Q} _.

Section MMSymInstances.

Context {Q : Type}.

Global Instance mm_sym_eq_dec  `{!EqDecision Q} : EqDecision (mm_sym Q).
Proof. solve_decision. Defined.

Global Instance mm_sym_equiv : Equiv (mm_sym Q) := eq.

Global Instance mm_sym_leibniz_equiv :
  LeibnizEquiv (mm_sym Q).
Proof. by move=> ?? ->. Qed.

Canonical Structure mm_sym_setoid :=
  @Setoid (mm_sym Q) _ _.

Lemma mm_list_equiv_eq
    (x y : list (mm_sym Q)) :
  @equiv _ (@monoid_equiv
    (list_monoid mm_sym_setoid)) x y →
  x = y.
Proof.
rewrite /equiv /monoid_equiv /=
  /setoid_equiv /=.
move=> H. elim: H => // a b l1 l2 Hab _ ->.
by rewrite Hab.
Qed.

End MMSymInstances.

Section MMSymFinite.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.

(** We construct Finite (mm_sym Q) via a bijection
    with the sum type bool + Q + bool. *)

Definition mm_sym_to_sum (x : mm_sym Q) : bool + Q :=
  match x with
  | mm_a => inl true
  | mm_b => inl false
  | mm_q q => inr q
  end.

Definition mm_sym_of_sum (x : bool + Q) : mm_sym Q :=
  match x with
  | inl true => mm_a
  | inl false => mm_b
  | inr q => mm_q q
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
  | mm_inc_a : mm_instr
  | mm_inc_b : mm_instr
  | mm_dec_a : Q → mm_instr
  | mm_dec_b : Q → mm_instr.

End MMInstr.

Arguments mm_inc_a {Q}.
Arguments mm_inc_b {Q}.
Arguments mm_dec_a {Q} _.
Arguments mm_dec_b {Q} _.

(** ** Encoding of instructions as KA terms (Definition 13) *)

Section MMEncoding.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.
Implicit Types (q : Q) (x : mm_sym Q).
Variable next : Q → Q.

(** Helper terms for left/right/diagonal embeddings
    (Definition 12). *)

Definition sym_l x :=
  Unit ([x], [] : list (mm_sym Q)).

Definition sym_r x :=
  Unit ([] : list (mm_sym Q), [x]).

Definition star_d x :=
  star (Unit ([x], [x])).

(** Instruction encoding (Definition 13). *)

Definition encode_instr q (i : mm_instr Q) :=
  match i with
  | mm_inc_a =>
      sym_r mm_a ⋅ star_d mm_a ⋅ star_d mm_b ⋅
      sym_l (mm_q q) ⋅ sym_r (mm_q (next q))
  | mm_inc_b =>
      star_d mm_a ⋅ sym_r mm_b ⋅ star_d mm_b ⋅
      sym_l (mm_q q) ⋅ sym_r (mm_q (next q))
  | mm_dec_a q' =>
      (star_d mm_b ⋅ sym_l (mm_q q) ⋅ sym_r (mm_q (next q)))
      ⊔ (sym_l mm_a ⋅ star_d mm_a ⋅ star_d mm_b ⋅
         sym_l (mm_q q) ⋅ sym_r (mm_q q'))
  | mm_dec_b q' =>
      (star_d mm_a ⋅ sym_l (mm_q q) ⋅ sym_r (mm_q (next q)))
      ⊔ (star_d mm_a ⋅ sym_l mm_b ⋅ star_d mm_b ⋅
         sym_l (mm_q q) ⋅ sym_r (mm_q q'))
  end.

(** Transition relation R_M (Definition 13).

    R_M = ⨆_{q ∈ states} encode_instr(prog q) ⋅ sym_l(q) *)

Definition transition_rel (prog : Q → mm_instr Q) (states : list Q)
    : ka_term (list (mm_sym Q) * list (mm_sym Q)) :=
  ⨆ q ∈ states, encode_instr q (prog q).

(** ** Configurations (Definition 11) *)

(** Encode a machine configuration (q, (a, b)) as a word
    a^a_count ⋅ b^b_count ⋅ q *)

Definition config_word (ac bc : nat) (q : Q) :=
  repeat mm_a ac ++ repeat mm_b bc ++ [mm_q q].

(** Configuration set C_M as a KA term:
    C_{M,S} = (mm_a)* ⋅ (mm_b)* ⋅ ⨆_{q ∈ S} Unit [mm_q q] *)

Definition config_set (S : list Q) :=
  star (Unit [mm_a]) ⋅ star (Unit [mm_b]) ⋅ ⨆ q ∈ S, Unit [mm_q q].

End MMEncoding.

(** ** Connection to the MM2 library *)

Section Fin.

(** Convert a nat to fin (S n) if in range, else 0. *)

Fixpoint nat_to_fin {m} (i : nat) : option (fin m) :=
  match m with
  | 0 => None
  | S m => match i with
           | 0 => Some Fin.F1
           | S i => Fin.FS <$> @nat_to_fin m i
           end
  end.

Lemma nat_to_finK {m} (i : nat) (n : fin m) :
  nat_to_fin i = Some n → fin_to_nat n = i.
Proof.
elim: m => //= m IH in n i *; case: i => [[<-]|] // i.
case e: (nat_to_fin i) =>  [n'|] //= [<-] /=; congr S.
exact: IH.
Qed.

Lemma fin_to_natK {m} (i : fin m) : nat_to_fin i = Some i.
Proof. by elim: m / i => //= m i ->. Qed.

Lemma nat_to_fin_ge {m} (i : nat) : m ≤ i → @nat_to_fin m i = None.
Proof.
elim: m i => [|m IH] //= [|i] m_i; first lia.
by rewrite IH //; lia.
Qed.

Lemma nat_to_fin_lt m i :
  i < m → ∃ fi : fin m, nat_to_fin i = Some fi.
Proof.
elim: m i => [|m IH] i Hi /=; first lia.
case: i Hi => [|i] Hi /=.
- by eexists.
- have [fi ->] := IH i ltac:(lia).
  by eexists.
Qed.

End Fin.

Section MM2Adapter.

Variable P : list mm2_instr.
Let n := length P.
Let Q := fin (S (S n)).

Local Ltac equivs_to_eq :=
  repeat match goal with
  | H : @equiv _ (@monoid_equiv
      (list_monoid mm_sym_setoid)) _ _
    |- _ =>
    apply mm_list_equiv_eq in H
  end; subst.

(** Convert a library mm2_instr at PC index i (1-indexed)
    to our mm_instr type.  Jump targets outside 1..n cause
    halting. *)

Definition translate_state (q : nat) : Q :=
  match q with
  | 0 =>
    Fin.F1
  | S q =>
    Fin.FS match @nat_to_fin n q with
           | Some q => Fin.FS q
           | None => Fin.F1
           end
  end.

Definition next_state (q : Q) : Q :=
  translate_state q.

Definition mm2_atom_fun (ρ : mm2_instr) (s : mm2_state) :=
  let '(i,(a,b)) := s in
  match ρ with
  | mm2_inc_a => (1+i,(S a,b))
  | mm2_inc_b => (1+i,(a,S b))
  | mm2_dec_a j =>
    match a with
    | 0 => (1+i,(0,b))
    | S a => (j,(a,b))
    end
  | mm2_dec_b j =>
    match b with
    | 0 => (1+i,(a,0))
    | S b => (j,(a,b))
    end
  end.

Lemma mm2_atom_fun_spec ρ s1 s2 :
  mm2_atom ρ s1 s2 ↔ mm2_atom_fun ρ s1 = s2.
Proof.
split.
- by case.
- case: ρ => [||j|j].
  1,2: case: s1 => [i [a b]] /= <-; constructor.
  + case: s1 => [i [[|a] b]] /= <-; constructor.
  + case: s1 => [i [a [|b]]] /= <-; constructor.
Qed.

Arguments mm2_atom_fun_spec {_ _ _}.

Definition mm2_step_fun s :=
  match s.1 with
  | 0 => None
  | S i => match nth_error P i with
           | Some ρ => Some (mm2_atom_fun ρ s)
           | None => None
           end
  end.

Lemma mm2_instr_at_nth_error ρ i :
  mm2_instr_at ρ (S i) P ↔ nth_error P i = Some ρ.
Proof.
split.
- case=> l [r [HP Hlen]].
  have -> : i = length l by lia.
  by rewrite HP nth_error_app2 // Nat.sub_diag.
- move=> Hnth.
  have [l [r [HP Hlen]]] :=
    nth_error_split _ _ Hnth.
  by exists l, r; split; first done; lia.
Qed.

Lemma mm2_step_fun_spec s1 s2 :
  mm2_step P s1 s2 ↔ mm2_step_fun s1 = Some s2.
Proof.
split.
- case=> ρ [Hinstr /mm2_atom_fun_spec <-].
  rewrite /mm2_step_fun /=.
  case: s1 Hinstr => [[|i] [a b]] /= Hinstr.
  { case: Hinstr => l [r [_ /=]]; lia. }
  by rewrite (iffLR (mm2_instr_at_nth_error _ _) Hinstr).
- rewrite /mm2_step_fun.
  case: s1 => [[|i] [a b]] //=.
  case Hnth: (nth_error P i) => [ρ|] //= [<-].
  exists ρ; split.
  + by apply/mm2_instr_at_nth_error.
  + by apply/mm2_atom_fun_spec.
Qed.

Arguments mm2_step_fun_spec {_ _}.

Definition mm2_to_instr (instr : mm2_instr) : mm_instr Q :=
  match instr with
  | mm2_inc_a => mm_inc_a
  | mm2_inc_b => mm_inc_b
  | mm2_dec_a q' => mm_dec_a (translate_state q')
  | mm2_dec_b q' => mm_dec_b (translate_state q')
  end.

(** The program function: given a state (fin (S n)),
    return the corresponding instruction.  State 0 and
    out-of-range states halt with output false. *)

Definition mm2_prog (q : Q) : mm_instr Q :=
  match nth_error P (fin_to_nat q - 2) with
  | Some instr => mm2_to_instr instr
  | None => mm_inc_a (* Unused *)
  end.

(** Active states: all fin (S n) except 0. *)

Definition active_states : list Q :=
  Fin.FS <$> (Fin.FS <$> enum (fin n)).

(** Running configurations *)

Definition C := config_set active_states.

(** All configurations *)

Definition T := config_set (enum Q).

(** The transition relation for a concrete MM2 program. *)

Definition mm2_R := transition_rel next_state mm2_prog active_states.

(** Encode an MM2 state as a configuration word. *)

Definition mm2_config (s : mm2_state) : list (mm_sym Q) :=
  config_word (fst (snd s)) (snd (snd s)) (translate_state (fst s)).

(** Running or accepted *)

Definition partially_accepted :=
  C ⊔ Unit (mm2_config (0,(0,0))).

Lemma power_le_star {T' : pre_ka} (x : T') k :
  x ^ k ⊑ star x.
Proof.
elim: k => [|k IH]; first exact: pre_ka_one_star.
apply: transitivity (pre_ka_mul_star _).
by apply: pre_ka_mul_mono IH.
Qed.

Lemma repeat_le_star (x : mm_sym Q) a : Unit (repeat x a) ⊑ star (Unit [x]).
Proof.
have -> : repeat x a = [x] ^ a.
{ by elim: a => //= a ->. }
rewrite monoid_morphism_power.
exact: power_le_star.
Qed.

Lemma config_word_le q (qs : list Q) a b :
  q ∈ qs →
  Unit (config_word a b q) ⊑ config_set qs.
Proof.
move=> q_qs; rewrite /config_word /config_set
  (monoid_morphism_mul (f := @Unit _))
  (monoid_morphism_mul (f := @Unit _)) assoc.
refine (pre_ka_mul_mono _ _).
- refine (pre_ka_mul_mono _ _);
    exact: repeat_le_star.
- exact: sqsubseteq_join_list q_qs.
Qed.

Lemma config_set_char q (qs : list Q) a b :
  Unit (config_word a b q) ⊑ config_set qs →
  q ∈ qs.
Proof.
rewrite -l_alt /config_set
  monoid_morphism_mul /=.
case=> w12 [w3 [/leibniz_equiv_iff Heq
  [_ Hw3]]].
rewrite semi_lattice_morphism_join_list
  elem_of_lang_join_list in Hw3.
case: Hw3 => [q' [q'_S /=
  /leibniz_equiv_iff Hw3]]; subst w3.
suff: q = q' by move=> ->.
move: Heq; rewrite /config_word /mul /list_mul
  !app_assoc => Heq.
by have [_ []] := app_inj_tail _ _ _ _ Heq.
Qed.

Lemma lang_sing_mm_a (w : list_monoid mm_sym_setoid) (m : nat) :
  (lang_sing [@mm_a Q] ^ m) w -> w ≡ repeat mm_a m.
elim: m w => [| m IH]; first by rewrite /power /repeat /= => _ ->; eauto.
rewrite /= => _ [_ [x2 [-> [-> Hlang]]]]; rewrite (IH _ Hlang); eauto.
Qed.

Lemma lang_sing_mm_b (w : list_monoid mm_sym_setoid) (m : nat) :
  (lang_sing [@mm_b Q] ^ m) w -> w ≡ repeat mm_b m.
elim: m w => [| m IH]; first by rewrite /power /repeat /= => _ ->; eauto.
rewrite /= => _ [_ [x2 [-> [-> Hlang]]]]; rewrite (IH _ Hlang); eauto.
Qed.

Lemma unit_sqsubseteq_join_list_unit (w : list_monoid mm_sym_setoid) (qs : list Q) :
  Unit w ⊑ ⨆ q ∈ qs, Unit [mm_q q] -> ∃ q, q ∈ qs ∧ w ≡ [mm_q q].
Proof.
move=> /l_alt Hw.
rewrite semi_lattice_morphism_join_list elem_of_lang_join_list in Hw.
case: Hw => /= [q [Hq H]]; exists q; eauto.
Qed.

Lemma config_set_inv xs (qs : list Q) :
  Unit xs ⊑ config_set qs →
  ∃ a b q, xs = config_word a b q ∧ q ∈ qs.
Proof.
rewrite -l_alt /config_set monoid_morphism_mul /=.
case=> w12 [w3 [Heq [
  [w1 [w2 [Hw12 [[na /lang_sing_mm_a Hna] [nb /lang_sing_mm_b Hnb]]]]]
  /l_alt /unit_sqsubseteq_join_list_unit [q [Hq Hw3]]
]]].
move: Heq.
rewrite {w12}Hw12 {w1}Hna {w2}Hnb {w3}Hw3 leibniz_equiv_iff => ->.
exists na, nb, q.
rewrite /config_word app_assoc; eauto.
Qed.

Lemma translate_state_active i :
  0 < i ≤ n → translate_state i ∈ active_states.
Proof.
case: i => [|i] [Hi1 Hi2]; first lia.
rewrite /translate_state /active_states.
have Hi : i < n by lia.
have [fi Hfi] := @nat_to_fin_lt n i Hi.
rewrite Hfi; apply/elem_of_list_fmap.
exists (Fin.FS fi); split; first done.
apply/elem_of_list_fmap.
exists fi; split; first done.
exact: elem_of_enum.
Qed.

Lemma elem_of_active_state q :
  q ∈ active_states →
  ∃ i : fin n, q = Fin.FS (Fin.FS i).
Proof.
rewrite /active_states.
move/elem_of_list_fmap => [q' [->
  /elem_of_list_fmap [q'' [-> _]]]].
by eauto.
Qed.

Lemma active_translate_state q :
  q ∈ active_states →
  ∃ i, 0 < i ≤ n ∧ q = translate_state i.
Proof.
case/elem_of_active_state => {}q ->.
exists (S (fin_to_nat q)).
split.
- split; first lia.
  have := fin_to_nat_lt q; lia.
- rewrite /translate_state /=.
  have [fi Hfi] := @nat_to_fin_lt n
    (fin_to_nat q)
    (fin_to_nat_lt q).
  rewrite Hfi; do 2 f_equal.
  have H := @nat_to_finK n (fin_to_nat q)
    fi Hfi.
  exact/fin_to_nat_inj.
Qed.

Lemma elem_of_C s : Unit (mm2_config s) ⊑ C ↔ 0 < s.1 ≤ n.
Proof.
rewrite /mm2_config /C; case: s => [i [a b]] /=.
split.
- case/config_set_char/elem_of_active_state=> q.
  case: i=> //= i /FS_inj.
  have [//|contra]: S i <= n ∨ n ≤ i by lia.
  { lia. }
  by rewrite nat_to_fin_ge //.
- move=> Hi.
  exact: config_word_le (translate_state_active Hi).
Qed.

Lemma elem_of_T s : Unit (mm2_config s) ⊑ T.
Proof.
rewrite /mm2_config /T.
case: s => [i [a b]] /=.
apply: config_word_le.
apply: (elem_of_enum (translate_state i)).
Qed.

Lemma fin_case m (q : fin (S m)) : q = 0%fin ∨ ∃ q', q = Fin.FS q'.
Proof. apply (Fin.caseS' q); eauto. Qed.

Lemma elem_of_T_inv xs : Unit xs ⊑ T → ∃ s, xs = mm2_config s.
Proof.
case/config_set_inv=> a [] b [] q [] -> _.
have [->|[{}q ->]] := fin_case q.
{ by exists (0,(a,b)). }
have [->|[{}q ->]] := fin_case q.
{ exists (S n, (a,b)). rewrite /mm2_config /=.
  rewrite nat_to_fin_ge //; lia. }
exists (S (fin_to_nat q), (a, b)).
by rewrite /mm2_config /= fin_to_natK.
Qed.

(** ** The encoding faithfully represents the transitions of a Minsky machine (~
Lemma 14). *)

Lemma repeat_le_star_d (x : mm_sym Q) a :
  Unit (repeat x a, repeat x a) ⊑
  star_d x.
Proof.
rewrite /star_d; elim: a => [|a IH].
- exact: pre_ka_one_star.
- have -> : (x :: repeat x a,
    x :: repeat x a)
    = ([x], [x])
      ⋅ (repeat x a, repeat x a) by [].
  rewrite monoid_morphism_mul.
  apply: transitivity (pre_ka_mul_star _).
  by apply: pre_ka_mul_mono.
Qed.

Local Lemma config_word_inj a1 b1 (q1 : Q)
    a2 b2 (q2 : Q) :
  config_word a1 b1 q1 =
  config_word a2 b2 q2 →
  a1 = a2 ∧ b1 = b2 ∧ q1 = q2.
Proof.
rewrite /config_word => H.
have Ha : a1 = a2.
{ move: a2 b2 q2 H;
  elim: a1 => [|a1 IH] [|a2] b2 q2 //=.
  - by case: b1 => [|?] /=; congruence.
  - by case: b2 => [|?] /=; congruence.
  - by move=> [= /IH ->]. }
subst a2; have Hb : b1 = b2.
{ move: (f_equal (@length _) H).
  by rewrite !length_app !repeat_length /=;
    lia. }
subst b2; split; [done|]; split; [done|].
have /app_inv_head H' := H.
by have [= ->] := app_inv_head _ _ _ H'.
Qed.

Local Lemma translate_state_spec pc :
  pc < n →
  fin_to_nat (translate_state (S pc)) =
  S (S pc).
Proof.
move=> Hpc.
rewrite /translate_state.
have [fi Hfi] := @nat_to_fin_lt n pc Hpc.
by rewrite Hfi /= (nat_to_finK Hfi).
Qed.

Local Lemma mm2_prog_spec pc ρ :
  nth_error P pc = Some ρ →
  mm2_prog (translate_state (S pc)) =
  mm2_to_instr ρ.
Proof.
move=> Hnth.
have Hpc : pc < n
  by apply/nth_error_Some; congruence.
rewrite /mm2_prog /translate_state.
have [fi Hfi] := @nat_to_fin_lt n pc Hpc.
rewrite Hfi /=.
have Heq := nat_to_finK Hfi.
by rewrite Heq Nat.sub_0_r Hnth.
Qed.

Lemma encoding_complete s1 s2 :
  mm2_step P s1 s2 →
  Unit (mm2_config s1, mm2_config s2) ⊑ mm2_R.
Proof.
move/mm2_step_fun_spec.
case: s1 => [[|pc] [a b]] //=.
rewrite /mm2_step_fun /=.
case Hnth: (nth_error P pc) => [ρ|] //=
  [<-].
have Hpc : pc < n
  by apply/nth_error_Some; congruence.
set q := translate_state (S pc).
have Hactive : q ∈ active_states
  by apply: translate_state_active; lia.
have Hprog := mm2_prog_spec Hnth.
have Hnext: next_state q =
  translate_state (S (S pc)).
{ by rewrite /next_state /q
    translate_state_spec. }
etransitivity;
  last exact:
    sqsubseteq_join_list _ _ _ Hactive.
rewrite Hprog.
Local Ltac solve_config_eq :=
  rewrite /config_word;
  cbv [mul prod_mul list_mul fst snd
    monoid_mul list_monoid]; simpl;
  f_equal; rewrite ?app_nil_r -?app_assoc //.
case: ρ Hnth Hprog => [||j|j]
  Hnth Hprog.
- (* mm2_inc_a *)
  rewrite /mm2_config -/q;
    simpl mm2_atom_fun; simpl fst;
    simpl snd; rewrite -?Hnext.
  have -> : (config_word a b q,
    config_word (S a) b (next_state q))
    = (([] : list _, [mm_a])
      ⋅ (repeat mm_a a, repeat mm_a a)
      ⋅ (repeat mm_b b, repeat mm_b b)
      ⋅ ([mm_q q], [] : list _)
      ⋅ ([] : list _,
        [mm_q (next_state q)])).
  { solve_config_eq. }
  rewrite !monoid_morphism_mul
    /encode_instr /mm2_to_instr
    /sym_r /sym_l.
  apply: pre_ka_mul_mono; last done.
  apply: pre_ka_mul_mono; last done.
  apply: pre_ka_mul_mono;
    last exact: repeat_le_star_d.
  apply: pre_ka_mul_mono;
    last exact: repeat_le_star_d.
  done.
- (* mm2_inc_b *)
  rewrite /mm2_config -/q;
    simpl mm2_atom_fun; simpl fst;
    simpl snd; rewrite -?Hnext.
  have -> : (config_word a b q,
    config_word a (S b) (next_state q))
    = ((repeat mm_a a, repeat mm_a a)
      ⋅ (([] : list _, [mm_b])
      ⋅ (repeat mm_b b, repeat mm_b b)
      ⋅ ([mm_q q], [] : list _)
      ⋅ ([] : list _,
        [mm_q (next_state q)]))).
  { solve_config_eq. }
  rewrite !monoid_morphism_mul
    /encode_instr /mm2_to_instr
    /sym_r /sym_l.
  rewrite 3!assoc.
  apply: pre_ka_mul_mono; last done.
  apply: pre_ka_mul_mono; last done.
  apply: pre_ka_mul_mono;
    last exact: repeat_le_star_d.
  apply: pre_ka_mul_mono; last done.
  exact: repeat_le_star_d.
- (* mm2_dec_a j *)
  rewrite /mm2_config -/q.
  case: a.
  + (* a = 0: branch 1 *)
    simpl mm2_atom_fun; simpl fst;
      simpl snd; rewrite -?Hnext.
    etransitivity;
      last exact: sqsubseteq_join_left.
    have -> : (config_word 0 b q,
      config_word 0 b (next_state q))
      = ((repeat mm_b b, repeat mm_b b)
        ⋅ ([mm_q q], [] : list _)
        ⋅ ([] : list _,
          [mm_q (next_state q)])).
    { solve_config_eq. }
    rewrite !monoid_morphism_mul
      /encode_instr /mm2_to_instr
      /sym_r /sym_l.
    apply: pre_ka_mul_mono; last done.
    apply: pre_ka_mul_mono; last done.
    exact: repeat_le_star_d.
  + (* a = S a': branch 2 *)
    move=> a'.
    simpl mm2_atom_fun; simpl fst;
      simpl snd.
    etransitivity;
      last exact: sqsubseteq_join_right.
    have -> : (config_word (S a') b q,
      config_word a' b (translate_state j))
      = (([mm_a], [] : list _)
        ⋅ (repeat mm_a a', repeat mm_a a')
        ⋅ (repeat mm_b b, repeat mm_b b)
        ⋅ ([mm_q q], [] : list _)
        ⋅ ([] : list _,
          [mm_q (translate_state j)])).
    { solve_config_eq. }
    rewrite !monoid_morphism_mul
      /encode_instr /mm2_to_instr
      /sym_r /sym_l.
    apply: pre_ka_mul_mono; last done.
    apply: pre_ka_mul_mono; last done.
    apply: pre_ka_mul_mono;
      last exact: repeat_le_star_d.
    apply: pre_ka_mul_mono;
      last exact: repeat_le_star_d.
    done.
- (* mm2_dec_b j *)
  rewrite /mm2_config -/q.
  case: b.
  + (* b = 0: branch 1 *)
    simpl mm2_atom_fun; simpl fst;
      simpl snd; rewrite -?Hnext.
    etransitivity;
      last exact: sqsubseteq_join_left.
    have -> : (config_word a 0 q,
      config_word a 0 (next_state q))
      = ((repeat mm_a a, repeat mm_a a)
        ⋅ ([mm_q q], [] : list _)
        ⋅ ([] : list _,
          [mm_q (next_state q)])).
    { solve_config_eq. }
    rewrite !monoid_morphism_mul
      /encode_instr /mm2_to_instr
      /sym_r /sym_l.
    apply: pre_ka_mul_mono; last done.
    apply: pre_ka_mul_mono; last done.
    exact: repeat_le_star_d.
  + (* b = S b': branch 2 *)
    move=> b'.
    simpl mm2_atom_fun; simpl fst;
      simpl snd.
    etransitivity;
      last exact: sqsubseteq_join_right.
    have -> : (config_word a (S b') q,
      config_word a b' (translate_state j))
      = ((repeat mm_a a, repeat mm_a a)
        ⋅ (([mm_b], [] : list _)
        ⋅ (repeat mm_b b', repeat mm_b b')
        ⋅ ([mm_q q], [] : list _)
        ⋅ ([] : list _,
          [mm_q (translate_state j)]))).
    { solve_config_eq. }
    rewrite !monoid_morphism_mul
      /encode_instr /mm2_to_instr
      /sym_r /sym_l 3!assoc.
    apply: pre_ka_mul_mono; last done.
    apply: pre_ka_mul_mono; last done.
    apply: pre_ka_mul_mono;
      last exact: repeat_le_star_d.
    apply: pre_ka_mul_mono; last done.
    exact: repeat_le_star_d.
Qed.

Local Lemma star_d_inv (x : mm_sym Q) s1 s2 :
  Unit (s1, s2) ⊑ star_d x →
  ∃ k, s1 = repeat x k ∧ s2 = repeat x k.
Proof.
rewrite /star_d -l_alt /=.
case=> k; elim: k s1 s2 =>
  [|k IH] s1 s2 /=.
- by case=> /= /mm_list_equiv_eq ->
    /mm_list_equiv_eq ->; exists 0.
- move=> /=.
  case=> [[a1 a2] [[b1 b2]
    [[El Er]
      [[El2 Er2] Hrec]]]].
  simpl in El, Er, El2, Er2.
  apply leibniz_equiv in El.
  apply leibniz_equiv in Er.
  apply leibniz_equiv in El2.
  apply leibniz_equiv in Er2; subst.
  have [k' [-> ->]] := IH _ _ Hrec.
  by exists (S k').
Qed.

Local Lemma Unit_le_mul_pair
    (e1 e2 : ka_term (list (mm_sym Q) *
      list (mm_sym Q)))
    (s w : list (mm_sym Q)) :
  Unit (s, w) ⊑ e1 ⋅ e2 →
  ∃ s1 w1 s2 w2,
    s = s1 ++ s2 ∧ w = w1 ++ w2 ∧
    Unit (s1, w1) ⊑ e1 ∧
    Unit (s2, w2) ⊑ e2.
Proof.
rewrite -l_alt /=.
case=> [[s1 w1] [[s2 w2] [[El Er]
  [/l_alt H1 /l_alt H2]]]].
simpl in El, Er.
apply leibniz_equiv in El.
apply leibniz_equiv in Er; subst.
by exists s1, w1, s2, w2.
Qed.

Local Lemma Unit_le_Unit_pair
    (sl sr sl' sr' : list (mm_sym Q)) :
  Unit (sl, sr) ⊑
    (Unit (sl', sr')
      : ka_term (list (mm_sym Q) *
        list (mm_sym Q))) →
  sl = sl' ∧ sr = sr'.
Proof.
rewrite -l_alt /=.
case=> El Er.
simpl in El, Er.
by apply leibniz_equiv in El;
  apply leibniz_equiv in Er.
Qed.

Local Lemma Unit_le_join_pair
    (e1 e2 : ka_term (list (mm_sym Q) *
      list (mm_sym Q)))
    (s w : list (mm_sym Q)) :
  Unit (s, w) ⊑ e1 ⊔ e2 →
  Unit (s, w) ⊑ e1 ∨ Unit (s, w) ⊑ e2.
Proof.
move/l_alt => /= [H|H];
  [left|right]; exact/l_alt.
Qed.

Local Lemma translate_state_inv
    (fi : fin n) pc :
  translate_state pc = Fin.FS (Fin.FS fi) →
  pc = S (fin_to_nat fi).
Proof.
case: pc => [|pc].
- rewrite /translate_state /= => E.
  have := f_equal fin_to_nat E; simpl; lia.
- rewrite /translate_state.
  case Hf: (@nat_to_fin n pc) => [fi'|].
  + move/FS_inj/FS_inj => Hfi; subst fi'.
    by rewrite -(nat_to_finK Hf).
  + move=> E.
    have := f_equal fin_to_nat E; simpl; lia.
Qed.

Local Lemma translate_state_eq q :
  translate_state (S (fin_to_nat q)) =
  Fin.FS (Fin.FS q) :> Q.
Proof.
rewrite /translate_state.
have Hpc := fin_to_nat_lt q.
have [fi' Hfi'] := @nat_to_fin_lt n
  (fin_to_nat q) Hpc.
rewrite Hfi'; do 2 f_equal.
exact/fin_to_nat_inj/(nat_to_finK Hfi').
Qed.

Local Ltac solve_encoding_eq :=
  rewrite /mm2_config /config_word /=;
  rewrite ?app_nil_r -?app_assoc //=.

Local Ltac decompose_leaves :=
  repeat match goal with
  | H : Unit (_, _) ⊑ Unit (_, _) |- _ =>
    apply Unit_le_Unit_pair in H;
    destruct H; subst
  end.

Lemma encoding_sound s1 w :
  Unit (mm2_config s1, w) ⊑ mm2_R →
  ∃ s2, w = mm2_config s2 ∧ mm2_step P s1 s2.
Proof.
rewrite -l_alt /mm2_R /transition_rel
  semi_lattice_morphism_join_list
  elem_of_lang_join_list.
case=> q' [q_active /l_alt Hl].
have [fi Hfi] :=
  elem_of_active_state q_active.
move: Hl; rewrite Hfi => Hl {q' Hfi
  q_active}.
set q := Fin.FS (Fin.FS fi).
have Hpc : fin_to_nat fi < n :=
  fin_to_nat_lt fi.
case Hρ: (nth_error P (fin_to_nat fi)) =>
  [ρ|]; last by move/nth_error_None: Hρ; lia.
have Hts := translate_state_eq fi.
have Hprog := mm2_prog_spec Hρ.
rewrite Hts in Hprog.
rewrite Hprog in Hl.
case: ρ Hρ Hprog Hl => [||j|j] Hρ Hprog Hl.
- (* mm2_inc_a *)
  (* e1 ⋅ e2 ⋅ e3 ⋅ e4 ⋅ e5 where
     e1 = sym_r mm_a, e2 = star_d mm_a,
     e3 = star_d mm_b,
     e4 = sym_l (mm_q q),
     e5 = sym_r (mm_q (next_state q)) *)
  case/Unit_le_mul_pair: Hl =>
    s14 [w14 [s5 [w5
      [Es [Ew [Hl Hl5]]]]]].
  case/Unit_le_mul_pair: Hl =>
    s13 [w13 [s4 [w4
      [Es14 [Ew14 [Hl Hl4]]]]]].
  case/Unit_le_mul_pair: Hl =>
    s12 [w12 [s3 [w3
      [Es13 [Ew13 [Hl Hl3]]]]]].
  case/Unit_le_mul_pair: Hl =>
    s1' [w1' [s2 [w2
      [Es12 [Ew12 [Hl1 Hl2]]]]]].
  apply star_d_inv in Hl2.
  destruct Hl2 as [ka [-> ->]].
  apply star_d_inv in Hl3.
  destruct Hl3 as [kb [-> ->]].
  apply Unit_le_Unit_pair in Hl1.
  destruct Hl1 as [-> ->].
  apply Unit_le_Unit_pair in Hl4.
  destruct Hl4 as [-> ->].
  apply Unit_le_Unit_pair in Hl5.
  destruct Hl5 as [-> ->].
  have Hcw : mm2_config s1 =
    config_word ka kb q.
  { move: Es; rewrite Es14 Es13 Es12.
    rewrite /mm2_config /config_word /=.
    by rewrite ?app_nil_r -?app_assoc. }
  have /config_word_inj [Ha [Hb Hq]] :=
    Hcw.
  have Hpc' := translate_state_inv Hq.
  exists (1 + fst s1,
    (S (fst (snd s1)), snd (snd s1))).
  have Ew' : w = config_word
    (S ka) kb (next_state q).
  { move: Ew; rewrite Ew14 Ew13 Ew12.
    rewrite /config_word /=.
    by rewrite ?app_nil_r -?app_assoc. }
  split.
  + rewrite Ew' /mm2_config /config_word
      /= Ha Hb Hpc'.
    by rewrite /next_state /q.
  + apply/mm2_step_fun_spec.
    rewrite /mm2_step_fun.
    case: s1 Hpc' Ha Hb Es Ew Ew' Hcw Hq
      => [pc1 [a1 b1]] /= Hpc' Ha Hb
        _ _ _ _ _.
    by rewrite Hpc' /= Hρ /= Ha Hb.
- (* mm2_inc_b:
     star_d mm_a ⋅ sym_r mm_b ⋅ star_d mm_b
     ⋅ sym_l (mm_q q)
     ⋅ sym_r (mm_q (next_state q)) *)
  case/Unit_le_mul_pair: Hl =>
    s14 [w14 [s5 [w5
      [Es [Ew [Hl Hl5]]]]]].
  case/Unit_le_mul_pair: Hl =>
    s13 [w13 [s4 [w4
      [Es14 [Ew14 [Hl Hl4]]]]]].
  case/Unit_le_mul_pair: Hl =>
    s12 [w12 [s3 [w3
      [Es13 [Ew13 [Hl Hl3]]]]]].
  case/Unit_le_mul_pair: Hl =>
    s1' [w1' [s2 [w2
      [Es12 [Ew12 [Hl1 Hl2]]]]]].
  apply star_d_inv in Hl1.
  destruct Hl1 as [ka [-> ->]].
  apply star_d_inv in Hl3.
  destruct Hl3 as [kb [-> ->]].
  apply Unit_le_Unit_pair in Hl2.
  destruct Hl2 as [-> ->].
  apply Unit_le_Unit_pair in Hl4.
  destruct Hl4 as [-> ->].
  apply Unit_le_Unit_pair in Hl5.
  destruct Hl5 as [-> ->].
  have Hcw : mm2_config s1 =
    config_word ka kb q.
  { move: Es; rewrite Es14 Es13 Es12.
    rewrite /config_word /=.
    by rewrite ?app_nil_r -?app_assoc. }
  have /config_word_inj [Ha [Hb Hq]] :=
    Hcw.
  have Hpc' := translate_state_inv Hq.
  have Ew' : w = config_word
    ka (S kb) (next_state q).
  { move: Ew; rewrite Ew14 Ew13 Ew12.
    rewrite /config_word /=.
    by rewrite ?app_nil_r -?app_assoc. }
  exists (1 + fst s1,
    (fst (snd s1), S (snd (snd s1)))).
  split.
  + rewrite Ew' /mm2_config /config_word
      /= Ha Hb Hpc'.
    by rewrite /next_state /q.
  + apply/mm2_step_fun_spec.
    rewrite /mm2_step_fun.
    case: s1 Hpc' Ha Hb Es Ew Ew' Hcw Hq
      => [pc1 [a1 b1]] /= Hpc' Ha Hb
        _ _ _ _ _.
    by rewrite Hpc' /= Hρ /= Ha Hb.
- (* mm2_dec_a j *)
  case/Unit_le_join_pair: Hl => Hl.
  + (* zero branch: a = 0,
       star_d mm_b ⋅ sym_l (mm_q q)
       ⋅ sym_r (mm_q (next_state q)) *)
    case/Unit_le_mul_pair: Hl =>
      s12 [w12 [s3 [w3
        [Es [Ew [Hl Hl3]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s1' [w1' [s2 [w2
        [Es12 [Ew12 [Hl1 Hl2]]]]]].
    apply star_d_inv in Hl1.
    destruct Hl1 as [kb [-> ->]].
    apply Unit_le_Unit_pair in Hl2.
    destruct Hl2 as [-> ->].
    apply Unit_le_Unit_pair in Hl3.
    destruct Hl3 as [-> ->].
    have Hcw : mm2_config s1 =
      config_word 0 kb q.
    { move: Es; rewrite Es12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    have /config_word_inj [Ha [Hb Hq]] :=
      Hcw.
    have Hpc' := translate_state_inv Hq.
    have Ew' : w = config_word
      0 kb (next_state q).
    { move: Ew; rewrite Ew12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    exists (1 + fst s1,
      (fst (snd s1), snd (snd s1))).
    split.
    * rewrite Ew' /mm2_config /config_word
        /= Ha Hb Hpc'.
      by rewrite /next_state /q.
    * apply/mm2_step_fun_spec.
      rewrite /mm2_step_fun.
      case: s1 Hpc' Ha Hb Es Ew Ew' Hcw Hq
        => [pc1 [a1 b1]] /= Hpc' Ha Hb
          _ _ _ _ _.
      by rewrite Hpc' /= Hρ /= Ha Hb.
  + (* nonzero branch: a = S a',
       sym_l mm_a ⋅ star_d mm_a
       ⋅ star_d mm_b ⋅ sym_l (mm_q q)
       ⋅ sym_r (mm_q q') *)
    case/Unit_le_mul_pair: Hl =>
      s14 [w14 [s5 [w5
        [Es [Ew [Hl Hl5]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s13 [w13 [s4 [w4
        [Es14 [Ew14 [Hl Hl4]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s12 [w12 [s3 [w3
        [Es13 [Ew13 [Hl Hl3]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s1' [w1' [s2 [w2
        [Es12 [Ew12 [Hl1 Hl2]]]]]].
    apply star_d_inv in Hl2.
    destruct Hl2 as [ka [-> ->]].
    apply star_d_inv in Hl3.
    destruct Hl3 as [kb [-> ->]].
    apply Unit_le_Unit_pair in Hl1.
    destruct Hl1 as [-> ->].
    apply Unit_le_Unit_pair in Hl4.
    destruct Hl4 as [-> ->].
    apply Unit_le_Unit_pair in Hl5.
    destruct Hl5 as [-> ->].
    have Hcw : mm2_config s1 =
      config_word (S ka) kb q.
    { move: Es; rewrite Es14 Es13 Es12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    have /config_word_inj [Ha [Hb Hq]] :=
      Hcw.
    have Hpc' := translate_state_inv Hq.
    have Ew' : w = config_word
      ka kb (translate_state j).
    { move: Ew; rewrite Ew14 Ew13 Ew12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    exists (j, (ka, snd (snd s1))).
    split.
    * by rewrite Ew' /mm2_config /= Hb.
    * apply/mm2_step_fun_spec.
      rewrite /mm2_step_fun.
      case: s1 Hpc' Ha Hb Es Ew Ew' Hcw Hq
        => [pc1 [a1 b1]] /= Hpc' Ha Hb
          _ _ _ _ _.
      by rewrite Hpc' /= Hρ /= Ha Hb.
- (* mm2_dec_b j *)
  case/Unit_le_join_pair: Hl => Hl.
  + (* zero branch: b = 0,
       star_d mm_a ⋅ sym_l (mm_q q)
       ⋅ sym_r (mm_q (next_state q)) *)
    case/Unit_le_mul_pair: Hl =>
      s12 [w12 [s3 [w3
        [Es [Ew [Hl Hl3]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s1' [w1' [s2 [w2
        [Es12 [Ew12 [Hl1 Hl2]]]]]].
    apply star_d_inv in Hl1.
    destruct Hl1 as [ka [-> ->]].
    apply Unit_le_Unit_pair in Hl2.
    destruct Hl2 as [-> ->].
    apply Unit_le_Unit_pair in Hl3.
    destruct Hl3 as [-> ->].
    have Hcw : mm2_config s1 =
      config_word ka 0 q.
    { move: Es; rewrite Es12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    have /config_word_inj [Ha [Hb Hq]] :=
      Hcw.
    have Hpc' := translate_state_inv Hq.
    have Ew' : w = config_word
      ka 0 (next_state q).
    { move: Ew; rewrite Ew12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    exists (1 + fst s1,
      (fst (snd s1), snd (snd s1))).
    split.
    * rewrite Ew' /mm2_config /config_word
        /= Ha Hb Hpc'.
      by rewrite /next_state /q.
    * apply/mm2_step_fun_spec.
      rewrite /mm2_step_fun.
      case: s1 Hpc' Ha Hb Es Ew Ew' Hcw Hq
        => [pc1 [a1 b1]] /= Hpc' Ha Hb
          _ _ _ _ _.
      by rewrite Hpc' /= Hρ /= Ha Hb.
  + (* nonzero branch: b = S b',
       star_d mm_a ⋅ sym_l mm_b
       ⋅ star_d mm_b ⋅ sym_l (mm_q q)
       ⋅ sym_r (mm_q q') *)
    case/Unit_le_mul_pair: Hl =>
      s14 [w14 [s5 [w5
        [Es [Ew [Hl Hl5]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s13 [w13 [s4 [w4
        [Es14 [Ew14 [Hl Hl4]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s12 [w12 [s3 [w3
        [Es13 [Ew13 [Hl Hl3]]]]]].
    case/Unit_le_mul_pair: Hl =>
      s1' [w1' [s2 [w2
        [Es12 [Ew12 [Hl1 Hl2]]]]]].
    apply star_d_inv in Hl1.
    destruct Hl1 as [ka [-> ->]].
    apply star_d_inv in Hl3.
    destruct Hl3 as [kb [-> ->]].
    apply Unit_le_Unit_pair in Hl2.
    destruct Hl2 as [-> ->].
    apply Unit_le_Unit_pair in Hl4.
    destruct Hl4 as [-> ->].
    apply Unit_le_Unit_pair in Hl5.
    destruct Hl5 as [-> ->].
    have Hcw : mm2_config s1 =
      config_word ka (S kb) q.
    { move: Es; rewrite Es14 Es13 Es12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    have /config_word_inj [Ha [Hb Hq]] :=
      Hcw.
    have Hpc' := translate_state_inv Hq.
    have Ew' : w = config_word
      ka kb (translate_state j).
    { move: Ew; rewrite Ew14 Ew13 Ew12.
      rewrite /config_word /=.
      by rewrite ?app_nil_r -?app_assoc. }
    exists (j, (fst (snd s1), kb)).
    split.
    * by rewrite Ew' /mm2_config /= Ha.
    * apply/mm2_step_fun_spec.
      rewrite /mm2_step_fun.
      case: s1 Hpc' Ha Hb Es Ew Ew' Hcw Hq
        => [pc1 [a1 b1]] /= Hpc' Ha Hb
          _ _ _ _ _.
      by rewrite Hpc' /= Hρ /= Ha Hb.
Qed.

Lemma encoding_rtc_complete s1 s2 :
  rtc (mm2_step P) s1 s2 →
  rtc (λ xs ys, Unit (xs, ys) ⊑ mm2_R)
    (mm2_config s1) (mm2_config s2).
Proof.
elim=> // x y z xy _ IH.
apply: rtc_l _ IH; exact: encoding_complete xy.
Qed.

Lemma encoding_rtc_sound s1 ys :
  rtc (λ xs ys, Unit (xs, ys) ⊑ mm2_R) (mm2_config s1) ys →
  ∃ s2, ys = mm2_config s2 ∧ rtc (mm2_step P) s1 s2.
Proof.
move=> Hrtc; apply: (rtc_ind_r
  (λ z, ∃ s2, z = mm2_config s2 ∧
    rtc (mm2_step P) s1 s2)
  (mm2_config s1) _ _ _ Hrtc).
- exists s1; done.
- move=> y z _ Hyz [s2 [Hy Hrtc']].
  subst y.
  case: (encoding_sound Hyz) => s3 [-> Hstep].
  exists s3; split; [done|].
  exact: rtc_r Hrtc' Hstep.
Qed.

Local Lemma translate_state_inj i1 i2 :
  i2 ≤ n →
  translate_state i1 = translate_state i2 →
  i1 = i2.
Proof.
case: i2 => [|q2].
- move=> _ Hts; case: i1 Hts => [//|q1].
  rewrite /translate_state => E.
  have := f_equal fin_to_nat E; simpl.
  by case: (nat_to_fin q1) => [?|] /=; lia.
- move=> Hq2.
  have Hq2' : q2 < n by lia.
  have [fi2 Hfi2] := @nat_to_fin_lt n q2 Hq2'.
  case: i1 => [|q1].
  + rewrite /translate_state Hfi2 => E.
    have := f_equal fin_to_nat E; simpl.
    by have := nat_to_finK Hfi2; lia.
  + rewrite /translate_state Hfi2.
    case Hfi1: (nat_to_fin q1) => [fi1|].
    * move/FS_inj/FS_inj => Hfi.
      have := nat_to_finK Hfi1.
      have := nat_to_finK Hfi2.
      by rewrite Hfi; congruence.
    * move=> E.
      have := f_equal fin_to_nat E; simpl.
      by have := nat_to_finK Hfi2; lia.
Qed.

Local Lemma mm2_config_inj s s2 :
  fst s2 ≤ n →
  mm2_config s = mm2_config s2 → s = s2.
Proof.
move=> Hle /config_word_inj [Ha [Hb Hq]].
have Hpc := translate_state_inj Hle Hq.
case: s Ha Hb {Hq} Hpc => [i [a b]]
  /= -> -> ->;
  case: s2 Hle => [? [??]] /=.
by move=> _.
Qed.

Local Lemma proj_elem q : Unit [mm_q q] ⊑ ⨆ q ∈ enum Q, Unit [mm_q q].
Proof. exact: sqsubseteq_join_list (elem_of_enum _). Qed.

Lemma encode_proj1_le q :
  q ∈ active_states →
  ka_term_proj1 (encode_instr next_state q (mm2_prog q)) ⊑ C.
Proof.
move=> active_q;
rewrite /C /config_set; case: (mm2_prog q) => [||q'|q'] /=;
rewrite ?(monoid_morphism_mul, semi_lattice_morphism_join,
          join_sqsubseteq, right_id, left_id) /= -1?lock; try split.
- by rewrite -sqsubseteq_join_list.
- by rewrite -sqsubseteq_join_list.
- by rewrite -[star (Unit [mm_a])]pre_ka_one_star left_id
    -sqsubseteq_join_list.
- by rewrite pre_ka_mul_star -sqsubseteq_join_list.
- by rewrite -[star (Unit [mm_b])]pre_ka_one_star right_id
    -sqsubseteq_join_list.
- by rewrite -assoc pre_ka_mul_star -sqsubseteq_join_list.
Qed.

Lemma encode_proj2_le q :
  ka_term_proj2 (encode_instr next_state q (mm2_prog q)) ⊑ T.
Proof.
rewrite /T /config_set [enum]lock; case: (mm2_prog q) => [||q'|q'] /=;
rewrite ?(monoid_morphism_mul, semi_lattice_morphism_join,
          join_sqsubseteq, right_id, left_id) /= -1?lock; try split.
- by rewrite pre_ka_mul_star -(proj_elem (next_state q)).
- by rewrite -(pre_ka_mul_star (Unit [mm_b])) assoc -(proj_elem (next_state q)).
- by rewrite -(pre_ka_one_star (Unit [mm_a])) left_id -(proj_elem (next_state q)).
- by rewrite -(proj_elem q').
- by rewrite -(pre_ka_one_star (Unit [mm_b])) right_id -proj_elem.
- by rewrite -proj_elem.
Qed.

Lemma mm2_R_ub1 : ka_term_proj1 mm2_R ⊑ C.
Proof.
rewrite /mm2_R /transition_rel
  semi_lattice_morphism_join_list.
apply/join_list_sqsubseteq => q active_q.
exact: encode_proj1_le.
Qed.

Lemma C_T : C ⊑ T.
Proof.
rewrite /C /T /config_set.
apply: pre_ka_mul_mono => //.
apply/join_list_sqsubseteq => q q_active.
exact: sqsubseteq_join_list (elem_of_enum _).
Qed.

Lemma mm2_R_ub1' : ka_term_proj1 mm2_R ⊑ T.
Proof. by rewrite -C_T; exact: mm2_R_ub1. Qed.

Lemma mm2_R_ub2 : ka_term_proj2 mm2_R ⊑ T.
Proof.
rewrite /mm2_R /transition_rel
  semi_lattice_morphism_join_list.
apply/join_list_sqsubseteq => q _.
exact: encode_proj2_le.
Qed.

Lemma repr_rel_mm2_R : repr_rel (pad_rel mm2_R) (pad_lang T).
Proof.
apply: bounded_output_repr_rel'.
- apply: finite_state_join_list => q active_q.
  by case: (mm2_prog q) => //= *; apply: finite_stateP.
- apply: bounded_output_join_list => q active_q.
  by case: (mm2_prog q) => //= *; apply: bounded_outputbP.
- exact: mm2_R_ub1'.
- exact: mm2_R_ub2.
Qed.

Definition red_lb s1 :=
  Unit (1, map Some (mm2_config s1) ⋅ [None]) ⋅ star (pad_rel mm2_R).

Definition red_ub :=
  dpseudo_top ⋅ ka_term_inj2 (pad_lang partially_accepted)
  ⊔ repr_rel_rtc_error repr_rel_mm2_R.

Lemma mm2_R_soundness_aux s1 s2 :
  rtc (mm2_step P) s1 s2 →
  red_lb s1 ⊑ red_ub →
  s2 = (0,(0,0)) ∨ 0 < s2.1 ≤ n.
Proof.
rewrite /red_ub /repr_rel_rtc_error -assoc.
move=> /encoding_rtc_complete s1_s2 ub.
have pa: Unit (mm2_config s2) ⊑ partially_accepted.
{ exact: repr_rel_rtc_soundness' s1_s2 ub. }
rewrite -elem_of_C comm -!l_alt /= in pa *; case: pa => pa; eauto.
right; move/leibniz_equiv_iff: pa; rewrite /mm2_config /config_word /=.
by case: (s2) => [[|?] [[|?] [|?]]] //=.
Qed.

Lemma mm2_stop_spec s : mm2_stop P s ↔ ¬ (0 < index s ≤ n).
Proof.
case: s=> [i [a b]]; split.
- move=> s_stop s_bounds; case e: (mm2_step_fun (i,(a,b))) => [s'|].
  + by apply: (s_stop s'); apply/mm2_step_fun_spec.
  + rewrite /mm2_step_fun /mm2_atom_fun /= in e s_bounds.
    case: i {s_stop} => [|i] in e s_bounds; first lia.
    case P_i: nth_error => [ρ|] //= in e *.
    move/nth_error_None in P_i; lia.
- move=> /= s_bounds s' /mm2_step_fun_spec.
  rewrite /mm2_step_fun /mm2_atom_fun /=.
  case: i => [|i] //= in s_bounds *.
  case P_i: nth_error => [ρ|] //.
  have: i < n by apply/nth_error_Some; congruence.
  lia.
Qed.

Lemma mm2_R_soundness s1 s2 :
  rtc (mm2_step P) s1 s2 →
  mm2_stop P s2 →
  red_lb s1 ⊑ red_ub →
  s2 = (0,(0,0)).
Proof.
move=> s1_s2 /mm2_stop_spec s2_stop red_leq.
have [//|] := mm2_R_soundness_aux s1_s2 red_leq.
congruence.
Qed.

Lemma mm2_step_det s s1 s2 :
  mm2_step P s s1 → mm2_step P s s2 → s1 = s2.
Proof.
move/mm2_step_fun_spec => H1 /mm2_step_fun_spec.
by rewrite H1; case.
Qed.

Lemma no_step_from_halt w :
  ¬ Unit (mm2_config (0,(0,0)), w) ⊑ mm2_R.
Proof.
move=> /encoding_sound [s2 [_ Hstep]].
move/mm2_step_fun_spec: Hstep.
by rewrite /mm2_step_fun /=.
Qed.

Lemma mm2_R_completeness s1 :
  rtc (mm2_step P) s1 (0,(0,0)) →
  red_lb s1 ⊑ red_ub.
Proof.
move=> /encoding_rtc_complete xs_ys.
rewrite /red_lb /red_ub /partially_accepted pad_lang_join.
have ->: pad_lang (Unit (mm2_config (0,(0,0))))
         ≡ Unit (map Some (mm2_config (0,(0,0))) ⋅ [None]).
{ by rewrite /pad_lang /= monoid_morphism_mul. }
apply: repr_rel_iter_final xs_ys.
- apply: elem_of_T.
- apply: mm2_R_ub1.
- move=> xs ys1 ys2 xs_ys1 xs_ys2.
  have: Unit xs ⊑ ka_term_proj1 mm2_R by rewrite -xs_ys1.
  rewrite mm2_R_ub1 C_T; case/elem_of_T_inv=> s xs_s.
  rewrite xs_s in xs_ys1 xs_ys2.
  case/encoding_sound: xs_ys1 => s1' [] ys1_s1' s_s1'.
  case/encoding_sound: xs_ys2 => s2' [] ys2_s2' s_s2'.
  have := mm2_step_det s_s1' s_s2'; congruence.
- exact: no_step_from_halt.
Qed.

End MM2Adapter.
