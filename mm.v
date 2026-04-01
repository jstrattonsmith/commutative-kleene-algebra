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

(** Running or accepted *)

Definition partially_accepted :=
  C ⊔ Unit (config_word 0 0 Fin.F1).

(** The transition relation for a concrete MM2 program. *)

Definition mm2_R := transition_rel next_state mm2_prog active_states.

(** Encode an MM2 state as a configuration word. *)

Definition mm2_config (s : mm2_state) : list (mm_sym Q) :=
  config_word (fst (snd s)) (snd (snd s)) (translate_state (fst s)).

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

(** ** The encoding faithfully represents the transitions of a Minsky machine (~
Lemma 14). *)

Lemma encoding_complete s1 s2 :
  mm2_step P s1 s2 →
  Unit (mm2_config s1, mm2_config s2) ⊑ mm2_R.
Proof. Admitted.

Lemma encoding_sound s1 w :
  Unit (mm2_config s1, w) ⊑ mm2_R →
  ∃ s2, w = mm2_config s2 ∧ mm2_step P s1 s2.
Proof. Admitted.

Lemma encoding_rtc_complete s1 s2 :
  rtc (mm2_step P) s1 s2 →
  rtc (λ xs ys, Unit (xs, ys) ⊑ mm2_R)
    (mm2_config s1) (mm2_config s2).
Proof.
elim=> // x y z xy _ IH.
apply: rtc_l _ IH; exact: encoding_complete xy.
Qed.

Lemma encoding_rtc_sound s1 ys :
  rtc (λ xs ys, Unit (xs, ys) ⊑ mm2_R)
    (mm2_config s1) ys →
  ∃ s2, ys = mm2_config s2 ∧
    rtc (mm2_step P) s1 s2.
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

Local Lemma proj_elem q :
  Unit [mm_q q] ⊑
    join_list (λ q0 : Q, Unit [mm_q q0]) (enum Q).
Proof. exact: sqsubseteq_join_list (elem_of_enum _). Qed.

Local Lemma proj_elem' q :
  Unit [mm_q q] ⊑
    ⨆ q0 ∈ enum Q, Unit [mm_q q0].
Proof. exact: proj_elem. Qed.

Local Ltac finish_proj :=
  rewrite ?assoc;
  repeat (first
    [ exact: proj_elem | reflexivity
    | refine (pre_ka_mul_mono _ _)
    | apply: transitivity (pre_ka_mul_star _);
      refine (pre_ka_mul_mono _ _)
    | apply: transitivity (pre_ka_one_star _) ]).

Lemma encode_proj1_le q :
  ka_term_proj1 (encode_instr next_state q
    (mm2_prog q)) ⊑ T.
Proof.
rewrite /T /config_set.
case: (mm2_prog q) => [||q'|q'] /=;
  rewrite ?semi_lattice_morphism_join
    ?join_sqsubseteq;
  repeat split;
  rewrite /ka_term_proj1 /sym_l /sym_r /star_d
    /ka_term_map /= ?left_id ?right_id;
  finish_proj. admit. admit.
Admitted.

Lemma encode_proj2_le q :
  ka_term_proj2 (encode_instr next_state q
    (mm2_prog q)) ⊑ T.
Proof.
rewrite /T /config_set.
case: (mm2_prog q) => [||q'|q'] /=;
  rewrite ?semi_lattice_morphism_join
    ?join_sqsubseteq;
  repeat split;
  rewrite /ka_term_proj2 /sym_l /sym_r /star_d
    /ka_term_map /= ?left_id ?right_id;
  finish_proj. admit. admit.
Admitted.

Lemma mm2_R_ub1 : ka_term_proj1 mm2_R ⊑ T.
Proof.
rewrite /mm2_R /transition_rel
  semi_lattice_morphism_join_list.
apply/join_list_sqsubseteq => q _.
exact: encode_proj1_le.
Qed.

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
- exact: mm2_R_ub1.
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

Lemma mm2_R_completeness s1 :
  rtc (mm2_step P) s1 (0,(0,0)) →
  red_lb s1 ⊑ red_ub.
Proof.
move=> /encoding_rtc_complete /pad_rel_rtc_1 /rtc_nsteps [m xs_ys].
have s1_T: Unit (mm2_config s1) ⊑ T by exact: elem_of_T.
have term: next_iter repr_rel_mm2_R (S m) [map Some (mm2_config s1) ⋅ [None]] = [].
{ admit. }
have := repr_rel_iter_empty' s1_T term.
rewrite strings_r_alt; set X := next_lt _ _ _ => red_leq.
apply: transitivity red_leq _; apply: join_mono => //.
apply: pre_ka_mul_mono => //.
apply: semi_lattice_morphism_sqsubseteq_proper.
admit.
Admitted.

End MM2Adapter.
