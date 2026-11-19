(* The direct reduction over the canonical binary alphabet: pre-KA term
   equality over the fixed carrier Tm_bin = list (option bool) *
   list (option bool) is undecidable (PreKA_EQ_bin_undec), with no
   effective inseparability, CT_L or MP.

   The binary encoding of the MM2 terms is CKAUndec/BinaryAlphabet.v's,
   with the concrete one-hot letter encoding enc_onehot of
   KA/BinaryAlphabetTransport.v (so that the reduction is a function). The
   completeness and soundness-for-halting-runs proofs below are adapted
   from BinaryAlphabet.v (mm2_R_completeness', mm2_R_soundness_aux'),
   which cannot be imported here: it imports CKAUndec/K.v and with it
   coq-synthetic-computability's effective-inseparability files. Its
   header comment records "a GENUINE OPEN GAP": red_leq' was not
   characterized for divergent runs, and the comment expects divergence
   to make the inequality hold "in spirit". In pre-KA it is the other way
   round: a divergent run refutes it (bin_not_le_of_not_terminates, an
   instance of DirectUndec/NonHalting.v's generic refutation), so red_leq'
   holds exactly when the run reaches (0,(0,0)). *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite relations.
From Stdlib Require Import Lia Relation_Operators Operators_Properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.automata
  KA.repr_rel KA.bounded_output.
From kacc Require Import KA.BinaryAlphabetTransport KA.BoundedOutputTransport.
From kacc Require Import CKAUndec.Encoding CKAUndec.Glue.RtcBridge.
From kacc Require Import DirectUndec.NonHalting.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.Synthetic Require Import Definitions ReducibilityFacts.
Require Undecidability.Synthetic.Undecidability.
Require Undecidability.TM.SBTM_undec.
From kacc Require DirectUndec.Undec.
Import MM2Notations.

(** * The binary terms of a machine *)

Section Bin.

Variable P : list mm2_instr.
Let QF : Type := fin (S (S (length P))).

Notation TAlph := (@Encoding.mm_sym_setoid QF).

Definition benc : TAlph → list bool := enc_onehot TAlph.
Definition bk : nat := length (enum (mm_sym QF)).

Global Instance benc_inj : Inj (=) (=) benc.
Proof. move=> x y; exact: enc_onehot_inj'. Qed.

Lemma benc_len x : length (benc x) = bk.
Proof. exact: enc_onehot_length. Qed.

Lemma bk_pos : 0 < bk.
Proof.
rewrite /bk; pose proof (elem_of_enum (A := mm_sym QF) mm_a) as h.
destruct (enum (mm_sym QF)) as [|y ys]; last (simpl; lia).
by apply elem_of_nil in h.
Qed.

Definition Mm2RMonoid : monoid :=
  prod_monoid (list_monoid TAlph) (list_monoid TAlph).

Lemma finite_stateb_mm2_R :
  @finite_stateb Mm2RMonoid _ (Encoding.mm2_R P) = true.
Proof.
apply: finite_stateb_join_list => q Hq.
by case: (Encoding.mm2_prog q).
Qed.

Lemma bounded_output_mm2_R : bounded_output (T := TAlph) (Encoding.mm2_R P).
Proof.
apply: bounded_output_join_list => q Hq.
by case: (Encoding.mm2_prog q) => *; apply: bounded_outputbP.
Qed.

Definition bin_R := Embed_pair benc (Encoding.mm2_R P).

Lemma repr_rel_bin :
  repr_rel (pad_rel bin_R) (pad_lang (Embed_word benc (Encoding.T P))).
Proof.
apply: bounded_output_repr_rel'.
- apply: finite_stateP.
  + done.
  + rewrite -(finite_stateb_transport TAlph bool_setoid benc bk benc_len bk_pos).
    apply/Is_true_true. exact: finite_stateb_mm2_R.
- exact: (bounded_output_transport TAlph bool_setoid benc bk benc_len bk_pos
           _ bounded_output_mm2_R).
- rewrite Embed_proj1_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: Encoding.mm2_R_ub1' P.
- rewrite Embed_proj2_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: Encoding.mm2_R_ub2 P.
Qed.

Definition bconf (s : mm2_state) : list bool :=
  enc_word benc (Encoding.mm2_config P s).

Definition bin_lb (s1 : mm2_state) :=
  Unit (1, map Some (bconf s1) ⋅ [None]) ⋅ star (pad_rel bin_R).

Definition bin_ub :=
  dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word benc (Encoding.partially_accepted P)))
    ⊔ repr_rel_rtc_error repr_rel_bin.

Lemma step_embed (x y : list TAlph) :
  Unit (x, y) ⊑ Encoding.mm2_R P →
  Unit (enc_word benc x, enc_word benc y) ⊑ bin_R.
Proof.
move=> Hxy.
have -> : Unit (enc_word benc x, enc_word benc y)
        = Embed_pair benc (Unit (x, y)) by [].
apply: semi_lattice_morphism_sqsubseteq_proper. exact: Hxy.
Qed.

Lemma rtc_embed (x y : list TAlph) :
  rtc (λ xs ys : list TAlph, Unit (xs, ys) ⊑ Encoding.mm2_R P) x y →
  rtc (λ xs ys, Unit (xs, ys) ⊑ bin_R) (enc_word benc x) (enc_word benc y).
Proof.
elim=> // x0 y0 z0 xy0 _ IH.
apply: rtc_l IH. exact: step_embed xy0.
Qed.

(** Adapted from CKAUndec/BinaryAlphabet.v's mm2_R_completeness'. *)

Lemma bin_complete (s1 : mm2_state) :
  rtc (mm2_step P) s1 (0, (0, 0)) → bin_lb s1 ⊑ bin_ub.
Proof.
move=> /Encoding.encoding_rtc_complete /rtc_embed xs_ys.
change (bin_lb s1 ⊑ dpseudo_top ⋅ ka_term_inj2
      (pad_lang (Embed_word benc (Encoding.C P) ⊔ Unit (bconf (0, (0, 0)))))
    ⊔ repr_rel_rtc_error repr_rel_bin).
rewrite pad_lang_join.
have -> : pad_lang (Unit (bconf (0, (0, 0))))
        ≡ Unit (map Some (bconf (0, (0, 0))) ⋅ [None]).
{ by rewrite /pad_lang /ka_term_map /repr_rel.lift /=
    (monoid_morphism_mul (f := Unit)). }
apply: repr_rel_iter_final xs_ys.
- have := Encoding.elem_of_T P s1.
  have -> : Unit (enc_word benc (Encoding.mm2_config P s1))
          = Embed_word benc (Unit (Encoding.mm2_config P s1)) by [].
  apply: semi_lattice_morphism_sqsubseteq_proper.
- rewrite Embed_proj1_natural.
  apply: semi_lattice_morphism_sqsubseteq_proper. exact: Encoding.mm2_R_ub1 P.
- move=> xs ys1 ys2 xs_ys1 xs_ys2.
  have [x1 [y1 [Ex1 [Ey1 Hin1]]]] :=
    Embed_pair_inv TAlph bool_setoid benc (Encoding.mm2_R P) xs ys1 xs_ys1.
  have [x2 [y2 [Ex2 [Ey2 Hin2]]]] :=
    Embed_pair_inv TAlph bool_setoid benc (Encoding.mm2_R P) xs ys2 xs_ys2.
  have Ex : x1 = x2.
  { apply: (enc_word_inj TAlph bool_setoid benc bk benc_len bk_pos).
    by rewrite -Ex1 -Ex2. }
  subst x2.
  have Hpx1 : Unit x1
      ⊑ @ka_term_proj1 (list_monoid TAlph) (list_monoid TAlph) (Encoding.mm2_R P)
    by rewrite -Hin1.
  rewrite (Encoding.mm2_R_ub1 P) (Encoding.C_T P) in Hpx1.
  case/Encoding.elem_of_T_inv: Hpx1 => s x1_s.
  rewrite x1_s in Hin1 Hin2.
  case/Encoding.encoding_sound: Hin1 => s1' [] y1_s1' s_s1'.
  case/Encoding.encoding_sound: Hin2 => s2' [] y2_s2' s_s2'.
  have Es : s1' = s2' by exact: MM2_facts.mm2_step_det s_s1' s_s2'.
  by rewrite Ey1 Ey2 y1_s1' y2_s2' Es.
- move=> ys' Hys'.
  have [x0 [y0 [Ex0 [Ey0 Hin0]]]] :=
    Embed_pair_inv TAlph bool_setoid benc (Encoding.mm2_R P) _ _ Hys'.
  have Ex0' : Encoding.mm2_config P (0, (0, 0)) = x0.
  { apply: (enc_word_inj TAlph bool_setoid benc bk benc_len bk_pos).
    exact: Ex0. }
  rewrite -Ex0' in Hin0.
  exact: Encoding.no_step_from_halt Hin0.
Qed.

(** Adapted from CKAUndec/BinaryAlphabet.v's mm2_R_soundness_aux'. *)

Lemma bin_sound_aux (s1 s2 : mm2_state) :
  rtc (mm2_step P) s1 s2 → bin_lb s1 ⊑ bin_ub →
  s2 = (0, (0, 0)) ∨ 0 < s2.1 ≤ length P.
Proof.
move=> /Encoding.encoding_rtc_complete /rtc_embed s1_s2.
rewrite /bin_ub /repr_rel_rtc_error -assoc => ub.
have pa : Unit (enc_word benc (Encoding.mm2_config P s2))
        ⊑ Embed_word benc (Encoding.partially_accepted P).
{ exact: repr_rel_rtc_soundness' s1_s2 ub. }
have [w [Ew Hw]] :=
  Embed_word_inv TAlph bool_setoid benc (Encoding.partially_accepted P) _ pa.
have Ew' : Encoding.mm2_config P s2 = w.
{ apply: (enc_word_inj TAlph bool_setoid benc bk benc_len bk_pos).
  exact: Ew. }
have pa0 : @sqsubseteq (ka_term (list TAlph)) _
             (Unit (Encoding.mm2_config P s2)) (Encoding.partially_accepted P).
{ rewrite Ew'. exact: Hw. }
have pa1 : @sqsubseteq (ka_term (list TAlph)) _
             (Unit (Encoding.mm2_config P s2)) (Encoding.C P)
         ∨ Encoding.mm2_config P s2 = Encoding.mm2_config P (0, (0, 0)).
{ move: pa0 => /l_alt.
  rewrite /Encoding.partially_accepted semi_lattice_morphism_join.
  case=> H.
  - left. apply/l_alt. exact: H.
  - right. move: H => /= H. exact: (proj1 (leibniz_equiv_iff _ _) H). }
case: pa1 => pa1.
- right. apply/Encoding.elem_of_C. exact: pa1.
- left.
  move: pa1.
  clear s1_s2 ub pa Ew Hw Ew' pa0.
  rewrite /Encoding.mm2_config /Encoding.config_word /=.
  by case: s2 => [[|?] [[|?] [|?]]] //=.
Qed.

Lemma bin_sound (s1 s2 : mm2_state) :
  rtc (mm2_step P) s1 s2 → mm2_stop P s2 → bin_lb s1 ⊑ bin_ub →
  s2 = (0, (0, 0)).
Proof.
move=> s1_s2 s2_stop le.
have [//|Hbad] := bin_sound_aux s1_s2 le.
exfalso; move/MM2_facts.mm2_stop_index_iff: s2_stop; lia.
Qed.

(** The new direction: divergent runs refute the inequality. *)

Lemma bconf_ne s : bconf s ≠ [].
Proof.
rewrite /bconf; move: (Encoding.mm2_config P s) (@mm2_config_ne P s).
case=> [//|y x] _; rewrite /enc_word /= => /(f_equal length).
rewrite /mul /= length_app benc_len; have := bk_pos; lia.
Qed.

Theorem bin_not_le_of_not_terminates s1 :
  ¬ mm2_terminates P s1 → ¬ bin_lb s1 ⊑ bin_ub.
Proof.
move=> nt.
apply: (chain_lb_not_le_chain_ub (R := repr_rel_bin)
          (c := λ j, bconf (run P s1 j))).
- move=> j; have [_ step] := run_step nt j.
  exact: step_embed (encoding_complete step).
- move=> j; exact: bconf_ne.
Qed.

Theorem bin_le_iff_sound s1 :
  ¬ clos_refl_trans _ (mm2_step P) s1 (0,(0,0)) → ¬ bin_lb s1 ⊑ bin_ub.
Proof.
move=> nreach le.
have nterm : ¬ mm2_terminates P s1.
{ case=> s2 [reach stop]; apply: nreach.
  by rewrite -(bin_sound (crt_to_rtc _ _ _ reach) stop le). }
exact: (bin_not_le_of_not_terminates nterm le).
Qed.

Theorem bin_le_iff_complete s1 :
  clos_refl_trans _ (mm2_step P) s1 (0,(0,0)) → bin_lb s1 ⊑ bin_ub.
Proof. move=> reach; exact: bin_complete (crt_to_rtc _ _ _ reach). Qed.

End Bin.

(** * Undecidability over the fixed binary carrier *)

Definition Tm_bin : monoid :=
  prod_monoid (list_monoid (option_setoid bool_setoid))
              (list_monoid (option_setoid bool_setoid)).

Definition PreKA_EQ_bin (p : ka_term Tm_bin * ka_term Tm_bin) : Prop :=
  p.1 ≡ p.2.

Definition mm2_to_eq_bin (x : MM2_PROBLEM) : ka_term Tm_bin * ka_term Tm_bin :=
  match x with
  | (P, a, b) => (bin_lb P (1%nat, (a, b)) ⊔ bin_ub P, bin_ub P)
  end.

Lemma reduction_bin_yes x : MM2_HALTS_ON_ZERO x → PreKA_EQ_bin (mm2_to_eq_bin x).
Proof.
case: x => [[P a] b] /= /bin_le_iff_complete /sqsubseteq_iff e.
exact: e.
Qed.

Lemma reduction_bin_no x : ¬ MM2_HALTS_ON_ZERO x → ¬ PreKA_EQ_bin (mm2_to_eq_bin x).
Proof.
case: x => [[P a] b] /= /bin_le_iff_sound nle e.
by apply: nle; apply/sqsubseteq_iff.
Qed.

Theorem PreKA_EQ_bin_undec : Undecidability.undecidable PreKA_EQ_bin.
Proof.
move=> [d hd].
apply: SBTM_undec.complement_SBTM_HALT_undec.
apply: (dec_red (reduces_complement Undec.SBTM_HALT_to_MM2_HALTS_ON_ZERO)).
exists (λ x, negb (d (mm2_to_eq_bin x))) => x.
rewrite /reflects /complement; split.
- move=> nh; case e: (d (mm2_to_eq_bin x)) => //.
  by exfalso; apply: (reduction_bin_no nh); apply/hd.
- case e: (d (mm2_to_eq_bin x)) => //= _ h.
  by move: e; have /hd -> := reduction_bin_yes h.
Qed.
