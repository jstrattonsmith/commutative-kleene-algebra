(* The direct route for the second encoding: balanced universality in
   pre-KA (Universality/UnivEncoding.v). A divergent run refutes
   bal_star ⊑ univ_ub_mm2 P s1 (univ_not_le_of_not_terminates). So, as for
   red_leq, the inequality holds exactly when the run reaches (0,(0,0))
   (univ_leq_complete/univ_leq_sound), and balanced universality is
   undecidable by a direct reduction from MM2_HALTS_ON_ZERO
   (Univ_EQ_undec), with no effective inseparability, CT_L or MP.

   bal_star occurs on the left and also as a prefix of the detectors on
   the right, so DirectUndec/OmegaModel.v's absorbing tokens cannot tell
   the two sides apart; this file uses DirectUndec/TailModel.v instead. The
   run is the infinite word W = # c0 # c1 # ..., one balanced letter per
   step. Its token (1, 0, 1) lies in bal_star. In univ_ub it could only
   come from a balanced detector word occurring in a prefix of W, and the
   language-level soundness lemmas of UnivEncoding.v (win_sound,
   nobad_run, run_parse) rule that out for valid runs. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite relations.
From Stdlib Require Import Lia Relation_Operators Operators_Properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.
From kacc Require Import CKAUndec.Encoding CKAUndec.Glue.RtcBridge.
From kacc Require Import DirectUndec.OmegaModel DirectUndec.TailModel.
From kacc Require DirectUndec.NonHalting.
From kacc Require Import Universality.balanced Universality.UnivEncoding.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper.
From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.Synthetic Require Import Definitions ReducibilityFacts.
Require Undecidability.Synthetic.Undecidability.
Require Undecidability.TM.SBTM_undec.
From kacc Require DirectUndec.Undec.
Import MM2Notations.

Section UnivDirect.

Variable P : list mm2_instr.
Variable s1 : mm2_state.
Hypothesis nt : ¬ mm2_terminates P s1.

Notation Q := (fin (S (S (length P)))).
Notation L := (option_setoid (@mm_sym_setoid Q)).
Notation M := (prod_monoid (list_monoid L) nat_add_monoid).
Notation term := (ka_term M).
Notation hash := (None : L).
Notation prog := (@mm2_prog P).
Notation nxt := (@next_state P).
Notation acts := (active_states P).
Notation q0 := (Fin.F1 : Q).
Notation bstar := (bal_star (A := L)).

(** * The infinite run as a word *)

Definition cj (j : nat) : uconf := uconf_of P (NonHalting.run P s1 j).

Fixpoint cs_from (k n : nat) : list uconf :=
  match n with
  | 0 => [cj k]
  | S n => cj k :: cs_from (S k) n
  end.

Lemma chain_from k n : uchain prog nxt acts (cs_from k n).
Proof.
elim: n k => [|n IH] k //=.
have [_ step] := NonHalting.run_step nt k.
case: (step_uconf step) => act e.
case: n IH => [|n] IH /=; split => //; split => //; exact: (IH (S k)).
Qed.

Lemma cs_from_snoc k n : cs_from k (S n) = cs_from k n ++ [cj (k + S n)].
Proof.
elim: n k => [|n IH] k; first by rewrite /= Nat.add_1_r.
change (cj k :: cs_from (S k) (S n) =
        (cj k :: cs_from (S k) n) ++ [cj (k + S (S n))]).
rewrite IH; have -> : k + S (S n) = S k + S n by lia.
done.
Qed.

Lemma elem_cs_from c k n : c ∈ cs_from k n → ∃ j, c = cj j.
Proof.
elim: n k => [|n IH] k /=.
- by move/elem_of_list_singleton => ->; exists k.
- by case/elem_of_cons => [->|/IH //]; exists k.
Qed.

Definition Wl (m : nat) : list L := UnivEncoding.run (cs_from 0 m).

Lemma Wl_S m : Wl (S m) = Wl m ++ uword (cj (S m)) ++ [hash].
Proof. by rewrite /Wl cs_from_snoc run_snoc. Qed.

Lemma Wl_len m : m < length (Wl m).
Proof.
elim: m => [|m IH].
- by rewrite /Wl /UnivEncoding.run /=; lia.
- rewrite Wl_S !length_app; move: IH; set n := length (Wl m).
  clearbody n => h; simpl; lia.
Qed.

Lemma Wl_prefix m d : ∃ z, Wl (m + d) = Wl m ++ z.
Proof.
elim: d => [|d [z e]]; first by exists []; rewrite Nat.add_0_r app_nil_r.
exists (z ++ uword (cj (S (m + d))) ++ [hash]).
by rewrite Nat.add_succ_r Wl_S e -app_assoc.
Qed.

Definition W (j : nat) : L := default hash (Wl j !! j).

Lemma lookup_Wl j m : j < length (Wl m) → Wl m !! j = Some (W j).
Proof.
move=> jm; rewrite /W.
case: (Wl_prefix j m) => z1 e1; case: (Wl_prefix m j) => z2 e2.
have hj := Wl_len j.
have [x hx] : is_Some (Wl j !! j) by apply: lookup_lt_is_Some_2.
rewrite hx /=.
have : Wl (j + m) !! j = Some x by rewrite e1; apply: lookup_app_l_Some.
rewrite Nat.add_comm e2 => /(lookup_app_Some _ _ _ _) [//|[hlen _]]; lia.
Qed.

Definition Wpref (k : nat) : list L := W <$> seq 0 k.

Lemma Wl_pref k : ∃ z, Wl k = Wpref k ++ z.
Proof.
exists (drop k (Wl k)); rewrite -{1}(take_drop k (Wl k)); f_equal.
apply: list_eq => i; rewrite /Wpref list_lookup_fmap.
case: (decide (i < k)) => ik.
- rewrite lookup_take // lookup_seq_lt //= lookup_Wl //.
  by have := Wl_len k; lia.
- rewrite lookup_take_ge; first lia.
  by rewrite lookup_seq_ge /=; first lia.
Qed.

Lemma W_hash_inf k : ∃ j, k ≤ j ∧ W j = hash.
Proof.
set j := length (Wl k ++ uword (cj (S k))).
have eS : Wl (S k) = (Wl k ++ uword (cj (S k))) ++ [hash].
{ by rewrite Wl_S app_assoc. }
have hj : j < length (Wl (S k)).
{ rewrite eS length_app /j.
  move: (length (Wl k ++ uword (cj (S k)))) => X; simpl; lia. }
exists j; split.
- rewrite /j length_app; have := Wl_len k.
  move: (length (Wl k)) (length (uword _)) => X Y; lia.
- have := lookup_Wl hj; rewrite eS list_lookup_middle //.
  by case.
Qed.

(** * The model *)

Definition rr (j : nat) : M := ([W j], 1%nat).

Lemma M_unit_split (x y : M) : x ⋅ y ≡ 1 → x ≡ 1 ∧ y ≡ 1.
Proof.
case: x y => [u a] [v b] /M_equiv_eq [/app_eq_nil [-> ->] ab].
rewrite nat_add_mulE nat_add_oneE in ab.
have ea : a = 0%nat by lia.
have eb : b = 0%nat by lia.
by split; apply: M_eq_equiv; rewrite ?ea ?eb.
Qed.

Notation D e := (tl (tden rr e)).

Lemma rseg_W k n : rseg rr k n = ((W <$> seq k n), n).
Proof.
elim: n k => [|n IH] k //=.
by rewrite IH.
Qed.

Lemma tsim_run_prefix (x : M) k :
  tsim rr x k 1 0 → x.1 = Wpref k ∧ x.2 = k.
Proof.
case=> n [n' [/= e /M_equiv_eq]].
rewrite !rseg_W; case: x => w a /= [ew ea].
rewrite nat_add_mulE in ea; rewrite nat_add_oneE nat_add_mulE in ea.
subst n'.
split; last by lia.
move: ew; rewrite /mul /= /Wpref seq_app fmap_app.
by move/app_inv_tail.
Qed.

(** * Token-freeness of the detectors *)

Lemma tokfree_wstar t k' : t ≠ hash → tokfree (D (star (Unit ([t], k')))).
Proof.
move=> th; apply: tokfree_tden_star; first exact: tokfree_tden_unit.
move=> k; case: (W_hash_inf k) => j [kj hj]; exists j; split => //.
by move=> /M_equiv_eq [e _]; apply: th; rewrite -hj e.
Qed.

Ltac tf :=
  repeat match goal with
  | |- tokfree (D (join_list _ _)) => apply: tokfree_tden_join_list => ?
  | |- tokfree (D (_ ⊔ _)) => apply: tokfree_tden_join
  | |- tokfree (D (_ ⋅ _)) => apply: tokfree_tden_mul
  | |- tokfree (D (Unit _)) => apply: tokfree_tden_unit
  | |- tokfree (D 1) => apply: tokfree_tden_unit
  | |- tokfree (D ⊥) => apply: tokfree_tden_bottom
  | |- tokfree (D (star (Unit ([?t], _)))) => apply: tokfree_wstar; done
  | |- tokfree (D (if ?b then _ else _)) => case: b
  | |- tokfree (D (wl _ _)) => apply: tokfree_tden_unit
  | |- tokfree (D (cst _)) => apply: tokfree_tden_unit
  | |- tokfree (D (balanced.bal _)) => apply: tokfree_tden_unit
  | |- tokfree (D (wstar _ _)) => rewrite /wstar /wl
  | |- tokfree (D (gw _ _ _)) => rewrite /gw /wstar /wl
  | |- tokfree (D (gs _ _)) => rewrite /gs /wstar /wl
  | |- tokfree (D (match ?b with _ => _ end)) => case: b
  end.

Lemma tokfree_e_win : tokfree (D (e_win prog nxt acts)).
Proof.
rewrite /e_win /w_all /w_ctrl /w_ma /w_fa /w_mb /w_fb /head /gw /gs.
rewrite /wstar /wl /cst /qall /qbut; tf.
Qed.

Lemma tokfree_E :
  tokfree (D (e_halt0 q0 ⊔ e_shape ⊔ e_win prog nxt acts)).
Proof.
apply: tokfree_tden_join; last exact: tokfree_e_win.
rewrite /e_halt0 /e_shape /balanced.bal; tf.
Qed.

Lemma tokfree_init_errs pre w : tokfree (D (init_errs pre w)).
Proof.
elim: w pre => [|t0 w IH] pre; first exact: tokfree_tden_bottom.
change (tokfree (D ((⨆ t ∈ enum L,
          if bool_decide (t = t0) then ⊥ else balanced.bal (pre ++ [t]))
        ⊔ init_errs (pre ++ [t0]) w))).
apply: tokfree_tden_join; last exact: IH.
tf.
Qed.

Lemma tokfree_bal_gen : tokfree (D (bal_gen (A := L))).
Proof. rewrite /bal_gen /balanced.bal; tf. Qed.

(** * Detector words are not empty *)

Lemma l_E_nonempty :
  ¬ l (e_halt0 q0 ⊔ e_shape ⊔ e_win prog nxt acts) (1 : M).
Proof.
case=> [[/l_bal_eq [] //|/l_e_shape [x [y [] //]]]|].
case/l_e_win => q [za [zb [_ H]]].
move: H => /l_join [/l_join [/l_join [/l_join [H|H]|H]|H]|H].
- case/(l_w_ctrl prog nxt q0): H => ? [? [? [? [e _]]]]; discriminate e.
- case/(l_w_ma prog nxt q0): H => ? [? [? [e _]]]; discriminate e.
- case/(l_w_fa prog nxt q0): H => ? [? [? [? [e _]]]]; discriminate e.
- case/(l_w_mb prog nxt q0): H => ? [? [? [? [? [e _]]]]]; discriminate e.
- case/(l_w_fb prog nxt q0): H => ? [? [? [? [? [e _]]]]]; discriminate e.
Qed.

(** * Balanced detector words do not occur in the run *)

Lemma run_halt0_free m u z :
  Wl m = u ++ hash :: uword (0, q0, 0) ++ hash :: z → False.
Proof.
case/(run_parse prog nxt q0) => cs1 [cs2 [e _]].
have : (0, q0, 0) ∈ cs_from 0 m by rewrite e; set_solver.
case/elem_cs_from => j ej.
have h := uconf_of_halt0 (eq_sym ej).
have [_ step] := NonHalting.run_step nt j.
move: step; rewrite h => - [ρ [hat _]].
by have := MM2_facts.mm2_instr_at_bounds hat; simpl; lia.
Qed.

Lemma prefix_e_pre m w z :
  l (e_pre prog nxt acts q0 (cj 0)) (w, length w) →
  Wl m = w ++ z → False.
Proof.
move=> H eW.
have Hc := chain_from 0 m.
case/l_join: H => [H|H].
- case/l_init_errs_inv: H => p [t0 [r [t [Ei [Ht Ew]]]]].
  have [rest erest] : ∃ rest, cs_from 0 m = cj 0 :: rest.
  { by case: (m) => [|?]; eexists. }
  move: eW; rewrite /Wl erest run_cons Ei Ew -!app_assoc /=.
  by move=> /app_inv_head [] E _; case: (Ht (eq_sym E)).
- case/(l_pad prog nxt q0): H => u [v [Ew H]].
  rewrite Ew -app_assoc in eW.
  case/l_join: H => [/l_join [H|H]|H].
  + case/l_bal_eq: H => Ev _; subst v.
    apply: (run_halt0_free (m := m) (u := u) (z := z)).
    by rewrite eW.
  + case/l_e_shape: H => x [y [Ev [_ Hb]]]; subst v.
    have := nobad_spec (u := u) (x := x) (y := y) (z := z).
    by rewrite Hb -eW => /(_ (nobad_run _)).
  + case/l_e_win: H => q [za [zb [Hq H]]].
    exact: (win_sound q0 Hc Hq eW H).
Qed.

Lemma head_list_nonempty :
  ¬ l (⨆ q ∈ acts, head q (wstar (Some mm_a) 1) (wstar (Some mm_b) 1))
      (([] : list L), 0%nat).
Proof.
case/l_join_list => q [_ H].
case/(l_head prog nxt): H => ? [? [? [? [e _]]]].
discriminate e.
Qed.

(** * The refutation *)

Lemma tden_bstar_tok : D bstar (TTok 1 0 1).
Proof.
exists 1, (TTok 1 0 1); split; first by rewrite left_id.
split; first by exists 0; simpl; reflexivity.
right; exists (TTok 1 0 1), 1; split; first by rewrite right_id.
split; last by exists 0; simpl; reflexivity.
exists 0; split; first reflexivity.
move=> j _; apply: (proj2 (TailModel.den_fin rr bal_gen (rr j))).
rewrite /bal_gen.
apply/l_join_list; exists (W j); split; first exact: elem_of_enum.
by apply/l_bal_eq.
Qed.

Lemma not_pre_bstar_X X h :
  tokfree (D X) → ¬ l X 1 → ∀ p, D (bstar ⋅ X) p → ¬ PreT rr h p.
Proof.
move=> tX nX p Dp Pp.
case: (pre_mul M_unit_split Dp Pp) => [[a [p' [_ [Dp' Pp']]]]|[p' [_ [_ D1]]]].
- by case: Pp' => t [k [ep _]]; apply: (tX t k 1); rewrite -ep.
- by apply: nX; apply/(TailModel.den_fin rr).
Qed.

Theorem univ_not_le_of_not_terminates : ¬ bstar ⊑ univ_ub_mm2 P s1.
Proof.
move=> le.
have tok := tden_le le tden_bstar_tok.
have P0 : PreT rr 1 (TTok 1 0 1).
{ exists 1, 0; split; first reflexivity.
  by apply: tsim_equiv; rewrite left_id. }
move: tok; rewrite /univ_ub_mm2 /univ_ub.
case=> [He|Hp].
- rewrite /e_end in He.
  case: He => [[[H|H]|H]|H].
  + by case: P0 => t [k [ep _]]; move: H; rewrite ep; apply: tokfree_tden_unit.
  + by case: P0 => t [k [ep _]]; move: H; rewrite ep; apply: tokfree_tden_unit.
  + change (D (bstar ⋅ (⨆ t ∈ enum L,
        if bool_decide (t = hash) then ⊥ else balanced.bal [t]))
        (TTok 1 0 1)) in H.
    move: H P0; apply: not_pre_bstar_X.
    * tf.
    * case/l_join_list => t [_]; case: bool_decide => //.
      by case/l_bal_eq.
  + change (D (bstar ⋅ (⨆ q ∈ acts,
        head q (wstar (Some mm_a) 1) (wstar (Some mm_b) 1)))
        (TTok 1 0 1)) in H.
    move: H P0; apply: not_pre_bstar_X.
    * rewrite /head /wstar /wl; tf.
    * exact: head_list_nonempty.
- case: (pre_mul M_unit_split Hp P0)
    => [[a [p' [Ha [Hp' Pp']]]]|[p' [Hp' [Pp' _]]]].
  + case: (pre_star M_unit_split tokfree_bal_gen Hp' Pp')
      => f [k [hf [_ hk]]].
    have {}Ha :=
      proj1 (TailModel.den_fin rr (e_pre prog nxt acts q0 (cj 0)) a) Ha.
    have /l_bal_star /= hf' : l bstar f.
    { apply: (proj1 (TailModel.den_fin rr bstar f)).
      exists (TFin f), 1; split; first by rewrite right_id.
      split => //; left; simpl; reflexivity. }
    clear Pp' Hp'.
    case: a Ha hk => w wa Ha; case: f hf hf' => v va _ /= hf' hk.
    case/tsim_run_prefix: hk => /= ew ewa.
    rewrite !nat_add_mulE nat_add_oneE in ewa.
    have lk : length (w ++ v) = k.
    { by rewrite -[w ++ v]/(w ⋅ v) ew /Wpref length_fmap length_seq. }
    rewrite length_app in lk.
    have wa_len : wa = length w by lia.
    rewrite wa_len in Ha.
    case: (Wl_pref k) => z ez.
    apply: (prefix_e_pre (m := k) (z := v ++ z) Ha).
    by rewrite ez -ew /mul /= -app_assoc.
  + have Hp'' : D (init_errs [] (UnivEncoding.run [cj 0])
                  ⊔ bstar ⋅ (e_halt0 q0 ⊔ e_shape ⊔ e_win prog nxt acts)) p'.
    { exact: Hp'. }
    case: Hp'' => [H|H].
    * case: Pp' => t [k [ep _]].
      move: H; rewrite ep => H.
      exact (@tokfree_init_errs [] (UnivEncoding.run [cj 0]) t k 1 H).
    * exact: (not_pre_bstar_X tokfree_E l_E_nonempty H Pp').
Qed.

End UnivDirect.

(** * The characterization and the reduction *)

Theorem univ_leq_complete P s1 :
  clos_refl_trans _ (mm2_step P) s1 (0,(0,0)) →
  bal_star (A := option_setoid (@mm_sym_setoid (fin (S (S (length P))))))
    ⊑ univ_ub_mm2 P s1.
Proof. move=> reach; exact: univ_completeness (crt_to_rtc _ _ _ reach). Qed.

Theorem univ_leq_sound P s1 :
  ¬ clos_refl_trans _ (mm2_step P) s1 (0,(0,0)) →
  ¬ bal_star (A := option_setoid (@mm_sym_setoid (fin (S (S (length P))))))
      ⊑ univ_ub_mm2 P s1.
Proof.
move=> nreach le.
have nterm : ¬ mm2_terminates P s1.
{ case=> s2 [reach stop]; apply: nreach.
  by rewrite -(univ_soundness (crt_to_rtc _ _ _ reach) stop le). }
exact: (univ_not_le_of_not_terminates nterm le).
Qed.

(** Balanced universality, with the alphabet of the machine as part of the
    instance (as in Universality/UnivMComplete.v's [Univ c]). *)

Definition UnivM (P : list mm2_instr) : monoid :=
  prod_monoid
    (list_monoid (option_setoid (@mm_sym_setoid (fin (S (S (length P)))))))
    nat_add_monoid.

Definition UNIV (x : { P : list mm2_instr & ka_term (UnivM P) }) : Prop :=
  bal_star ⊑ projT2 x.

Definition mm2_to_univ (x : MM2_PROBLEM) :
    { P : list mm2_instr & ka_term (UnivM P) } :=
  match x with (P, a, b) => existT P (univ_ub_mm2 P (1%nat, (a, b))) end.

Lemma reduction_univ_yes x : MM2_HALTS_ON_ZERO x → UNIV (mm2_to_univ x).
Proof. case: x => [[P a] b]; exact: univ_leq_complete. Qed.

Lemma reduction_univ_no x : ¬ MM2_HALTS_ON_ZERO x → ¬ UNIV (mm2_to_univ x).
Proof. case: x => [[P a] b]; exact: univ_leq_sound. Qed.

Theorem UNIV_undec : Undecidability.undecidable UNIV.
Proof.
move=> [d hd].
apply: SBTM_undec.complement_SBTM_HALT_undec.
apply: (dec_red (reduces_complement Undec.SBTM_HALT_to_MM2_HALTS_ON_ZERO)).
exists (λ x, negb (d (mm2_to_univ x))) => x.
rewrite /reflects /complement; split.
- move=> nh; case e: (d (mm2_to_univ x)) => //.
  by exfalso; apply: (reduction_univ_no nh); apply/hd.
- case e: (d (mm2_to_univ x)) => //= _ h.
  by move: e; have /hd -> := reduction_univ_yes h.
Qed.

Theorem UNIV_MP_reduction : Undec.MP → MM2_HALTS_ON_ZERO ⪯ UNIV.
Proof.
move=> mp; exists mm2_to_univ => x; split; first exact: reduction_univ_yes.
case: x => [[P a] b] u.
apply/Undec.HALTS_ON_ZERO_search; apply: mp => nex.
apply: (reduction_univ_no _ u) => hoz; apply: nex.
by apply/Undec.HALTS_ON_ZERO_search.
Qed.
