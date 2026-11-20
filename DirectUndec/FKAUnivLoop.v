(* Why DirectUndec/UnivDirect.v does not carry over to KA universality.

   Universality/UnivTop.v's full universality in the free KA,
   `FKA Σ* ⊑ FKA (univ_top_ub P s1)`, holds whenever the run from s1 is
   periodic, i.e. s1 lies on a cycle of the machine (fka_univ_top_cycle),
   although such a run never halts. So, as for red_leq in
   DirectUndec/FKALoop.v, the KA analogue of univ_not_le_of_not_terminates
   is false (fka_univ_top_not_terminates_fails, with FKALoop.v's
   two-instruction loop_prog), and no direct reduction from halting can be
   built on this encoding in KA.

   The proof is right star induction over `bal_star = bal_gen*`. With r the
   period of the run word (`rc`, one `# a^n q b^m` per configuration of the
   cycle), the invariant is

     r* ⋅ (⨆ i < |r|, take i r)  ⊔  e_pre c0 ⋅ bal_star,

   "a prefix of the infinite run word r r r ..., or a word already caught
   by a detector". Reading one more letter either continues the run word
   or deviates from it, and UnivEncoding.v's `detect` catches the
   deviation. The run word is infinite, but `r* ≤ 1 ⊔ r ⊔ bal_star ⋅ r ⋅ r`
   (star_unfold2) reduces everything to words with at most three periods:
   after two periods, the detector that fires (and the e_end component that
   accepts a prefix of the run) is padded with `bal_star` on the left,
   which absorbs the rest of the word. Both facts come from `detect` and
   `prefix_end` on the finite chain of three periods. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite fin relations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.ka.
From kacc Require Import Universality.balanced Universality.BalancedKA.
From kacc Require Import CKAUndec.Encoding Universality.UnivEncoding.
From kacc Require Import Universality.UnivTop DirectUndec.FKALoop.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

(** * Two KA facts *)

Section KAFacts.

Variable T : ka.
Implicit Types x z : T.

Lemma star_mul_self' x : star x ⋅ x ⊑ star x.
Proof.
by rewrite (ka_star_comm (x := x) (y := x)) //; exact: pre_ka_mul_star.
Qed.

(* Unfold a star twice, absorbing the rest into a larger star. *)
Lemma star_unfold2 x z : x ⊑ star z → star x ⊑ 1 ⊔ x ⊔ star z ⋅ x ⋅ x.
Proof.
move=> Hx; apply: ka_star_le; apply/join_sqsubseteq; split.
  by do 2 (etransitivity; last exact: sqsubseteq_join_left).
rewrite !pre_ka_right_dist right_id; apply/join_sqsubseteq; split.
  apply/join_sqsubseteq; split.
    by etransitivity; last exact: sqsubseteq_join_left;
       exact: sqsubseteq_join_right.
  etransitivity; last exact: sqsubseteq_join_right.
  rewrite -[x ⋅ x](left_id 1) assoc.
  by apply: pre_ka_mul_mono => //; apply: pre_ka_mul_mono => //;
     exact: pre_ka_one_star.
etransitivity; last exact: sqsubseteq_join_right.
rewrite !assoc; apply: pre_ka_mul_mono => //; apply: pre_ka_mul_mono => //.
exact: ka_mul_le_star.
Qed.

End KAFacts.

Lemma fka_join_list {M : monoid} {I} (f : I → ka_term M) xs :
  FKA (join_list f xs) = join_list (λ i, FKA (f i)) xs.
Proof. elim: xs => [//|i xs IH] /=; rewrite -IH; reflexivity. Qed.

(** * Universality of a periodic run in KA *)

Section Cycle.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.

Notation L := (option_setoid (@mm_sym_setoid Q)).
Notation M := (prod_monoid (list_monoid L) nat_add_monoid).
Notation term := (ka_term M).
Notation hash := (None : L).
Notation bstar := (bal_star (A := L)).

Variable prog : Q → mm_instr Q.
Variable nxt : Q → Q.
Variable acts : list Q.
Variable q0 : Q.

(* The start configuration c0 lies on the cycle c0, cs..., c0. *)
Variable c0 : @uconf Q.
Variable cs : list (@uconf Q).
Hypothesis Hcyc : uchain prog nxt acts (c0 :: cs ++ [c0]).

Notation ep := (e_pre prog nxt acts q0 c0).
Notation ee := (e_end (Q := Q) acts).

(* The period of the run word. *)
Definition rc : list L := flat_map (λ c, hash :: uword c) (c0 :: cs).

Lemma uchain_glue l1 c l2 :
  uchain prog nxt acts (l1 ++ [c]) → uchain prog nxt acts (c :: l2) →
  uchain prog nxt acts (l1 ++ c :: l2).
Proof.
elim: l1 => [//|a l1 IH] H1 H2.
case: l1 IH H1 => [|b l1] IH /= H1.
- by case: H1 => Ha [Ec _]; split; [|split].
- case: H1 => Ha [Eb H1]; split => //; split => //.
  exact: IH H1 H2.
Qed.

Definition ch : list (@uconf Q) :=
  c0 :: cs ++ c0 :: cs ++ c0 :: cs ++ [c0].

Lemma uchain_ch : uchain prog nxt acts ch.
Proof.
change (uchain prog nxt acts ((c0 :: cs) ++ c0 :: (cs ++ c0 :: cs ++ [c0]))).
apply: uchain_glue => //.
change (uchain prog nxt acts ((c0 :: cs) ++ c0 :: (cs ++ [c0]))).
exact: uchain_glue.
Qed.

Lemma run_app xs l :
  run (xs ++ l) = flat_map (λ c, hash :: uword c) xs ++ run l.
Proof.
elim: xs => [//|c xs IH]; rewrite /run in IH *.
by rewrite /= /cw -app_assoc /= IH -app_assoc.
Qed.

Lemma run_ch : run ch = rc ++ rc ++ rc ++ run [c0].
Proof.
have -> : ch = (c0 :: cs) ++ (c0 :: cs) ++ (c0 :: cs) ++ [c0] by [].
by rewrite !run_app.
Qed.

Lemma rc_len : length (uword c0) < length rc.
Proof. rewrite /rc /= length_app; lia. Qed.

Lemma run_ch_split v i x :
  rc !! i = Some x →
  v = take i rc ∨ v = rc ++ take i rc ∨ v = rc ++ rc ++ take i rc →
  ∃ r', run ch = v ++ x :: r'.
Proof.
move=> Hi; have Erc : rc = take i rc ++ x :: drop (S i) rc.
{ by rewrite -(drop_S _ _ _ Hi) take_drop. }
rewrite run_ch => - [->|[->|->]].
- exists (drop (S i) rc ++ rc ++ rc ++ run [c0]).
  by rewrite {1}Erc -app_assoc.
- exists (drop (S i) rc ++ rc ++ run [c0]).
  by rewrite {2}Erc -!app_assoc.
- exists (drop (S i) rc ++ run [c0]).
  by rewrite {3}Erc -!app_assoc.
Qed.

(** ** Word-level facts, from UnivEncoding.v's detect and prefix_end *)

Let B : fka M := star (FKA (bal_gen (A := L))).

Lemma B_word_le w (F Y : term) :
  l (bstar ⋅ F) (w, length w) → bstar ⋅ F ⊑ Y →
  B ⋅ FKA (bal w) ⊑ FKA Y.
Proof.
move=> /l_alt Hw HY.
etransitivity; last exact: fka_le_of_pre HY.
etransitivity.
  apply: pre_ka_mul_mono; [reflexivity|exact: fka_le_of_pre Hw].
change (B ⋅ (B ⋅ FKA F) ⊑ B ⋅ FKA F).
by rewrite assoc ka_star_mul_star.
Qed.

Lemma dev_ep v i x t :
  rc !! i = Some x → t ≠ x →
  v = take i rc ∨ v = rc ++ take i rc ∨ v = rc ++ rc ++ take i rc →
  l ep (v ++ [t], length (v ++ [t])).
Proof.
move=> Hi Ht Hv; case: (run_ch_split Hi Hv) => r' Er.
exact: (detect q0 uchain_ch Er Ht).
Qed.

Lemma pre_ee v i x :
  rc !! i = Some x →
  v = take i rc ∨ v = rc ++ take i rc ∨ v = rc ++ rc ++ take i rc →
  l ee (v, length v).
Proof.
move=> Hi Hv; case: (run_ch_split Hi Hv) => r' Er.
exact: (prefix_end q0 uchain_ch Er).
Qed.

Lemma long_ep w :
  l ep (w, length w) → length (run [c0]) < length w →
  B ⋅ FKA (bal w) ⊑ FKA ep.
Proof.
move=> H Hlen; case/l_join: H => H.
- case/l_init_errs_inv: H => p [t0 [r [t [Ew [_ Ev]]]]].
  move: Hlen; rewrite Ew Ev /= !length_app /=; lia.
- by apply: (B_word_le H); exact: sqsubseteq_join_right.
Qed.

Lemma long_ee w :
  l ee (w, length w) → 2 ≤ length w → B ⋅ FKA (bal w) ⊑ FKA ee.
Proof.
move=> H Hlen; case/l_join: H => [/l_join [/l_join [H|H]|H]|H].
- by case/l_one: H => Ew _; move: Hlen; rewrite Ew /=; lia.
- by case/l_bal_eq: H => Ew _; move: Hlen; rewrite Ew /=; lia.
- apply: (B_word_le H).
  by etransitivity; last exact: sqsubseteq_join_left;
     exact: sqsubseteq_join_right.
- by apply: (B_word_le H); exact: sqsubseteq_join_right.
Qed.

(** ** The invariant *)

Let R : fka M := FKA (star (bal rc)).
Let Cur : term := ⨆ i ∈ seq 0 (length rc), bal (take i rc).
Let E : fka M := FKA (ep ⋅ bstar).

Lemma R_unfold : R ⊑ 1 ⊔ FKA (bal rc) ⊔ B ⋅ FKA (bal rc) ⋅ FKA (bal rc).
Proof.
change (star (FKA (bal rc)) ⊑
        1 ⊔ FKA (bal rc) ⊔ star (FKA (bal_gen (A := L))) ⋅ FKA (bal rc) ⋅
        FKA (bal rc)).
apply: star_unfold2.
exact: fka_le_of_pre (bal_le_star rc).
Qed.

Lemma fka_bal_app (w u : list L) :
  FKA (bal (w ++ u)) ≡ FKA (bal w) ⋅ FKA (bal u).
Proof. exact: fka_of_pre (bal_app w u). Qed.

Lemma R_word (w : list L) :
  R ⋅ FKA (bal w) ⊑
  FKA (bal w) ⊔ FKA (bal (rc ++ w)) ⊔ B ⋅ FKA (bal (rc ++ rc ++ w)).
Proof.
etransitivity; first by apply: pre_ka_mul_mono; [exact: R_unfold|].
rewrite !pre_ka_left_dist left_id !fka_bal_app !assoc.
reflexivity.
Qed.

Lemma ep_E : FKA ep ⊑ E.
Proof.
apply: fka_le_of_pre; rewrite -{1}[ep](right_id 1).
by apply: pre_ka_mul_mono => //; exact: pre_ka_one_star.
Qed.

Lemma one_Cur : (1 : term) ⊑ Cur.
Proof.
have Hpos : 0 < length rc by rewrite /rc /=; lia.
have H0 : 0 ∈ seq 0 (length rc) by apply/elem_of_seq; lia.
etransitivity; last exact: (sqsubseteq_join_list (λ i, bal (take i rc)) H0).
by rewrite /= bal_nil.
Qed.

Lemma step_le i t :
  i ∈ seq 0 (length rc) →
  R ⋅ FKA (bal (take i rc ++ [t])) ⊑ R ⋅ FKA Cur ⊔ E.
Proof.
move/elem_of_seq => Hi.
have [x Hx] : is_Some (rc !! i) by apply/lookup_lt_is_Some; lia.
case: (decide (t = x)) => [->|Ht].
- etransitivity; last exact: sqsubseteq_join_left.
  rewrite -(take_S_r _ _ _ Hx).
  case: (decide (S i < length rc)) => HSi.
  + apply: pre_ka_mul_mono => //; apply: fka_le_of_pre.
    rewrite /Cur; apply: (sqsubseteq_join_list (λ i, bal (take i rc))).
    apply/elem_of_seq; lia.
  + have -> : take (S i) rc = rc by apply: take_ge; lia.
    change (star (FKA (bal rc)) ⋅ FKA (bal rc) ⊑
            star (FKA (bal rc)) ⋅ FKA Cur).
    etransitivity; first exact: star_mul_self'.
    rewrite -{1}[star _](right_id 1); apply: pre_ka_mul_mono => //.
    exact: fka_le_of_pre one_Cur.
- etransitivity; last exact: sqsubseteq_join_right.
  etransitivity; first exact: R_word.
  apply/join_sqsubseteq; split; [apply/join_sqsubseteq; split|].
  + etransitivity; last exact: ep_E.
    apply: fka_le_of_pre; apply/l_alt.
    by apply: (dev_ep Hx Ht); left.
  + etransitivity; last exact: ep_E.
    apply: fka_le_of_pre; apply/l_alt; rewrite app_assoc.
    by apply: (dev_ep Hx Ht); right; left.
  + etransitivity; last exact: ep_E.
    have -> : rc ++ rc ++ take i rc ++ [t] = (rc ++ rc ++ take i rc) ++ [t].
      by rewrite -!app_assoc.
    apply: long_ep; first by apply: (dev_ep Hx Ht); right; right.
    move: rc_len; rewrite /run /cw /= !length_app /=; lia.
Qed.

Lemma cur_le i :
  i ∈ seq 0 (length rc) →
  R ⋅ FKA (bal (take i rc)) ⊑ FKA ee.
Proof.
move/elem_of_seq => Hi.
have [x Hx] : is_Some (rc !! i) by apply/lookup_lt_is_Some; lia.
etransitivity; first exact: R_word.
apply/join_sqsubseteq; split; [apply/join_sqsubseteq; split|].
- apply: fka_le_of_pre; apply/l_alt.
  by apply: (pre_ee Hx); left.
- apply: fka_le_of_pre; apply/l_alt.
  by apply: (pre_ee Hx); right; left.
- apply: long_ee; first by apply: (pre_ee Hx); right; right.
  move: rc_len; rewrite !length_app; lia.
Qed.

Theorem fka_univ_cycle : FKA bstar ⊑ FKA (univ_ub prog nxt acts q0 c0).
Proof.
set X := R ⋅ FKA Cur ⊔ E.
have HX : X ⊑ FKA (univ_ub prog nxt acts q0 c0).
{ apply/join_sqsubseteq; split; last first.
    by apply: fka_le_of_pre; exact: sqsubseteq_join_right.
  etransitivity; last first.
    by apply: fka_le_of_pre; exact: sqsubseteq_join_left.
  change (FKA (star (bal rc) ⋅ Cur) ⊑ FKA ee).
  rewrite /Cur (fka_of_pre (join_list_right_dist _ _ _)) fka_join_list.
  apply/join_list_sqsubseteq => i Hi; exact: cur_le. }
etransitivity; last exact: HX.
change (FKA bstar) with (star (FKA (bal_gen (A := L)))).
rewrite -[star _](left_id 1).
apply: ka_star_ind_r; apply/join_sqsubseteq; split.
  etransitivity; last exact: sqsubseteq_join_left.
  rewrite -[1](left_id 1); apply: pre_ka_mul_mono.
    exact: fka_le_of_pre (pre_ka_one_star (bal rc)).
  exact: fka_le_of_pre one_Cur.
rewrite {1}/X pre_ka_left_dist; apply/join_sqsubseteq; split.
- rewrite /Cur /bal_gen !fka_join_list -assoc join_list_left_dist.
  rewrite join_list_right_dist; apply/join_list_sqsubseteq => i Hi.
  rewrite join_list_right_dist join_list_right_dist.
  apply/join_list_sqsubseteq => t _.
  rewrite -fka_bal_app; exact: step_le.
- etransitivity; last exact: sqsubseteq_join_right.
  change (FKA ep ⋅ B ⋅ FKA bal_gen ⊑ FKA ep ⋅ B).
  rewrite -assoc; apply: pre_ka_mul_mono => //.
  exact: star_mul_self'.
Qed.

End Cycle.

(** * MM2 machines whose start state lies on a cycle *)

Section MM2Cycle.

Variable P : list mm2_instr.
Notation Q := (fin (S (S (length P)))).
Notation TL := (option_setoid (@mm_sym_setoid Q)).

Theorem fka_univ_top_cycle s1 s2 :
  mm2_step P s1 s2 → rtc (mm2_step P) s2 s1 →
  FKA (sigma_top (A := TL)) ⊑ FKA (univ_top_ub P s1).
Proof.
move=> Hs /rtc_uchain [cs [cs' [Hc E]]].
case: (step_uconf Hs) => Hact Es.
have Hcyc : uchain (@mm2_prog P) (@next_state P) (active_states P)
              (uconf_of P s1 :: cs' ++ [uconf_of P s1]).
{ by rewrite -E; split; [|split]. }
rewrite sigma_top_ka.
change (FKA (bal_star (A := TL)) ⊔ FKA unbal ⊑
        FKA (univ_ub_mm2 P s1) ⊔ FKA unbal).
by apply: join_mono => //; exact: fka_univ_cycle Hcyc.
Qed.

End MM2Cycle.

(** * The two-instruction loop *)

Local Close Scope ka_scope.

Theorem fka_univ_top_loop :
  FKA (sigma_top (A := option_setoid (@mm_sym_setoid
         (fin (S (S (length loop_prog))))))) ⊑
  FKA (univ_top_ub loop_prog (1, (0, 0))).
Proof.
apply: (fka_univ_top_cycle loop_step1).
by apply: rtc_l; [exact: loop_step2|exact: rtc_refl].
Qed.

(** The KA analogue of UnivDirect.v's univ_not_le_of_not_terminates is
    false. *)

Corollary fka_univ_top_not_terminates_fails :
  ¬ (∀ P s1, ¬ mm2_terminates P s1 →
     ¬ FKA (sigma_top (A := option_setoid (@mm_sym_setoid
              (fin (S (S (length P))))))) ⊑ FKA (univ_top_ub P s1)).
Proof.
move=> H; exact: H _ _ loop_not_terminates fka_univ_top_loop.
Qed.
