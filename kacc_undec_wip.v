(* ------- ------- *)
(* ------- Interpreting MM instructions as terms ------- *)
(* ------- ------- *)

Section Theory.
Local Open Scope ka_scope.

Inductive Σ_M : Type :=
  | Q_M (n : nat)
  | a
  | b
  | c_0
  | c_1.

Fixpoint π_l (t : ka_term Σ_M) : ka_term Σ_M :=
  match t with
  | 0 => 0
  | 1 => 1
  | L _ => t
  | R _ => 1
  | t1 ⋅ t2 => (π_l t1) ⋅ (π_l t2)
  | t1 + t2 => (π_l t1) + (π_l t2)
  | K_Star t' => K_Star (π_l t')
  end%ka.

Fixpoint π_r (t : ka_term Σ_M) : ka_term Σ_M :=
  match t with
  | 0 => 0
  | 1 => 1
  | L _ => 1
  | R _ => t
  | t1 ⋅ t2 => (π_r t1) ⋅ (π_r t2)
  | t1 + t2 => (π_r t1) + (π_r t2)
  | K_Star t' => K_Star (π_r t')
  end%ka.

Lemma star_leq : forall (t : ka_term T), 1 + t⋅t✶ ≤ t✶.
Proof.
  intros.
  rewrite - star_expand.
  apply leq_reflex.
Qed.

Definition build_term (side : T -> ka_term T) := fold_right (λ (n : T) t, side n ⋅ t).

Fixpoint strip_ones (t : ka_term T) :=
  match t with
  | 1 ⋅ t => strip_ones t
  | t ⋅ 1 => strip_ones t
  | t ⋅ t' => (strip_ones t) ⋅ strip_ones t'
  | t + t' => (strip_ones t) + strip_ones t'
  | _ => t
  end.

(* Global Instance strip_ones_proper :
  Proper (ka_eq ==> ka_eq) (@strip_ones).
Proof.
  (* rewrite /strip_ones => t1 t2; elim: t1 t2 / => //=. *)
  move=> t1 t2; elim: t1 t2 / => //=.
  - move=> x y H G. by apply Ka_sym.
  - move=> x y z _ H _ G. apply (Ka_trans H G).
  - move=> x y H _ x' y' H' _. by rewrite H; rewrite H'.
  - move=> x y H G x' y' H' G'. rewrite H. *)

(* Lemma strip_ones_dist_dot t t' : strip_ones (t ⋅ t') ≡ (strip_ones t) ⋅ (strip_ones t').
Proof.
  induction t.
  - simpl. rewrite [X in _ ≡ X] Dot_Z2. *)

Lemma strip_ones_equiv t : strip_ones t ≡ t.
Proof.
  elim: t; try reflexivity.
  - move=> t1 H t2 G.
    rewrite -[X in _ ≡ X+_] H.
    rewrite -[X in _ ≡ _+X] G.
    elim t1; eauto.
  - move=> t1 H t2 G.
    rewrite -[X in _ ≡ X⋅_] H.
    rewrite -[X in _ ≡ _⋅X] G.
    elim t1.
    + simpl. rewrite [X in _ ≡ X] Dot_Z2.
Admitted.



Definition string_to_ka_term ls :=
  match ls with (l1, l2) =>
    (* strip_ones *) ((build_term L 1 l1)⋅(build_term R 1 l2))
  end.

(* QUEST: thoughts on notation here? *)
Global Instance up_close_comm_string : UpClose (list T * list T) (ka_term T) :=
  λ x, string_to_ka_term x.

Definition interp (n : nat) (P : list mm2_instr) :=
  match nth n P mm2_inc_a with
  | mm2_inc_a => R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M (S n))
  | mm2_inc_b => (lr a)✶ ⋅ R b ⋅ (lr b)✶  ⋅ R (Q_M (S n))
  | mm2_dec_a n' => (lr b)✶ ⋅ (R (Q_M n'))
                    + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  | mm2_dec_b n' => (lr a)✶ ⋅ (R (Q_M n'))
                    + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  end.

Definition interp_single (n : nat) (instr : mm2_instr) :=
  match instr with
  | mm2_inc_a =>    R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M (S n))
  | mm2_inc_b =>    (lr a)✶ ⋅ R b ⋅ (lr b)✶  ⋅ R (Q_M (S n))
  | mm2_dec_a n' => (lr b)✶ ⋅ (R (Q_M n'))
                    + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  | mm2_dec_b n' => (lr a)✶ ⋅ (R (Q_M n'))
                    + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  end.


Definition ka_simpl_plus (t1 t2 : ka_term T) : ka_term T :=
  match t1, t2 with
  | 0, _ => t2
  | _, 0 => t1
  | _, _ => t1 + t2
  end.

Variant ka_simpl_plus_spec : ka_term T -> ka_term T -> ka_term T -> Type :=
| KaSimplPlus1 t2 : ka_simpl_plus_spec 0 t2 t2
| KaSimplPlus2 t1 : ka_simpl_plus_spec t1 0 t1
| KaSimplPlus3 t1 t2 : ka_simpl_plus_spec t1 t2 (t1 + t2).

Lemma ka_simpl_plusP t1 t2 : ka_simpl_plus_spec t1 t2 (ka_simpl_plus t1 t2).
Proof.
case: t1 => *; case: t2 => * /=; constructor.
Qed.

Lemma ka_simpl_plusE t1 t2 : ka_simpl_plus t1 t2 ≡ t1 + t2.
Proof.
case: t1 t2 _ / ka_simpl_plusP => [t2|t1|t1 t2] //.
- by rewrite Plus_Id.
- by rewrite Plus_Id'.
Qed.

Definition ka_simpl_dot (t1 t2 : ka_term T) : ka_term T :=
  match t1, t2 with
  | 0, _ => 0
  | _, 0 => 0
  | 1, _ => t2
  | _, 1 => t1
  | _, _ => K_Dot t1 t2
  end.

Variant ka_simpl_dot_spec : ka_term T -> ka_term T -> ka_term T -> Type :=
| KaSimplDot1 t2 : ka_simpl_dot_spec 0 t2 0
| KaSimplDot2 t1 : ka_simpl_dot_spec t1 0 0
| KaSimplDot3 t2 : ka_simpl_dot_spec 1 t2 t2
| KaSimplDot4 t1 : ka_simpl_dot_spec t1 1 t1
| KaSimplDot5 t1 t2 : ka_simpl_dot_spec t1 t2 (K_Dot t1 t2).

Lemma ka_simpl_dotP t1 t2 : ka_simpl_dot_spec t1 t2 (ka_simpl_dot t1 t2).
Proof.
case: t1 => *; case: t2 => * /=; constructor.
Qed.

Lemma ka_simpl_dotE t1 t2 : ka_simpl_dot t1 t2 ≡ K_Dot t1 t2.
Proof.
case: t1 t2 _ / ka_simpl_dotP => [t2|t1|t2|t1|t1 t2] //.
- by rewrite Dot_Z2.
- by rewrite Dot_Z1.
- by rewrite Dot_Id2.
- by rewrite Dot_Id1.
Qed.

Definition ka_simpl_star t : ka_term T :=
  match t with
  | 0 => 1
  | _ => K_Star t
  end.

Lemma ka_simpl_starE t : ka_simpl_star t ≡ K_Star t.
Proof.
case: t => //=.
by rewrite Star Dot_Z2 Plus_Id'.
Qed.

Fixpoint ka_simpl t : ka_term T :=
  match t with
  | 0 => 0
  | 1 => 1
  | L _ => t
  | R _ => t
  | t1 + t2 => ka_simpl_plus (ka_simpl t1) (ka_simpl t2)
  | K_Dot t1 t2 => ka_simpl_dot (ka_simpl t1) (ka_simpl t2)
  | K_Star t => ka_simpl_star (ka_simpl t)
  end.

Lemma ka_simplE t : ka_simpl t ≡ t.
Proof.
elim: t => //=.
- by move=> t1 IH1 t2 IH2; rewrite ka_simpl_plusE IH1 IH2.
- by move=> t1 IH1 t2 IH2; rewrite ka_simpl_dotE IH1 IH2.
- by move=> t IH; rewrite ka_simpl_starE IH.
Qed.

Lemma ka_simpl_inj t1 t2 : ka_simpl t1 ≡ ka_simpl t2 → t1 ≡ t2.
Proof. by rewrite !ka_simplE. Qed.

Global Instance ka_simpl_proper : Proper ((≡) ==> (≡)) ka_simpl.
Proof. by move=> t1 t2 e; rewrite !ka_simplE. Qed.

(* QUEST: is this notation reasonable? *)
Global Instance ka_term_elem_of : ElemOf (list T * list T) (ka_term T) :=
  λ s t, lang_interp t s.

(* used, but unused *)
Lemma term_leq_term_star : ∀ (t : ka_term T), t ≤ t✶.
Proof.
  intros.
  (* rewrite {2} Star. *)
  rewrite Star.
  rewrite Star.
  rewrite Dist_L.
  rewrite Dot_Id1.
  rewrite Plus_Com.
  rewrite - Plus_Assoc.
  apply t_leq_t_plus.
Qed.

(* unused *)
Lemma leq_term__leq_term_star : ∀ (t t': ka_term T), t ≤ t' -> t ≤ K_Star t'.
Proof.
  intros.
  apply leq_trans with (t2:=t'); [assumption | apply term_leq_term_star].
Qed.

(* unused *)
Lemma t__leq__t_star : ∀ (t : ka_term T), t ≤ t✶.
Proof.
  intros.
  unfold ka_leq.
  rewrite Star.
  rewrite Star.
  rewrite Dist_L.
  rewrite Dot_Id1.
  rewrite - Plus_Assoc.
  assert (H : t + t ⋅ (t ⋅ t ✶) + t ≡ t + t ⋅ (t ⋅ t ✶) ).
  { rewrite Plus_Com. rewrite Plus_Assoc.
    rewrite Plus_Idemp. reflexivity. }
  rewrite H.
  rewrite Plus_Assoc.
  reflexivity.
Qed.

(* used *)
Lemma t_tstar__leq__tstar : ∀ (t : ka_term T), t⋅t✶ ≤ t✶.
Proof.
  intros.
  rewrite [X in _ ≤ X] Star.
  rewrite Plus_Com.
  apply t_leq_t_plus.
Qed.

(* used, but unused *)
Lemma leq__leq_dot_L : ∀ (t1 t2 t3 : ka_term T), t2 ≤ t3 -> t1 ⋅ t2 ≤ t1 ⋅ t3.
Proof.
  intros.
  unfold ka_leq in H.
  rewrite - H.
  rewrite Dist_L.
  rewrite Plus_Com.
  apply t_leq_t_plus.
Qed.

(* unused *)
Lemma leq__leq_dot_R : ∀ (t1 t2 t3 : ka_term T), t1 ≤ t3 -> t1 ⋅ t2 ≤ t3 ⋅ t2.
Proof.
  intros.
  unfold ka_leq in H.
  rewrite - H.
  rewrite Dist_R.
  rewrite Plus_Com.
  apply t_leq_t_plus.
Qed.

(* unused *)
Lemma pow_leq_star : ∀ (t : ka_term T) n, t^n ≤ t✶.
Proof.
  intros.
  generalize dependent t.
  induction n as [| n IHn].
  - intros. unfold ka_power. apply one_leq_star.
  - intros. simpl.
    rewrite Star.
    assert (H : t⋅t^n ≤ t⋅t✶).
    { apply leq__leq_dot_L. apply IHn. }
    apply leq_trans with (t2:=t⋅t✶).
    + assumption.
    + rewrite Plus_Com. apply t_leq_t_plus.
Qed.

(* Theorem 5 *)
Theorem term_lang_equiv : ∀ s t, ↑s ≤ t <-> s ∈ t.
Proof.
  intros; split; intros H.
  - unfold ka_leq in H.
    rewrite l_i_equality. symmetry in H. apply H.
    simpl.
    unfold ka_pred_add. right.
    apply li_term_to_string_true.
  - generalize dependent s.
    induction t; intros.
    + simpl in H. contradiction.
    + simpl in H. unfold ka_pred_unit in H.
      subst. simpl. rewrite Dot_Id2. apply leq_reflex.
    + inversion H. simpl. repeat (rewrite Dot_Id1). apply leq_reflex.
    + inversion H. simpl. rewrite Dot_Id2; rewrite Dot_Id1; apply leq_reflex.
    + simpl in H; unfold ka_pred_add in H. destruct H as [H1 | H2].
      * apply IHt1 in H1.
        apply leq_trans with (t2:=t1);
        [assumption | apply t_leq_t_plus].
      * apply IHt2 in H2.
        apply leq_trans with (t2:=t2);
        [assumption | rewrite Plus_Com; apply t_leq_t_plus].
    + simpl in H. unfold ka_pred_mul in H.
      destruct H as [s1 [s2 [Hs1s2 [HLI1 HLI2]]]].
      apply IHt1 in HLI1; apply IHt2 in HLI2.
      subst. destruct s1, s2. rewrite string_to_term__pair_append__commute.
      apply leq_leq_dot; assumption.
    + simpl in H. unfold ka_pred_star in H.
      destruct H as [n H].
      generalize dependent s.
      induction n as [| n IHn].
      * intros; simpl in H.
        unfold ka_pred_unit in H; subst.
        simpl; rewrite Dot_Id1.
        apply one_leq_star.
      * intros. simpl in H.
        destruct H as [s1 [s2 [Hs1s2 [HLI1 Hpow]]]].
        apply IHn in Hpow.
        subst.
        apply IHt in HLI1.
        destruct s1 as (s1, s1'), s2 as (s2, s2').
        rewrite string_to_term__pair_append__commute.
        assert (H : (↑(s1, s1')) ⋅ (↑(s2, s2')) ≤ t⋅t✶).
        {
          apply leq_leq_dot; assumption.
        }
        apply leq_trans with (t2:=t⋅t✶);
        [assumption | apply t_tstar__leq__tstar].
Qed.

(* unused *)
Lemma zero_neq_one : (@K_Zero T ≢ @K_One T)%ka.
Proof.
  intros H.
  (* QUEST: why was using apply not working here?? *)
  have eq_langs := l_i_equality H.
  specialize (eq_langs ([], [])).
  simpl in eq_langs.
  unfold ka_pred_zero, ka_pred_unit in eq_langs.
  rewrite eq_langs.
  reflexivity.
Qed.

(* unused *)
Lemma zero_neq_L : ∀ a, (@K_Zero T ≢ L a).
Proof.
  intros a H.
  have eq_langs := l_i_equality H.
  specialize (eq_langs ([a], [])).
  simpl in eq_langs.
  unfold ka_pred_zero, ka_pred_left in eq_langs.
  rewrite eq_langs.
  reflexivity.
Qed.

(* unused *)
Lemma zero_neq_R : ∀ a, (@K_Zero T ≢ R a).
Proof.
  intros a H.
  have eq_langs := l_i_equality H.
  specialize (eq_langs ([], [a])).
  simpl in eq_langs.
  unfold ka_pred_zero, ka_pred_left in eq_langs.
  rewrite eq_langs.
  reflexivity.
Qed.

(* unused *)
Lemma zero_neq_one_plus_t : ∀ (t : ka_term T), 0 ≢ 1 + t.
Proof.
  intros t H.
  have G := l_i_equality H.
  specialize (G ([], [])).
  simpl in G.
  unfold ka_pred_zero, ka_pred_add, ka_pred_unit in G.
  rewrite G. left. reflexivity.
Qed.

(* unused *)
Lemma zero_neq_L_plus_t : ∀ (t : ka_term T) a, 0 ≢ L a + t.
Proof.
  intros t a H.
  have G := l_i_equality H.
  specialize (G ([a], [])).
  simpl in G.
  unfold ka_pred_zero, ka_pred_add, ka_pred_unit in G.
  rewrite G. left. reflexivity.
Qed.

(* unused *)
Lemma zero_neq_R_plus_t : ∀ (t : ka_term T) a, 0 ≢ R a + t.
Proof.
  intros t a H.
  have G := l_i_equality H.
  specialize (G ([], [a])).
  simpl in G.
  unfold ka_pred_zero, ka_pred_add, ka_pred_unit in G.
  rewrite G. left. reflexivity.
Qed.

(* unused *)
Lemma neq_reflex_false : ∀ (t : ka_term T), not (t ≢ t).
Proof.
  intros t H; apply H; reflexivity.
Qed.

(* Corollary 8' *)
Lemma either_empty_or_nonzero : ∀ (t : ka_term T), t ≡ 0 ∨ ∃ s, s ∈ t.
Proof.
  intros t.
  induction t.
  - left; reflexivity.
  - right. exists ([], []). reflexivity.
  - right. exists ([t], []). reflexivity.
  - right. exists ([], [t]). reflexivity.
  - destruct IHt1 as [IHt1 | IHt1]; destruct IHt2 as [IHt2 | IHt2].
    + left. rewrite IHt1. rewrite IHt2. apply Plus_Idemp.
    + right. destruct IHt2 as [s H].
      exists s. rewrite IHt1.
      rewrite Plus_Id; assumption.
    + right; destruct IHt1 as [s H].
      exists s; rewrite IHt2.
      rewrite Plus_Id'.
      assumption.
    + destruct IHt1 as [s1 H1], IHt2 as [s2 H2].
      right. exists s1.
      simpl. unfold ka_pred_add.
      left; assumption.
  - destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2].
    + left. rewrite H1. apply Dot_Z2.
    + left. rewrite H1. apply Dot_Z2.
    + left. rewrite H2. apply Dot_Z1.
    + destruct H1 as [s1 H1], H2 as [s2 H2].
      right.
      exists (pair_append s1 s2).
      simpl.
      unfold ka_pred_mul.
      exists s1, s2.
      auto.
  - right. exists ([], []).
    simpl.
    unfold ka_pred_star.
    exists 0%nat.
    reflexivity.
Qed.


Lemma interp_build_term_l : ∀ s, (s, []) ∈ build_term L 1 s.
Proof.
  intros s. induction s as [| c s IHs].
  - reflexivity.
  - simpl in *.
    unfold ka_pred_mul, ka_pred_left.
    exists ([c], []), (s, []).
    repeat split; intuition.
Qed.

Lemma interp_build_term_r : ∀ s, ([], s) ∈ build_term R 1 s.
Proof.
  intros s. induction s as [| c s IHs].
  - reflexivity.
  - simpl in *.
    unfold ka_pred_mul, ka_pred_left.
    exists ([], [c]), ([], s).
    repeat split; intuition.
Qed.

(* Corollary 8'' *)
Lemma no_string_leq_0 : ∀ s, not (↑s ≤ 0).
Proof.
  intros s H.
  unfold ka_leq in H.
  rewrite Plus_Id in H.
  destruct s as (s1, s2).
  simpl in H.
  have eq_langs := l_i_equality H.
  specialize (eq_langs (s1, s2)).
  simpl in eq_langs; unfold ka_pred_mul, ka_pred_zero in eq_langs.
  apply eq_langs.
  exists (s1, []), ([], s2).
  repeat split.
  - simpl; rewrite app_nil_r; reflexivity.
  - apply interp_build_term_l.
  - apply interp_build_term_r.
Qed.

(* unused *)
Lemma no_string_equiv_0 : ∀ s, ↑s ≢ 0.
Proof.
  intros s H.
  rewrite <- Plus_Id in H. (* QUEST: ssreflect way of writing this? *)
  apply no_string_leq_0 in H; assumption.
Qed.

(* unused *)
Lemma zero_leq_anything : ∀ (t : ka_term T), 0 ≤ t.
Proof.
  intros.
  unfold ka_leq.
  apply Plus_Id'.
Qed.

Lemma zero_eq_sum : ∀ (t t' : ka_term T), 0 ≡ t + t' <-> 0 ≡ t ∧ 0 ≡ t'.
Proof.
  intros t t'; split.
  - intros H. generalize dependent t'.
    induction t.
    + intros t' H. rewrite Plus_Id in H.
      intuition.
    + intros t' H.
      apply zero_neq_one_plus_t in H.
      exfalso; assumption.
    + intros t' H.
      apply zero_neq_L_plus_t in H.
      exfalso; assumption.
    + intros t' H.
      apply zero_neq_R_plus_t in H.
      exfalso; assumption.
    + intros t' H.
      rewrite - Plus_Assoc in H.
      apply IHt1 in H as [H1 H2].
      apply IHt2 in H2 as [H2 H3].
      rewrite - H1.
      rewrite - H2.
      rewrite Plus_Idemp.
      intuition.
    + intros t' H.
    admit.
    + intros t' H.
      rewrite Star in H.
      rewrite - Plus_Assoc in H.
      apply zero_neq_one_plus_t in H.
      contradiction.
  - intros [H1 H2].
    rewrite - H1; rewrite - H2.
    rewrite Plus_Id.
    reflexivity.
Admitted.

Lemma zero_eq_prod : ∀ (t1 t2 : ka_term T), 0 ≡ t1 ⋅ t2 -> t1 ≡ 0 ∨ t2 ≡ 0.
Proof.
  intros t1 t2 H.
  generalize dependent t2.
  induction t1.
  - intros t2 H; left; reflexivity.
  - intros t2 H. rewrite Dot_Id2 in H.
    right; symmetry; assumption.
  - intros t2 H.
    have [Ht2 | [s Ht2]] := either_empty_or_nonzero t2.
    + right; assumption.
    + have eq_langs := l_i_equality H.
      simpl in eq_langs.
      unfold ka_pred_zero, ka_pred_mul, ka_pred_left in eq_langs.
      exfalso; rewrite eq_langs.
      exists ([t], []), s.
      repeat split.
      auto.
  - intros t2 H.
    have [Ht2 | [s Ht2]] := either_empty_or_nonzero t2.
    + right; assumption.
    + have eq_langs := l_i_equality H.
      simpl in eq_langs.
      unfold ka_pred_zero, ka_pred_mul, ka_pred_right in eq_langs.
      exfalso; rewrite eq_langs.
      exists ([], [t]), s.
      repeat split.
      auto.
  - intros t2 H.
    Search K_Zero.
    have [Ht2 | [s Ht2]] := either_empty_or_nonzero t2.
    + right; assumption.
    + have eq_langs := l_i_equality H.
      simpl in eq_langs.
      unfold ka_pred_zero, ka_pred_mul, ka_pred_add in eq_langs.
Admitted.

(* used but unused *)
Lemma zero_neq_prod : ∀ (t1 t2 : ka_term T), 0 ≢ t1 ⋅ t2 (*<*)-> t1 ≢ 0 ∧ t2 ≢ 0.
Proof.
  (* split;  *)intros t1 t2 H.
  split; intros G.
    + rewrite G in H.
      rewrite Dot_Z2 in H.
      apply H; reflexivity.
    + rewrite G in H.
      rewrite Dot_Z1 in H.
      apply H; reflexivity.
Qed.

(* unused *)
Lemma zero_neq_const_dot_term : ∀ (t t': ka_term T) a, (t ≡ 1 ∨ t ≡ L a ∨ t ≡ R a) -> 0 ≢ t⋅t' -> 0 ≢ t'.
Proof.
  intros t t' a H G.
  destruct H as [H | [H | H]]; rewrite H in G; clear H;
  try (rewrite Dot_Id2 in G; assumption);
  apply zero_neq_prod in G as [G1 G2];
  apply ka_neq_sym; assumption.
Qed.

(* QUEST: is there a nice way to merge these two lemmas? *)
Lemma lang_interp_build_l : ∀ (s1 s2 s3 : list T),
  (s2, s3) ∈ build_term L 1 s1 -> s2 = s1 ∧ s3 = [].
Proof.
  intros s1 s2 s3 H. simpl in H.
  generalize dependent s2;
  generalize dependent s3.
  induction s1 as [|c s1 IHs1].
  + intros. simpl in H; unfold ka_pred_unit in H.
    inversion H. intuition.
  + intros.
    simpl in H;
    unfold ka_pred_mul in H.
    destruct H as [s4 [s5 [Hp [Hl HLI]]]].
    unfold ka_pred_left in Hl.
    subst. destruct s5 as (s5, s5'). simpl in Hp.
    inversion Hp; subst.
    apply IHs1 in HLI as [Heq H5].
    subst. intuition.
Qed.

Lemma lang_interp_build_r : ∀ (s1 s2 s3 : list T),
  (s2, s3) ∈ build_term R 1 s1 -> s1 = s3 ∧ s2 = [].
Proof.
  intros s1 s2 s3 H. simpl in H.
  generalize dependent s2;
  generalize dependent s3.
  induction s1 as [|c s1 IHs1].
  + intros. simpl in H; unfold ka_pred_unit in H.
    inversion H. intuition.
  + intros.
    simpl in H;
    unfold ka_pred_mul in H.
    destruct H as [s4 [s5 [Hp [Hr HLI]]]].
    unfold ka_pred_right in Hr.
    subst. destruct s5 as (s5, s5'). simpl in Hp.
    inversion Hp. subst.
    apply IHs1 in HLI as [Heq H5].
    subst. intuition.
Qed.

Lemma string_interp_self : ∀ s s', s' ∈ (↑s) <-> s = s'.
Proof.
  intros.
  split.
  - intros H.
    destruct s as (s1, s2), s' as (s1', s2').
    simpl in H.
    unfold ka_pred_mul in H.
    destruct H as [s3 [s4 [Hs1s2' [HLIs1 HLIs2]]]].
    destruct s3 as (s3, s3'), s4 as (s4, s4').
    simpl in Hs1s2'.
    rewrite Hs1s2'.
    apply lang_interp_build_l in HLIs1 as [H1 H2];
    apply lang_interp_build_r in HLIs2 as [H3 H4].
    subst; simpl; rewrite app_nil_r.
    reflexivity.
  - intros H. rewrite H.
    apply li_term_to_string_true.
Qed.

Fixpoint map_indexed' {A} {B} (f : nat -> A -> B) n ls :=
  match ls with
  | [] => []
  | hd :: tl => f n hd :: map_indexed' f (S n) tl
  end.

Definition map_indexed {A} {B} (f : nat -> A -> B) ls := map_indexed' f 0 ls.

Definition term_product (ls : list (ka_term T)) := fold_right (λ t t', t⋅t') 1 ls.

Definition term_sum (ls : list (ka_term T)) := fold_right (λ t t', t+t') 0 ls.

Lemma term_sum_app ls1 ls2 : term_sum (ls1 ++ ls2) ≡ term_sum ls1 + term_sum ls2.
Proof.
elim: ls1 => [|s1 ls1 IH] /=; first by rewrite Plus_Id.
by rewrite IH Plus_Assoc.
Qed.

Definition cstring_sum (ls : list (list T * list T)) := term_sum (map string_to_ka_term ls).
Notation "## ls" := (cstring_sum ls) (at level 30):ka_scope.

Lemma string_interp_in_list : ∀ ls s, s ∈ ##ls <-> In s ls.
Proof.
  move=> ls.
  split; move: s.
  - elim: ls; [done| move=> s ls IHl s' H].
    simpl in *.
    unfold ka_pred_add in H.
    destruct H as [H | H]; [apply string_interp_self in H | ]; intuition.
  - elim: ls; [done| move=> s ls IHl s' H]; simpl in H;
    destruct H as [H | H];
    simpl; unfold ka_pred_add;
    [rewrite string_interp_self | apply IHl in H];
    intuition.
Qed.

Lemma cstring_sum_cons_to_sum c ls : ##(c :: ls) ≡ (↑c) + ##ls.
Proof.
  unfold cstring_sum; reflexivity.
Qed.

Lemma cstring_sum_app_to_sum ls ls' : ##(ls ++ ls') ≡ ##ls + ##ls'.
Proof.
  unfold cstring_sum.
  rewrite map_app.
  rewrite term_sum_app.
  reflexivity.
Qed.

(* used *)
Lemma leq_leq__sum_leq (t1 t2 t3 : ka_term T) : t1 ≤ t3 -> t2 ≤ t3 -> t1 + t2 ≤ t3.
Proof.
  move=> H G.
  unfold ka_leq in *.
  rewrite Plus_Assoc.
  rewrite H; assumption.
Qed.

(* unused *)
Lemma leq_leq_plus' (t1 t2 t3 : ka_term T) : t1 ≤ t2 ∨ t1 ≤ t3 -> t1 ≤ t2 + t3.
Proof.
  move=> [H | H]; [| rewrite Plus_Com]; apply leq_leq_plus; assumption.
Qed.

Lemma s_in_list__s_leq_sum c ls :
  In c ls -> ↑c ≤ ##ls.
Proof.
  move=> H.
  unfold ka_leq.
  induction ls as [|s ls IHls].
  - contradiction.
  - destruct H as [H | H].
    + subst. rewrite cstring_sum_cons_to_sum.
      rewrite -Plus_Assoc.
      rewrite [X in _+X] Plus_Com.
      rewrite Plus_Assoc.
      rewrite Plus_Idemp.
      reflexivity.
    + apply IHls in H.
      rewrite cstring_sum_cons_to_sum.
      rewrite -[X in _ ≡ _ + X] H.
      rewrite Plus_Assoc.
      reflexivity.
Qed.

Lemma lang_interp_subset__term_leq : ∀ ls ls',
  (∀ s, s ∈ ##ls -> s ∈ ##ls' ) ->
    ##ls ≤ ##ls'.
Proof.
  move=> ls ls'.
  induction ls as [| c ls IHls];
  move=> H.
  - unfold cstring_sum; simpl; apply zero_leq_anything.
  - rewrite cstring_sum_cons_to_sum.
    assert ( G : ∀ s, s ∈ ##ls -> s ∈ ##ls').
    {
      move=> s G.
      apply H.
      simpl; unfold ka_pred_add.
      intuition.
    }
    apply IHls in G.
    specialize (H c).
    rewrite string_interp_in_list in H.
    simpl in H.
    assert (K : c = c ∨ In c ls). { intuition. }
    apply H in K.
    rewrite string_interp_in_list in K.
    apply s_in_list__s_leq_sum in K.
    apply leq_leq__sum_leq; assumption.
Qed.

Fixpoint below_one (t : ka_term T) :=
  match t with
  | K_Zero => true
  | K_One => true
  | L _ => false
  | R _ => false
  | K_Plus t1 t2 => below_one t1 && below_one t2
  | K_Dot t1 t2 => empty_bool t1 || empty_bool t2 || below_one t1 && below_one t2
  | K_Star t => empty_bool t
  end.

Lemma empty_bool_below_one t : empty_bool t = true → below_one t = true.
Proof.
elim: t => //=.
- by move=> t1 IH1 t2 IH2 /andb_true_iff [/IH1 -> /IH2 ->].
- move=> t1 IH1 t2 IH2 /orb_true_iff [->|->] //=.
  by rewrite orb_true_r.
Qed.

Global Instance below_one_proper : Proper (@ka_eq T ==> eq) below_one.
Proof.
move=> t1 t2; elim: t1 t2 / => //=.
- congruence.
- congruence.
- by move=> t11 t12 e1 -> t21 t22 e2 ->; rewrite e1 e2.
- by move=> ?? {2}->.
- move=> t; rewrite orb_false_r andb_true_r.
  case e: empty_bool => //=.
  by rewrite empty_bool_below_one.
- move=> t; case e: empty_bool => //=.
  by rewrite empty_bool_below_one.
- by move=> t; rewrite orb_true_r.
- move=> t1 t2 t3.
  case e1: (empty_bool t1) => //=.
  case e2: (empty_bool t2) => //=.
  case e3: (empty_bool t3) => //=.
  by rewrite andb_assoc.
- by move=> ??; rewrite andb_comm.
- by move=> ???; rewrite andb_assoc.
- by move=> ?; rewrite andb_diag.
- move=> t1 t2 t3.
  case e1: (empty_bool t1) => //=.
  case e2: (empty_bool t2) => //=.
    by rewrite (empty_bool_below_one e2) andb_true_l.
  case e3: (empty_bool t3) => //=.
    by rewrite (empty_bool_below_one e3) !andb_true_r.
  by case: (below_one t1).
- move=> t1 t2 t3.
  case e1: (empty_bool t1) => //=.
    by rewrite (empty_bool_below_one e1) /=.
  case e2: (empty_bool t2) => //=.
    by rewrite (empty_bool_below_one e2) !andb_true_r.
  case e3: (empty_bool t3) => //=.
  case: (below_one t3).
  + by rewrite !andb_true_r.
  + by rewrite !andb_false_r.
- move=> t; rewrite orb_false_r.
  case e: empty_bool => //=.
  by rewrite andb_false_r.
Qed.

Lemma below_oneP t : below_one t = true ↔ t ≡ 0 ∨ t ≡ 1.
Proof.
split => [|- [->|->] //=].
elim: t => //=; eauto.
- move=> t1 IH1 t2 IH2 /andb_true_iff [/IH1 H1 /IH2 H2].
  rewrite -[t1 + t2]ka_simplE.
  case: H1 H2 => [] -> [] -> /=; eauto.
  + by rewrite Plus_Id; eauto.
  + by rewrite Plus_Id; eauto.
  + by rewrite Plus_Id'; eauto.
  + by rewrite Plus_Idemp; eauto.
- move=> t1 IH1 t2 IH2 /orb_true_iff [].
  + by case/orb_true_iff=> [] /empty_boolP ->;
    rewrite ?Dot_Z1 ?Dot_Z2; eauto.
  + case/andb_true_iff=> /IH1 [] -> /IH2 [] ->.
    * by rewrite Dot_Z1; eauto.
    * by rewrite Dot_Z2; eauto.
    * by rewrite Dot_Z1; eauto.
    * by rewrite Dot_Id1; eauto.
- move=> t IH /empty_boolP ->; right.
  by rewrite Star Dot_Z2 Plus_Id'.
Qed.


Lemma cstring_app_commute : ∀ l1 l2,
  ##(l1 ++ l2) ≡ (##l1) + (##l2).
Proof.
  intros.
  induction l1 as [| c1 l1 IHl1].
  + simpl.
    unfold cstring_sum; simpl.
    rewrite Plus_Id; reflexivity.
  + simpl. unfold cstring_sum. simpl.
    unfold cstring_sum in IHl1.
    rewrite IHl1.
    apply Plus_Assoc.
Qed.

Lemma zero_star : (@K_Zero T)✶ ≡ @K_One T.
Proof.
  rewrite Star.
  rewrite Dot_Z2.
  rewrite Plus_Com.
  rewrite Plus_Id.
  reflexivity.
Qed.

Lemma one_star : (@K_One T)✶ ≡ @K_One T.
Proof.
  assert (H : (@K_One T) ≤ (@K_One T)✶).
  { unfold ka_leq. rewrite Plus_Com.
    rewrite [X in _ + X ≡ X] Star.
    rewrite Plus_Assoc.
    rewrite Plus_Idemp.
    reflexivity. }
  apply leq_antisym; try assumption.
  unfold ka_leq in *.
Admitted.

Lemma star_term_interp_empty : ∀ (t : ka_term T),
  ([], []) ∈ t✶.
Proof.
  intros t.
  exists 0%nat.
  reflexivity.
Qed.

Lemma finite_build_term side s :
  side = L ∨ side = R → finite_bool (build_term side 1 s) = true.
Proof.
move=> e; elim: s => //= x s ->.
by case: e => -> /=; rewrite orb_true_r.
Qed.

Lemma finite_string_to_ka_term s : finite_bool (↑s) = true.
Proof.
case: s => s1 s2 /=.
rewrite !finite_build_term ?orb_true_r; eauto.
Qed.

Lemma finite_cstring_sum ls : finite_bool (cstring_sum ls) = true.
Proof.
by elim: ls => //= l ls ->; rewrite finite_string_to_ka_term.
Qed.

Theorem finite_def' t : finite_bool t = true ↔  ∃ ls, t ≡ cstring_sum ls.
Proof.
split => [|[ls ->]]; last by rewrite finite_cstring_sum.
elim: t => //=.
- by move=> _; exists [].
- by move=> _; exists [([], [])]; rewrite /cstring_sum /= Dot_Id1 Plus_Id'.
- move=> x _; exists [([x], [])]; rewrite /cstring_sum /=.
  by rewrite !Dot_Id1 Plus_Id'.
- move=> x _; exists [([], [x])]; rewrite /cstring_sum /=.
  by rewrite Dot_Id1 Dot_Id2 Plus_Id'.
- move=> t1 IH1 t2 IH2 /andb_true_iff [fin1 fin2].
  have [[ls1 e1] [ls2 e2]] := (IH1 fin1, IH2 fin2).
  by exists (ls1 ++ ls2); rewrite e1 e2 cstring_app_commute.
- move=> t1 IH1 t2 IH2 /orb_true_iff [] H.
  + exists []; case/orb_true_iff: H=> /empty_boolP ->;
    by rewrite ?Dot_Z1 ?Dot_Z2.
  + case/andb_true_iff: H => fin1 fin2.
    have [[ls1 e1] [ls2 e2]] := (IH1 fin1, IH2 fin2).
    exists (concat (map (λ s1, map (λ s2, pair_append s1 s2) ls2) ls1)).
    rewrite {}e1 {}e2.
    elim: ls1 {IH1 IH2 t1 t2 fin1 fin2} => //= [|s1 ls1 IH1] in ls2 *.
      by rewrite Dot_Z2.
    rewrite /cstring_sum /= Dist_R IH1 map_app term_sum_app.
    rewrite map_map.
    suff ->: string_to_ka_term s1 ⋅ cstring_sum ls2 ≡
      term_sum (map (λ s2, string_to_ka_term (pair_append s1 s2)) ls2) by [].
    elim: ls2 {IH1 ls1} => [|s2 ls2 IH] //=.
      by rewrite Dot_Z1.
    by rewrite /cstring_sum /= Dist_L IH string_to_term__pair_append__commute.
- move=> t _ /empty_boolP e; exists [([], [])]; rewrite {}e.
  by rewrite Star Dot_Z2 Plus_Id' /cstring_sum /= Dot_Id1 Plus_Id'.
Qed.

Theorem problem : ¬ ∃ ls, 1 ✶ ≡ cstring_sum ls.
Proof. by move=> /finite_def' /=. Qed.

(* Corollary 7' *)
Theorem finite_terms_interp__equiv t t' : finite_bool t = true ->
  finite_bool t' = true ->
    (∀ s, s ∈ t <-> s ∈ t') ->
      t ≡ t'.
Proof.
  move=> H1 H2 H3.
  apply finite_def' in H1 as [l1 H1].
  apply finite_def' in H2 as [l2 H2].
  (* QUEST: this series of asserts is annoying...how better? *)
  assert (G : ∀ s, s ∈ ##l1 <-> s ∈ ## l2).
  {
    move=> s;
    rewrite -H1; rewrite -H2;
    apply H3.
  }
  assert (G1 : ∀ s, s ∈ ##l1 -> s ∈ ## l2).
  { apply G. }
  assert (G2 : ∀ s, s ∈ ##l2 -> s ∈ ## l1).
  { apply G. }
  apply lang_interp_subset__term_leq in G1.
  apply lang_interp_subset__term_leq in G2.
  by rewrite H1; rewrite H2; apply leq_antisym.
Qed.

(* Definition finite_term t := ∃ ls, ∀ s, In s ls <-> lang_interp t s.

Lemma finite_terms__finite_sum : ∀ t t', finite_term t ∧ finite_term t' -> finite_term (t + t').
Proof.
  intros t t' [[l1 H1] [l2 H2]].
  unfold finite_term.
  simpl.
  unfold ka_pred_add.
  exists (l1 ++ l2).
  intros s.
  split.
  + intros H.
    apply in_app_or in H as [H | H];
    [apply H1 in H | apply H2 in H];
    intuition.
  + intros [H | H]; apply in_or_app;
    [apply H1 in H | apply H2 in H];
    intuition.
Qed. *)

(* QUEST: How to allow term_list_to_term to be generic here? *)

(* Definition C_M (P : list mm2_instr) := *)

(* Fixpoint R_M' (P' P : list mm2_instr) (n : nat) := match P with
  | [] => 0
  | hd :: tl => (interp n P) ⋅ (L (Q_M n)) + R_M' tl P (S n)
  end. *)

(* Definition R_M (P : list mm2_instr) := R_M' P P 1. *)

(* Fixpoint C_M' (P : list mm2_instr) (n : nat) := match P with
  | [] => 0
  | _::tl => L (Q_M n) + C_M' tl (S n)
  end. *)

(* Definition C_M (P : list mm2_instr) := (L a)✶ ⋅ (L b)✶ ⋅ (C_M' P 1). *)

Lemma pull_L_forward (x y : T) (t : ka_term T) : R x ⋅ (L y ⋅ t) ≡ L y ⋅ (R x ⋅ t).
Proof.
  repeat (rewrite Dot_Assoc).
  by rewrite -LR_Com.
Qed.

(* I think in regular KA this might work, but maybe not in pre-KA *)
Lemma proj_com (t t' : ka_term T) : (π_l t) ⋅ (π_r t') ≡ (π_r t') ⋅ (π_l t).
Proof.
  elim: t.
  - by rewrite Dot_Z2; rewrite Dot_Z1.
  - by rewrite Dot_Id2; rewrite Dot_Id1.
  - move=> t /=. elim: t'.
    + by rewrite Dot_Z2; rewrite Dot_Z1.
    + by rewrite Dot_Id2; rewrite Dot_Id1.
    + move=> t' /=; by rewrite Dot_Id2; rewrite Dot_Id1.
    + move=> t' /=; by rewrite LR_Com.
    + move=> t1 H1 t2 H2 /=; rewrite Dist_L; rewrite Dist_R.
      by rewrite H1; rewrite H2.
    + move=> t1 H1 t2 H2 /=.
      rewrite Dot_Assoc.
      rewrite H1.
      rewrite -Dot_Assoc.
      rewrite H2.
      by rewrite Dot_Assoc.
    + move=> t' H /=.
Admitted.

Lemma proj_concat (t : ka_term T) : t ≡ (π_l t) ⋅ (π_r t).
Proof.
  elim: t.
  - by rewrite Dot_Z2.
  - by rewrite Dot_Id2.
  - move=> t; by rewrite Dot_Id1.
  - move=> t; by rewrite Dot_Id2.
  - move=> t1 H1 t2 H2 /=.
    rewrite Dist_R; repeat (rewrite Dist_L).
    rewrite Plus_Assoc.
    rewrite [X in X + _ ≡ _] H1.
    rewrite [X in _ + X ≡ _] H2.
    admit.
  - move=> t1 H1 t2 H2 /=.
    rewrite [X in X ⋅ _ ≡ _] H1.
    rewrite [X in _ ⋅ X ≡ _] H2.
    repeat (rewrite Dot_Assoc).
    rewrite - Dot_Assoc.
    rewrite - Dot_Assoc.
    rewrite [X in _ ⋅ X ≡ _] Dot_Assoc.
    rewrite LR_Com.

End Theory.

Ltac sep_lr := repeat (rewrite pull_L_forward).

(* -------------- *)

Definition R_M (P : list mm2_instr) :=
   term_sum (map_indexed interp_single P).

(* Local Open Scope ka_scope. *)

Example string_to_ka_term__test1 :
  string_to_ka_term ([a; b; a; a], [a; b; a; a]) ≡ (lr a ⋅ lr b ⋅ lr a ⋅ lr a).
Proof.
  simpl; unfold lr_term.
  repeat (rewrite Dot_Id1).
  repeat (rewrite -Dot_Assoc).
  by sep_lr.
Qed.


Example string_to_ka_term__test2 :
  string_to_ka_term ([a; b; c_1], [a; b; c_1]) ≡ lr a ⋅ lr b ⋅ lr c_1.
Proof.
  simpl; unfold lr_term.
  repeat (rewrite Dot_Id1).
  repeat (rewrite -Dot_Assoc).
  by sep_lr.
Qed.

Check lang_interp.
Theorem term_leq_R_M__in_lang_interp : ∀ P s s', ((string_to_ka_term ([s], [])) ⋅ (string_to_ka_term ([], [s'])) ≤ R_M P <-> lang_interp (R_M P) ([s], [s']))%ka.
Proof.
  simpl; split; intros.
  - unfold R_M.

Fixpoint to_term (f : T -> ka_term T) (s : list T) :=
  match s with
  | n :: rest => (f n)⋅(to_term f rest)
  | [] => 1
  end.

(* how to make T implicit here? it is added explicitly after End Theory. *)
Definition step_relation (s s' : list T) (e : ka_term T) :=
  (to_term L s) ⋅ (to_term R s') ≤ e.

Definition C_M n := (lr a)✶⋅(lr b)✶⋅(lr (Q_M n)).

(* Inductive T_M :=
  | cm n (H : C_M n) : T_M
  | c0 c_0 : T_M
  | c1 c_1 : T_M
. *)

Definition R_M n1 n2 :=
  (*Inc(1, q)*)   R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M n1) ⋅ L (Q_M n1) +
  (*Inc(2, q)*)   (lr a)✶ ⋅ R b ⋅ (lr b)✶ ⋅ R (Q_M n1) ⋅ L (Q_M n1)+
  (*If(1,q1,q2)*) (lr b)✶ ⋅ R (Q_M n1) + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M n2) +
  (*If(2,q1,q2)*) (lr a)✶ ⋅ R (Q_M n1) + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ R (Q_M n2) +
  (*Halt(0)*)     R c_0 +
  (*Halt(1)*)     R c_1
  .

Print R_M.

Fixpoint power_list {T} (x:T) n :=
  match n with
  | 0%nat => []
  | S n => x :: (power_list x n)
  end.

Definition c_m_form_list n m i := power_list a n ++ (power_list b m) ++ [Q_M i].

(* Definition R_M := *)

(* Lemma step_form : ∀ s s' *)

End Theory.
Local Open Scope ka_scope.
Print step_relation.

Locate "lr".
Lemma step_form : ∀ s s' n1 n2,
  step_relation Σ_M s s' (R_M n1 n2)
    -> ∃ n m i, s = c_m_form_list n m i /\ (to_term Σ_M lr_term s) ≤ C_M i.
Proof.
  intros.
  unfold step_relation in H.
  unfold R_M in H.
  unfold C_M.
  unfold c_m_form_list.
  (* exists n1; exists n2; exists n2. *)
Admitted.

Example ex_to_term : step_relation Σ_M [a; b; c_1] [a; b; c_1]
  ((lr a)⋅(lr b)⋅(lr c_1)).
Proof.



Section Canonicalization.

Fixpoint freeQ_L (e : ka_term T) :=
  match e with
  | L _ => false
  | x + y => (freeQ_L x) && (freeQ_L y)
  | x ⋅ y => (freeQ_L x) && (freeQ_L y)
  | _ => true
  end.

Fixpoint freeQ_Plus (e : ka_term T) :=
  match e with
  | _ + _ => false
  | x ⋅ y => (freeQ_Plus x) && freeQ_Plus y
  | _ => true
  end.

Fixpoint collect_L_R (e : ka_term T) (accL accR : list (ka_term T)) :=
  match e with
  | x ⋅ y =>
    (match collect_L_R x accL accR with
    | (accL, accR) =>
      collect_L_R y accL accR
    end)
  | L x => ((L x)::accL, accR)
  | R x => (accL, (R x)::accR)
  | 0 => (0::accL, [])
  | _ => (accL, accR)
  end.

Fixpoint compose acc term :=
  match acc with
  | [] => term
  | K_Zero::rest => K_Zero
  | x::rest => (compose rest (@K_Dot T x term))
  end.

Definition compose_L_R accL_accR :=
  match accL_accR with
  (* | ([], _) => 0
  | (_, []) => 0 *)
  | (accL, accR) => (compose accL 1) ⋅ (compose accR 1)
  end.

Fixpoint remove_1 e :=
  match e with
  | 1 ⋅ e => remove_1 e
  | e ⋅ 1 => remove_1 e
  | x ⋅ y => (remove_1 x) ⋅ remove_1 y
  | x + y => (remove_1 x) + remove_1 y
  | s => s
  end.

(* is this worth it?? *)
Fixpoint left_assoc e :=
  match e with
  | x ⋅ (y ⋅ z) => (left_assoc x) ⋅ (left_assoc y) ⋅ (left_assoc z)
  (* | x + (y + z) => (left_assoc x) + (left_assoc y) + (left_assoc z) *)
  | t => t
  end.

(* Theorem left_assoc_equiv e : left_assoc e ≡ e.
Proof.
  induction e; try (reflexivity).
  - assert (H : left_assoc (e1 + e2) ≡ (left_assoc e1) + left_assoc e2).
    { simpl. inversion IHe2; subst. compute. }
  rewrite <- IHe1. generalize dependent IHe2.
    induction e2; try reflexivity.
    intros. rewrite <- IHe2.
    simpl.
    compute. *)

(* Definition canonicalize e := left_assoc (remove_1 (compose_L_R (collect_L_R e [] []))).

Theorem canonicalize_equiv e : canonicalize e ≡ e.
Proof.
  induction e; try (compute; reflexivity).
  - unfold canonicalize.
    assert
    unfold collect_L_R.
  assert (H : canonicalize (e1 + e2) ≡ (canonicalize e1) + (canonicalize e2)).
    { rewrite IHe1. rewrite IHe2. compute. }
  unfold canonicalize.
    unfold collect_L_R. *)

End Canonicalization.

Local Open Scope ka_scope.

Example check_canonicalize : canonicalize Σ_M (R a ⋅ L a ⋅ R b ⋅ L b) ≡ L a ⋅ L b ⋅ R a ⋅ R b.
Proof.
  (* simpl. why does simpl not do anything here? compute does more *)
  compute. reflexivity.
Qed.

Theorem canonicalize_equiv :

(* Fixpoint to_L__R (e : ka_term T) :=
  match e with
  | x + y =>
  end.
  match e with
  | (R y) ⋅ (L x) => (L x) ⋅ (R y)
  | (u⋅R y) ⋅ L x => (to_L__R u)⋅L x⋅ R y
  | (u⋅R y) ⋅ ((L x) ⋅ w) => (to_L__R u)⋅L x⋅ R y⋅(to_L__R w)
  | (R y) ⋅ ((L x) ⋅ w) => (L x) ⋅ R y ⋅(to_L__R (w))
  | x + y => (to_L__R x) + (to_L__R y)
  | x ⋅ y => (to_L__R x) ⋅ (to_L__R y)
  | s => s
  end. *)

(* Example to_L__R_ex1 : ∀ x y, to_L__R ((lr x)⋅(lr y)) ≡ (L x)⋅(L y)⋅(R x)⋅(R y).
Proof.
  intros.
  (* unfold lr_term. *)
  reflexivity.
Qed.

Example to_L__R_ex2 : ∀ x y z, to_L__R ((lr x)⋅(lr y)⋅(lr z)) ≡ L x⋅L y⋅L z⋅R x⋅R y⋅R z.
Proof.
  intros.
  simpl. *)



Lemma plus_interleave : ∀ (x y z w : ka_term T), x + y + z + w ≡ x + z + y + w.
Proof.
  intros.
  rewrite <- Plus_Assoc.
  rewrite <- Plus_Assoc.
  assert (G : y + (z + w) ≡ (z + w) + y). { apply Plus_Com. }
  rewrite G.
  assert (H : y + w ≡ w + y). { apply Plus_Com. }
  rewrite <- Plus_Assoc.
  rewrite <- H.
  rewrite Plus_Assoc.
  rewrite Plus_Assoc.
  reflexivity.
Qed.

Lemma extra_one_ignore : forall (x : ka_term T), 1 + 1 + x ≡ 1 + x.
Proof.
  intros.
  rewrite Plus_Idemp.
  reflexivity.
Qed.

Print step_relation.
Locate "lr".




Lemma x_xstar__xtar_x : forall (t : ka_term T), t⋅t✶ ≡ t✶⋅t.
Proof.
  intros.
  induction t.
  - rewrite Dot_Z2. rewrite Dot_Z1. reflexivity.
  - rewrite Dot_Id2. rewrite Dot_Id1. reflexivity.
  - admit.
  - admit.
  - rewrite Dist_R. rewrite Dist_L.
Admitted. (* should follow from t⋅t✶ ≡ t✶ ≡ t✶⋅t *)


Lemma x_x_star : forall (t : ka_term T), t✶ ≡ t✶⋅t.
Proof.
  intros.
  assert (H : t✶ ≤ t✶⋅t).
  {admit. }
  assert (G : t✶⋅t ≤ t✶).
  {admit. }
  apply (leq_antisym _ _ H G).
Admitted.
  (* unfold ka_leq.
  rewrite Plus_Com.
  rewrite star_expand.
  rewrite Dist_R.
  rewrite Dot_Id2.
  rewrite Plus_Assoc.
  rewrite Plus_Assoc.
  rewrite Dist_L.
  rewrite Dot_Id1.
  rewrite Dot_Assoc.
  rewrite <- star_expand.
  assert (H : t ≡ t⋅1).
  { symmetry. apply Dot_Id1. }
  rewrite <- Dot_Assoc.
  rewrite H.
  rewrite <- Dot_Assoc.
  rewrite <- Dist_L.
  rewrite <- H.
  rewrite Dot_Id2.
  rewrite <- star_expand.
  Check star_leq.

  replace (t✶) with (1 + t⋅t✶).
  apply Star. *)


Inductive step_relation :=
  |

(* Inductive disjoint_union {T} : Type :=
  | l (t : T)
  | r (t : T).

(* Coercion K_Var : Σ_M >-> ka_term. QUEST: how to make this work? *)

Inductive commute_on_disjoint_union {T} : disjoint_union -> disjoint_union -> Prop :=
  | commute_refl : Reflexive (@commute_on_disjoint_union T)
  | commute_sym : Symmetric (@commute_on_disjoint_union T)
  | lr_com (s s' : T) : commute_on_disjoint_union (l s) (r s').

Print ka_term.

Check term_to_disjoint_term ([[a]]⋅[[b]]⋅[[Q_M 1]]). *)
(* Example ex_1 :
  term_to_disjoint_term ([[a]]⋅[[b]]⋅[[Q_M 1]])
  ≡ [[l a]]⋅[[r a]]⋅[[l b]]⋅[[r b]]⋅[[l (Q_M 1)]]⋅[[r (Q_M 1)]].
  Proof. simpl. Unset Printing Notations. *)


(* Print mm2_instr.
(* Unset Printing Notations. *)
Print mm2_atom.
Locate "//".

Print mm2_stop. *)

Definition interpret_mm2_instr (pc1 pc2 : nat) (i : mm2_instr) :=
  match i with
  | mm2_inc_a => (lr a)⋅((lr a)✶)⋅((lr b)✶)⋅(R (Q_M pc1))
  | mm2_inc_b => ((lr a)✶)⋅(R b)⋅((lr b)✶)⋅(R (Q_M pc1))
  | mm2_dec_a n => ((lr b)✶)⋅(R (Q_M pc1)) + (L a)⋅((lr a)✶)⋅((lr b)✶)⋅(R (Q_M pc2))
  | mm2_dec_b n => ((lr a)✶)⋅(R (Q_M pc1)) + ((lr a)✶)⋅(L b)⋅((lr b)✶)⋅(R (Q_M pc2))
  end.

Check interpret_mm2_instr.

Print mm2_atom.

(* Definition interpret_mm2 (i : mm2_atom) :=
  match i with
    | _ => 1
  end.
Check interpret_mm2. *)

(* ------- testing out some lemmas on the ka_eq and ka_term types ------- *)

Local Open Scope ka_scope.

Global Instance KatCC_Eq_equiv : ∀ T, Equivalence (@ka_eq T).
Proof.
  split; constructor; try assumption.
  apply Ka_sym, Ka_trans with y; auto.
Qed.

Lemma ka_power_decomp : forall T (kat : ka_term T) n m,
  ka_power kat (n + m) ≡ K_Dot (ka_power kat n) (ka_power kat m).
Proof.
  intros.
  induction n.
  - simpl. rewrite Dot_Id2. reflexivity.
  - simpl. rewrite IHn. rewrite Dot_Assoc. reflexivity.
Qed.

Lemma test : forall T (t : ka_term T), t + 0 ≡ t.
Proof.
intros. rewrite Plus_Com. by constructor. Qed.

Lemma plus_assoc_swap1 : ∀ T (x y z : ka_term T),
  x + (y + z) ≡ x + (z + y).
Proof.
  intros. assert (H: y+z ≡ z + y).
  - apply Plus_Com.
  - rewrite H. reflexivity.
Qed.

Lemma plus_assoc_swap2 : ∀ T (x y z : ka_term T),
  x + (y + z) ≡ (x + z) + y.
Proof.
  intros. assert (H: y+z≐z+y).
  - apply Plus_Com.
  - rewrite H. apply Plus_Assoc.
Qed.

(* QUEST: why does this struggle with typing? *)
Lemma test_1 : forall (T:Type) (x y z : ka_term T), x ≤ y -> (x + z ≡ (x + y) + z).
Proof.
  intros. unfold ka_leq in H. rewrite Plus_Com in H. rewrite H. reflexivity.
Qed.

Global Instance leq_trans : ∀ T, Transitive (@ka_eq T).
Proof.
  unfold Transitive. intros.
  apply Ka_trans with y; assumption.
Qed.

(* QUEST: in Arthur's setup, he has TEStar1, TEStarL, TEStarR.
In the present setup, I'm not sure how to translate or derive these... *)
Lemma one_star : ∀ (T : Type) (x : ka_term T), (1 ≤ x✶).
Proof.
intros. compute. rewrite (Ka_Star x). Abort. (* HELP! -- can't be helped *)


(* ------- Testing Example 1 ------- *)
(* QUEST: How to do this? -- don't, its very hard *)
(* Inductive N_Top_Bot : Type :=
  | Top
  | Bot
  | X (n : nat)
.

Theorem n_top_bot_ka : @ka_eq N_Top_Bot. *)
