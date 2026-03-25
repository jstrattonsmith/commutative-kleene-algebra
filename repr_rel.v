Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite gmap mapset.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import utils algebra pre_ka lang automata.

Section RepresentableRelations.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Implicit Types (e : ka_term (list T * list T)) (L : ka_term (list T)).

Definition diff : ka_term (list T * list T) :=
  let diffs := filter (λ '(x, y), bool_decide (x ≠ y)) (enum (T * T)) in
  ⨆ (map (λ '(x, y), Unit ([x], [y])) diffs).

Record repr_rel e L : Type := {
  repr_rel_dom : ka_term_proj1 e ⊑ L;
  repr_rel_cod : ka_term_proj2 e ⊑ L;
  next : list T → list (list T);
  next_spec : ∀ sl sr, sr ∈ next sl ↔ Unit (sl, sr) ⊑ e;
  residue : ka_term (list T * list T);
  expand_rel :
    ∀ xs : list T,
      Unit (1, xs) ⋅ e ⊑
        Unit (xs, xs) ⋅ ⨆ (map (λ ys, Unit (1, ys)) (next xs))
        ⊔ ka_term_diag pseudo_top ⋅ diff ⋅ residue;
}.

(** Lifting a finite set of strings to a KA term. *)

Definition strings_r (σ : list (list T)) : ka_term (list T * list T) :=
  ⨆ (map (λ xs, Unit (1, xs)) σ).

(** Next function: image of a set of strings under a representable relation. *)

Section ReprRelIteration.

Variable e : ka_term (list T * list T).
Variable L : ka_term (list T).
Variable R : repr_rel e L.

Definition next_set (σ : list (list T)) : list (list T) :=
  flat_map (next R) σ.

Definition next_iter (n : nat) (σ : list (list T)) : list (list T) :=
  Nat.iter n next_set σ.

Fixpoint next_lt (n : nat) (σ : list (list T)) : list (list T) :=
  match n with
  | 0 => []
  | S n => next_lt n σ ++ next_iter n σ
  end.

Definition error : ka_term (list T * list T) :=
  ka_term_diag pseudo_top ⋅ diff ⋅ residue R ⋅ star e.

(** Helper: strings_r distributes over append. *)

Lemma strings_r_app (σ1 σ2 : list (list T)) :
  strings_r (σ1 ++ σ2) ≡ strings_r σ1 ⊔ strings_r σ2.
Proof.
by rewrite /strings_r map_app join_list_app.
Qed.

(** Helper: expand_rel summed over a list of strings. *)

Lemma expand_rel_sum (σ : list (list T)) :
  strings_r σ ⋅ e ⊑
    ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r (next_set σ)
    ⊔ ka_term_diag pseudo_top ⋅ diff ⋅ residue R.
Proof.
rewrite /strings_r join_list_left_dist map_map.
apply/join_list_sqsubseteq => _ /elem_of_list_fmap [xs [-> xs_σ]] /=.
etransitivity; first exact: expand_rel R xs.
apply: join_mono; last reflexivity.
apply: pre_ka_mul_mono.
- apply: sqsubseteq_join_list; apply/elem_of_list_fmap; eauto.
- apply/join_list_sqsubseteq => _ /elem_of_list_fmap [ys [-> ys_next]].
  apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
  exists ys; split => //.
  rewrite /next_set; apply/elem_of_list_In/in_flat_map.
  exists xs; split; exact/elem_of_list_In.
Qed.

(** Lemma 21: Iteration of a representable relation.
    For e : Rel(L), there exists ρ such that for every n and finite Σ ⊆ L:
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Next^n(Σ)_r · e* + Σ* · Σ≠ · ρ *)

(** Helper: next_lt (S n) σ is σ ++ next_lt n (next_set σ). *)

Lemma next_iter_succ (n : nat) (σ : list (list T)) :
  next_iter (S n) σ = next_iter n (next_set σ).
Proof. exact: Nat.iter_succ_r. Qed.

Lemma next_lt_succ (n : nat) (σ : list (list T)) :
  next_lt (S n) σ = σ ++ next_lt n (next_set σ).
Proof.
elim: n σ => [|n IHn] σ.
- by simpl; rewrite app_nil_r.
- change (next_lt (S n) σ ++ next_iter (S n) σ =
         σ ++ (next_lt n (next_set σ) ++ next_iter n (next_set σ))).
  rewrite IHn -next_iter_succ.
  by rewrite app_assoc.
Qed.

(** Helper: ⨆(map (λ xs, Unit(xs,xs)) σ) ⊑ pseudo_top *)

Lemma unit_le_pseudo_top (x : list T * list T) : Unit x ⊑ pseudo_top.
Proof.
etransitivity; last exact: pseudo_top_absorb x.
rewrite -{1}[Unit x](right_id 1); apply: pre_ka_mul_mono => //.
exact: pre_ka_one_star.
Qed.

Lemma diag_units_le_pseudo_top (σ : list (list T)) :
  ⨆ (map (λ xs, Unit (xs, xs) : ka_term (list T * list T)) σ) ⊑ pseudo_top.
Proof.
apply/join_list_sqsubseteq => _ /elem_of_list_fmap [xs [-> _]].
exact: unit_le_pseudo_top.
Qed.

Lemma repr_rel_iter (n : nat) (σ : list (list T)) :
  strings_r σ ⋅ star e ⊑
    pseudo_top ⋅ strings_r (next_lt n σ)
    ⊔ pseudo_top ⋅ strings_r (next_iter n σ) ⋅ star e
    ⊔ error.
Proof.
elim: n σ => [|n IH] σ.
- (* Base case: x ⊑ pseudo_top ⋅ x since 1 ⊑ pseudo_top *)
  etransitivity; last (apply: sqsubseteq_join; left;
    apply: sqsubseteq_join; right; reflexivity).
  rewrite -assoc.
  etransitivity; last (apply: pre_ka_mul_mono;
    [exact: pre_ka_one_star | reflexivity]).
  by rewrite left_id.
- (* Inductive step: follow paper proof chain *)
  set σ' := next_set σ.
  set err_base := ka_term_diag pseudo_top ⋅ diff ⋅ residue R.

  (* Step 1: e* = 1 + e · e* *)
  have step1 : strings_r σ ⋅ star e ≡
    strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e.
  { by rewrite {1}pre_ka_star_unfold pre_ka_right_dist right_id assoc. }

  (* Step 2: apply expand_rel_sum *)
  have step2 : strings_r σ ⋅ e ⋅ star e ⊑
    (⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⊔ err_base) ⋅ star e.
  { apply: pre_ka_mul_mono; last reflexivity.
    exact: expand_rel_sum. }

  (* Step 3: distribute · e* *)
  have step3 : (⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⊔ err_base) ⋅ star e ≡
    ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⋅ star e ⊔ err_base ⋅ star e.
  { by rewrite pre_ka_left_dist. }

  (* Step 4: apply IH to σ' *)
  have step4 : strings_r σ' ⋅ star e ⊑
    pseudo_top ⋅ strings_r (next_lt n σ') ⊔
    pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e ⊔ error.
  { exact: IH. }

  (* Step 5: ⨆(diag σ) ⊑ pseudo_top *)
  have step5 : ⨆ (map (λ xs, Unit (xs, xs) : ka_term _) σ) ⊑ pseudo_top.
  { exact: diag_units_le_pseudo_top. }

  (* Step 6: err_base · e* ⊑ error *)
  have step6 : err_base ⋅ star e ⊑ error.
  { rewrite /error /err_base. reflexivity. }

  (* Step 7: pseudo_top · pseudo_top ⊑ pseudo_top *)
  have step7 : pseudo_top ⋅ pseudo_top ⊑ (pseudo_top : ka_term (list T * list T)).
  { exact: pseudo_top_finite _ (pre_ka_one_star _). }

  (* Compose: *)
  rewrite step1 join_sqsubseteq; split.
  + (* strings_r σ ⊑ pseudo_top · strings_r (next_lt (S n) σ) ⊔ ... *)
    etransitivity; last apply: sqsubseteq_join_left.
    etransitivity; last apply: sqsubseteq_join_left.
    rewrite next_lt_succ strings_r_app.
    rewrite -{1}[strings_r σ]left_id.
    apply: pre_ka_mul_mono; first exact: pre_ka_one_star.
    exact: sqsubseteq_join_left.
  + (* strings_r σ · e · e* ⊑ ... *)
    etransitivity; first exact: step2.
    rewrite step3 join_sqsubseteq; split.
    * (* ⨆(diag σ) · strings_r σ' · e* ⊑ ... *)
      rewrite assoc.
      etransitivity.
      { apply: pre_ka_mul_mono; first exact: step5. reflexivity. }
      etransitivity.
      { apply: pre_ka_mul_mono; last exact: step4. reflexivity. }
      rewrite !pre_ka_right_dist !assoc join_sqsubseteq; split; last first.
      -- (* pseudo_top · error ⊑ error *)
         etransitivity; last apply: sqsubseteq_join_right.
         rewrite /error -!assoc.
         apply: pre_ka_mul_mono; last reflexivity.
         apply: pre_ka_mul_mono; last reflexivity.
         apply: pre_ka_mul_mono; last reflexivity.
         exact: step7.
      -- rewrite join_sqsubseteq; split.
         ++ (* pseudo_top · pseudo_top · strings_r(next_lt n σ') ⊑ pseudo_top · strings_r(next_lt (S n) σ) *)
            etransitivity; last apply: sqsubseteq_join_left.
            etransitivity; last apply: sqsubseteq_join_left.
            rewrite -assoc.
            etransitivity.
            { apply: pre_ka_mul_mono; first exact: step7. reflexivity. }
            apply: pre_ka_mul_mono; first reflexivity.
            rewrite next_lt_succ strings_r_app.
            exact: sqsubseteq_join_right.
         ++ (* pseudo_top · pseudo_top · strings_r(next_iter n σ') · e* ⊑ pseudo_top · strings_r(next_iter (S n) σ) · e* *)
            etransitivity; last apply: sqsubseteq_join_left.
            etransitivity; last apply: sqsubseteq_join_right.
            rewrite -!assoc.
            etransitivity.
            { apply: pre_ka_mul_mono; first exact: step7. reflexivity. }
            rewrite !assoc.
            apply: pre_ka_mul_mono; last reflexivity.
            apply: pre_ka_mul_mono; first reflexivity.
            rewrite next_iter_succ. reflexivity.
    * (* err_base · e* ⊑ error ⊑ ... *)
      etransitivity; first exact: step6.
      exact: sqsubseteq_join_right.
Qed.

(** Theorem 22: If Next^n_e(Σ) = ∅, then
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Σ≠ · ρ *)

Lemma repr_rel_iter_empty (n : nat) (σ : list (list T)) :
  next_iter n σ = [] →
  strings_r σ ⋅ star e ⊑
    pseudo_top ⋅ strings_r (next_lt n σ) ⊔ error.
Proof.
move=> Hempty.
etransitivity; first exact: repr_rel_iter n σ.
rewrite Hempty /strings_r /=.
(* The middle term has ⨆ [] = ⊥, so pseudo_top ⋅ ⊥ ⋅ star e ≡ ⊥ *)
rewrite (@right_absorb _ _ (⊥ : ka_term _) _ _) (@left_absorb _ _ (⊥ : ka_term _) _ _).
by rewrite right_id.
Qed.

End ReprRelIteration.

(** Definition 28: Bounded-output terms.

    A term [e] over [Σ ⊕ Σ] (represented as [ka_term (list T * list T)]) has
    bounded output with fanout [k] if, for every string [s] in its language,
    the length of the right projection is bounded by [(|π_l(s)| + 1) * k].

    Intuitively, this means the term represents a relation that maps each
    input string to only finitely many output strings of bounded length. *)

Definition bounded_output_with (k : nat) (e : ka_term (list T * list T)) : Prop :=
  ∀ sl sr, Unit (sl, sr) ⊑ e → length sr ≤ (length sl + 1) * k.

Definition bounded_output (e : ka_term (list T * list T)) : Prop :=
  ∃ k, bounded_output_with k e.

(** Lemma 29: If [e] has bounded output with fanout [k] and [Σ] is a finite
    set of strings, then [Next_e(Σ)] is finite.  More precisely, if
    [s ∈ Next_e(Σ)], then [|s| ≤ (m + 1) * k] where
    [m = max { |s'| | s' ∈ Σ }]. *)

Lemma bounded_output_next_bound k (e : ka_term (list T * list T)) sl sr sr' :
  bounded_output_with k e →
  Unit (sl ++ sr, sr') ⊑ e →
  length sr' ≤ (length sl + length sr + 1) * k.
Proof.
move=> Hbo Hin.
have := Hbo _ _ Hin.
by rewrite List.length_app.
Qed.

(** Lemma 30 (partial): Bounded-output is preserved by join. *)

Lemma bounded_output_with_bot k :
  bounded_output_with k (⊥ : ka_term (list T * list T)).
Proof.
move=> sl sr /l_alt.
by rewrite pre_ka_morphism_bottom.
Qed.

Lemma bounded_output_with_join k1 k2 e1 e2 :
  bounded_output_with k1 e1 →
  bounded_output_with k2 e2 →
  bounded_output_with (max k1 k2) (e1 ⊔ e2).
Proof.
move=> H1 H2 sl sr /l_alt.
rewrite semi_lattice_morphism_join.
case=> /l_alt Hin.
- have := H1 _ _ Hin.
  have : k1 ≤ max k1 k2 by lia.
  by nia.
- have := H2 _ _ Hin.
  have : k2 ≤ max k1 k2 by lia.
  by nia.
Qed.

Lemma bounded_output_join e1 e2 :
  bounded_output e1 →
  bounded_output e2 →
  bounded_output (e1 ⊔ e2).
Proof.
move=> [k1 H1] [k2 H2].
exists (max k1 k2).
exact: bounded_output_with_join.
Qed.

(** Lemma 30 (partial): Bounded-output is preserved by multiplication. *)

Lemma bounded_output_with_mul k1 k2 e1 e2 :
  bounded_output_with k1 e1 →
  bounded_output_with k2 e2 →
  bounded_output_with (k1 + k2) (e1 ⋅ e2).
Proof.
move=> H1 H2 sl sr /l_alt.
rewrite pre_ka_morphism_mul.
move=> [[sl1 sr1] [[sl2 sr2] [Heq [/l_alt H1' /l_alt H2']]]].
have := H1 _ _ H1'.
have := H2 _ _ H2'.
move: Heq => /leibniz_equiv_iff [/= esl esr].
rewrite esl esr !length_app. nia.
Qed.

Lemma bounded_output_mul e1 e2 :
  bounded_output e1 →
  bounded_output e2 →
  bounded_output (e1 ⋅ e2).
Proof.
move=> [k1 H1] [k2 H2].
exists (k1 + k2).
exact: bounded_output_with_mul.
Qed.

(** Lemma 30 (star case): Bounded-output is preserved by star,
    provided that [|π_l(s)| ≥ 1] for all strings [s ≤ e].
    Under this condition, [e*] has bounded output with fanout [2k]
    when [e] has fanout [k]. *)

Definition left_nonempty (e : ka_term (list T * list T)) : Prop :=
  ∀ sl sr, Unit (sl, sr) ⊑ e → length sl ≥ 1.

Definition left_has_emptyb (e : ka_term (list T * list T)) : bool :=
  has_one (ka_term_proj1 e).

Lemma left_has_emptyb_falseP e :
  left_has_emptyb e = false ↔ left_nonempty e.
Proof.
rewrite /left_has_emptyb /left_nonempty; split.
- move=> Hf sl sr Hin.
  destruct sl as [|x sl']; last by simpl; lia.
  exfalso.
  have : has_one (@ka_term_proj1 (list_monoid T) (list_monoid T) e) = true.
  { apply/has_oneP.
    rewrite -(@pre_ka_morphism_one _ _ (@ka_term_proj1 (list_monoid T) (list_monoid T)) _).
    exact: semi_lattice_morphism_sqsubseteq_proper Hin. }
  by rewrite Hf.
- move=> Hne.
  apply/Bool.not_true_iff_false. move=> /has_oneP /l_alt.
  rewrite l_natural => -[[sl sr] /= [/leibniz_equiv_iff Esl /l_alt Hin]].
  simpl in Esl. subst sl.
  have := Hne _ _ Hin. simpl. lia.
Qed.

Lemma bounded_output_with_star k e :
  bounded_output_with k e →
  left_nonempty e →
  bounded_output_with (2 * k) (star e).
Proof.
move=> Hbo Hne sl sr /l_alt.
rewrite pre_ka_morphism_star.
case=> n; revert sl sr; elim: n => [|n IH] sl sr /=.
- move=> [/leibniz_equiv_iff Esl /leibniz_equiv_iff Esr].
  simpl in Esl, Esr. subst. exact (Nat.le_0_l _).
- move=> [[sl1 sr1] [[sl2 sr2] [/leibniz_equiv_iff [/= esl esr] [/l_alt He Hrec]]]].
  have := Hbo _ _ He.
  have := Hne _ _ He.
  have := IH _ _ Hrec.
  rewrite esl esr !length_app. nia.
Qed.

Lemma bounded_output_star e :
  bounded_output e →
  left_nonempty e →
  bounded_output (star e).
Proof.
move=> [k Hk] Hne.
exists (2 * k).
exact: bounded_output_with_star.
Qed.

(** Bounded-output unit terms. *)

Lemma bounded_output_unit (s : list T * list T) :
  bounded_output (Unit s).
Proof.
destruct s as [s1 s2]; exists (length s2).
move=> sl sr /l_alt /= [/leibniz_equiv_iff Esl /leibniz_equiv_iff Esr].
simpl in Esl, Esr. subst. nia.
Qed.

(** Boolean check for bounded output: traverses the term and verifies
    that every starred subterm satisfies left_nonempty (via left_has_emptyb). *)

Fixpoint bounded_outputb (e : ka_term (list T * list T)) : bool :=
  match e with
  | Unit _ => true
  | ka_term_bottom => true
  | ka_term_join e1 e2 => bounded_outputb e1 && bounded_outputb e2
  | ka_term_mul e1 e2 => bounded_outputb e1 && bounded_outputb e2
  | ka_term_star e => negb (left_has_emptyb e) && bounded_outputb e
  end.

Lemma bounded_outputbP e :
  bounded_outputb e = true → bounded_output e.
Proof.
elim: e.
- move=> s _. exact: bounded_output_unit.
- move=> _. exists 0. exact: bounded_output_with_bot.
- move=> e1 IH1 e2 IH2 /andb_true_iff [/IH1 H1 /IH2 H2].
  exact: bounded_output_join.
- move=> e1 IH1 e2 IH2 /andb_true_iff [/IH1 H1 /IH2 H2].
  exact: bounded_output_mul.
- move=> e IH /andb_true_iff [/negb_true_iff /left_has_emptyb_falseP Hne /IH Hbo].
  exact: bounded_output_star.
Qed.

(** Definition 32: Prefix-free terms. A term [L] is prefix-free if for
    all strings [s1 ≤ L] and [s2 ≤ L], if [s1] is a prefix of [s2],
    then [s1 = s2]. *)

Definition prefix_free (L : ka_term (list T)) : Prop :=
  ∀ s1 s2, Unit s1 ⊑ L → Unit s2 ⊑ L →
    (∃ t, s2 = s1 ++ t) → s1 = s2.

(** Lemma 34 (from paper): A finite-state, bounded-output term whose
    domain and codomain lie in a prefix-free language is representable. *)

Lemma bounded_output_repr_rel e L :
  bounded_output e →
  ka_term_proj1 e ⊑ L →
  ka_term_proj2 e ⊑ L →
  prefix_free L →
  repr_rel e L.
Proof.
Admitted.

End RepresentableRelations.

