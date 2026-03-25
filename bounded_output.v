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
From kacc Require Import repr_rel.

Section BoundedOutput.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Implicit Types (e : ka_term (list T * list T)) (L : ka_term (list T)).

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


End BoundedOutput.
