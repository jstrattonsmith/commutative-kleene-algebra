(* Pre-KA is complete for star-free terms: a term without star denotes a
   finite language and is pre-KA-equal to the join of its words
   (KA/pre_ka.v's count_finiteP), and joins of words with the same
   language are pre-KA-equal (KA/lang.v's l_inj_finite, Corollary 7).
   This is what lets RegexUnif/Invariant.v produce pre-KA (hence KA)
   proofs of equations it has only checked in languages. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.algebra KA.pre_ka KA.lang.
From kacc Require Import RegexUnif.Syntax.

Fixpoint star_free {T : Type} (e : ka_term T) : Prop :=
  match e with
  | Unit _ | ka_term_bottom => True
  | ka_term_join e1 e2 | ka_term_mul e1 e2 => star_free e1 ∧ star_free e2
  | ka_term_star _ => False
  end.

Section StarFree.

Context {T : monoid}.

Implicit Types e : ka_term T.

Lemma star_free_count e : star_free e → count_term e ⊑ 1.
Proof.
elim: e => [x||e1 IH1 e2 IH2|e1 IH1 e2 IH2|e IH] /=.
- by move=> _; reflexivity.
- by move=> _; exact: bottom_sqsubseteq.
- by case=> /IH1 H1 /IH2 H2; rewrite join_sqsubseteq.
- by case=> /IH1 H1 /IH2 H2; apply/count_mul_one; right.
- by [].
Qed.

Lemma star_free_finite e : star_free e → ∃ xs, e ≡ ⨆ x ∈ xs, Unit x.
Proof. by move=> /star_free_count /count_finiteP. Qed.

Lemma star_free_l_inj e1 e2 :
  star_free e1 → star_free e2 → l e1 ≡ l e2 → e1 ≡ e2.
Proof.
move=> /star_free_finite [xs ->] /star_free_finite [ys ->].
exact: l_inj_finite.
Qed.

Lemma star_free_join_list {A} (f : A → ka_term T) xs :
  (∀ x, x ∈ xs → star_free (f x)) → star_free (join_list f xs).
Proof.
elim: xs => //= x xs IH H; split.
- exact: H (elem_of_list_here _ _).
- by apply: IH => y Hy; apply: H; apply: elem_of_list_further.
Qed.

Lemma star_free_mul_list {A} (f : A → ka_term T) xs :
  (∀ x, x ∈ xs → star_free (f x)) → star_free (mul_list f xs).
Proof.
elim: xs => //= x xs IH H; split.
- exact: H (elem_of_list_here _ _).
- by apply: IH => y Hy; apply: H; apply: elem_of_list_further.
Qed.

End StarFree.

Section SubstStarFree.

Context {A : setoid}.

Lemma star_free_nth (σ : list (ka_term (list_monoid A))) i :
  Forall star_free σ → star_free (nth i σ ⊥).
Proof.
elim: σ i => [|e σ IH] i; first by case: i.
by move=> /Forall_cons [He Hσ]; case: i => [|i] //=; apply: IH.
Qed.

Lemma star_free_subst (σ : list (ka_term (list_monoid A))) (e : uterm) :
  Forall star_free σ → star_free e → star_free (subst σ e).
Proof.
move=> Hσ; rewrite /subst; elim: e => //=.
- move=> w _; apply: star_free_mul_list => - [a|i] _ //=.
  exact: star_free_nth.
- by move=> e1 IH1 e2 IH2 [/IH1 ? /IH2 ?].
- by move=> e1 IH1 e2 IH2 [/IH1 ? /IH2 ?].
Qed.

Lemma nth_map_seq {X} (f : nat → X) N i d :
  i < N → nth i (map f (seq 0 N)) d = f i.
Proof.
move=> Hi; rewrite (nth_indep _ d (f 0)) ?length_map ?length_seq //.
by rewrite map_nth seq_nth.
Qed.

(* A language-level solution by star-free terms is a pre-KA solution, as
   long as the equations themselves are star-free. The substitution is
   given as a function and cut down to the variables that occur. *)
Lemma unif_of_lsolves (f : nat → ka_term (list_monoid A)) eqs :
  (∀ i, star_free (f i)) →
  (∀ p, p ∈ eqs → star_free p.1 ∧ star_free p.2) →
  lsolves (λ i, l (f i)) eqs → unif preka_eqv eqs.
Proof.
move=> Hf Heqs Hsol.
set vs := eqs ≫= λ p : ueq, uvars p.1 ++ uvars p.2.
set N := S (list_max vs).
have HN p i : p ∈ eqs → i ∈ uvars p.1 ++ uvars p.2 → i < N.
{ move=> Hp Hi; rewrite /N; apply/Nat.lt_succ_r.
  have /Forall_forall Hmax := proj1 (list_max_le vs _) (le_n _).
  apply: Hmax.
  by rewrite /vs elem_of_list_bind; exists p. }
exists (map f (seq 0 N)) => p Hp.
have Hσ : Forall star_free (map f (seq 0 N))
  by apply/Forall_map/Forall_forall => i _.
have [Hp1 Hp2] := Heqs p Hp.
apply: star_free_l_inj; try exact: star_free_subst.
have Hext e : (∀ i, i ∈ uvars e → i < N) →
  lsubst (λ i, l (nth i (map f (seq 0 N)) ⊥)) e ≡ lsubst (λ i, l (f i)) e.
{ by move=> He; apply: lsubst_ext => i /He Hi; rewrite nth_map_seq. }
have H1 := Hext p.1 (λ i Hi,
  HN p i Hp (proj2 (elem_of_app _ _ _) (or_introl Hi))).
have H2 := Hext p.2 (λ i Hi,
  HN p i Hp (proj2 (elem_of_app _ _ _) (or_intror Hi))).
by rewrite !l_subst H1 H2; exact: Hsol p Hp.
Qed.

End SubstStarFree.
