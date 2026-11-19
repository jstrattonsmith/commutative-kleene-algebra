(* A pre-Kleene algebra of languages with "omega tokens", used to refute
   pre-KA inequalities that hold in the language model but whose proof
   would need star induction.

   Fix a monoid M and a sequence r : nat -> M (in DirectUndec/NonHalting.v,
   the steps of an infinite machine run). A token (t, k) stands for the
   infinite product t ⋅ r k ⋅ r (k+1) ⋅ ...; two tokens are identified
   (tsim) when they agree after finitely many further steps. An element of
   the model is a language (its finite part, as in KA/lang.v) together with
   a tsim-closed set of tokens. Products absorb tokens on the right, and
   star A additionally contains the token (1, k) whenever every r j with
   j >= k lies in A: the star unfolding axiom is the only star axiom of
   pre-KA, and it is satisfied because (1, k) = r k ⋅ (1, k+1). Star
   induction fails in this model, which is the point.

   The finite part of the interpretation of a term is its language
   (den_fin); tokens are preserved by pre-KA inequalities (den_tok_le). *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.

Section OmegaModel.

Variable M : monoid.
Variable r : nat → M.

Implicit Types (t u a x : M) (k j : nat).

(** ** Segments of the run and equality of tokens *)

Fixpoint rseg k n : M :=
  match n with
  | 0 => 1
  | S n => r k ⋅ rseg (S k) n
  end.

Lemma rseg_add k n m : rseg k (n + m) ≡ rseg k n ⋅ rseg (k + n) m.
Proof.
elim: n k => [|n IH] k /=.
- by rewrite left_id Nat.add_0_r.
- rewrite IH assoc.
  by have -> : S k + n = k + S n by lia.
Qed.

Definition tsim t k t' k' : Prop :=
  ∃ n n', k + n = k' + n' ∧ t ⋅ rseg k n ≡ t' ⋅ rseg k' n'.

Lemma tsim_extend t k t' k' n n' m :
  k + n = k' + n' → t ⋅ rseg k n ≡ t' ⋅ rseg k' n' →
  t ⋅ rseg k (n + m) ≡ t' ⋅ rseg k' (n' + m).
Proof.
move=> e1 e2; rewrite !rseg_add !assoc e2 e1; reflexivity.
Qed.

Lemma tsim_refl t k : tsim t k t k.
Proof. by exists 0, 0. Qed.

Lemma tsim_equiv t u k : t ≡ u → tsim t k u k.
Proof. by move=> e; exists 0, 0; rewrite e. Qed.

Lemma tsim_sym t k t' k' : tsim t k t' k' → tsim t' k' t k.
Proof. by case=> n [n' [e1 e2]]; exists n', n; rewrite e2. Qed.

Lemma tsim_trans t1 k1 t2 k2 t3 k3 :
  tsim t1 k1 t2 k2 → tsim t2 k2 t3 k3 → tsim t1 k1 t3 k3.
Proof.
case=> n1 [n2 [e1 h1]] [m2 [m3 [e2 h2]]].
set J := max (k1 + n1) (k2 + m2).
exists (n1 + (J - (k1 + n1))), (m3 + (J - (k2 + m2))); split; first lia.
rewrite (tsim_extend (J - (k1 + n1)) e1 h1).
rewrite -(tsim_extend (J - (k2 + m2)) e2 h2).
have -> : n2 + (J - (k1 + n1)) = m2 + (J - (k2 + m2)) by lia.
reflexivity.
Qed.

Lemma tsim_mul_l a t k t' k' : tsim t k t' k' → tsim (a ⋅ t) k (a ⋅ t') k'.
Proof. by case=> n [n' [e1 e2]]; exists n, n'; rewrite -!assoc e2. Qed.

Lemma tsim_step t k : tsim t k (t ⋅ r k) (S k).
Proof.
exists 1%nat, 0; split; first lia.
by rewrite /= !right_id.
Qed.

(** ** The model *)

Record omega := Omega {
  om_fin : lang M;
  om_tok : M → nat → Prop;
  om_tok_closed : ∀ t k t' k', tsim t k t' k' → om_tok t k → om_tok t' k';
}.

Implicit Types A B C : omega.

Global Instance omega_equiv : Equiv omega := λ A B,
  om_fin A ≡ om_fin B ∧ ∀ t k, om_tok A t k ↔ om_tok B t k.

Global Instance omega_equivalence : Equivalence (≡@{omega}).
Proof.
split.
- by move=> A; split.
- by move=> A B [e1 e2]; split => // t k; rewrite e2.
- move=> A B C [e1 e2] [e3 e4]; split; first by rewrite e1 e3.
  by move=> t k; rewrite e2 e4.
Qed.

Canonical Structure omega_setoid := @Setoid omega _ _.

Definition nonempty A := (∃ x, om_fin A x) ∨ (∃ t k, om_tok A t k).

Global Program Instance omega_one : One omega :=
  {| om_fin := 1; om_tok := λ _ _, False |}.
Next Obligation. by move=> ????? []. Qed.

Global Program Instance omega_bottom : Bottom omega :=
  {| om_fin := ⊥; om_tok := λ _ _, False |}.
Next Obligation. by move=> ????? []. Qed.

Global Program Instance omega_join : Join omega := λ A B,
  {| om_fin := om_fin A ⊔ om_fin B;
     om_tok := λ t k, om_tok A t k ∨ om_tok B t k |}.
Next Obligation.
by move=> A B t k t' k' h [?|?]; [left|right]; apply: om_tok_closed h _.
Qed.

Global Program Instance omega_mul : Mul omega := λ A B,
  {| om_fin := om_fin A ⋅ om_fin B;
     om_tok := λ t k,
       (om_tok A t k ∧ nonempty B) ∨
       ∃ a t' k', om_fin A a ∧ om_tok B t' k' ∧ tsim t k (a ⋅ t') k' |}.
Next Obligation.
move=> A B t k t' k' h [[At ne]|[a [u [m [Aa [Bu h']]]]]].
- by left; split => //; apply: om_tok_closed h At.
- right; exists a, u, m; do !split => //.
  by apply: tsim_trans h'; apply: tsim_sym.
Qed.

Definition runs_in (L : lang M) k := ∀ j, k ≤ j → L (r j).

Global Program Instance omega_star : Star omega := λ A,
  {| om_fin := star (om_fin A);
     om_tok := λ t k, ∃ f, star (om_fin A) f ∧
       ((∃ t' k', om_tok A t' k' ∧ tsim t k (f ⋅ t') k') ∨
        (∃ k', runs_in (om_fin A) k' ∧ tsim t k f k')) |}.
Next Obligation.
move=> A t k t' k' h [f [Af [[u [m [Au h']]]|[m [Am h']]]]];
  exists f; split => //; [left; exists u, m|right; exists m];
  (split => //; apply: tsim_trans h'; exact: tsim_sym).
Qed.

(** *** Unfolding the operations *)

Lemma om_tok_mul A B t k :
  om_tok (A ⋅ B) t k ↔
  (om_tok A t k ∧ nonempty B) ∨
  ∃ a t' k', om_fin A a ∧ om_tok B t' k' ∧ tsim t k (a ⋅ t') k'.
Proof. done. Qed.

Lemma om_tok_join A B t k :
  om_tok (A ⊔ B) t k ↔ om_tok A t k ∨ om_tok B t k.
Proof. done. Qed.

Lemma om_tok_star A t k :
  om_tok (star A) t k ↔
  ∃ f, star (om_fin A) f ∧
       ((∃ t' k', om_tok A t' k' ∧ tsim t k (f ⋅ t') k') ∨
        (∃ k', runs_in (om_fin A) k' ∧ tsim t k f k')).
Proof. done. Qed.

Lemma nonempty_mul A B : nonempty (A ⋅ B) ↔ nonempty A ∧ nonempty B.
Proof.
split.
- case=> [[x [x1 [x2 [_ [Ax1 Bx2]]]]]|[t [k [[At ne]|]]]].
  + by split; left; [exists x1|exists x2].
  + by split => //; right; exists t, k.
  + case=> a [t' [k' [Aa [Bt' _]]]].
    by split; [left; exists a|right; exists t', k'].
- case=> [[[a Aa]|[t [k At]]] neB].
  + case: neB => [[b Bb]|[t [k Bt]]].
    * by left; exists (a ⋅ b), a, b.
    * right; exists (a ⋅ t), k; right; exists a, t, k.
      by do !split => //; apply: tsim_refl.
  + by right; exists t, k; left.
Qed.

Lemma nonempty_join A B : nonempty (A ⊔ B) ↔ nonempty A ∨ nonempty B.
Proof. rewrite /nonempty /=; firstorder. Qed.

(** ** Algebraic laws *)

Lemma omega_monoid_mixin : MonoidMixin omega.
Proof.
constructor.
- move=> A B C; split.
    exact: (assoc (⋅) (om_fin A) (om_fin B) (om_fin C)).
  move=> t k; rewrite !om_tok_mul nonempty_mul; split.
  + case=> [[At ne]|[a [t' [k' [Aa [BCt' h]]]]]].
    * by case: ne => ??; left; split => //; left.
    * case/om_tok_mul: BCt' => [[Bt' neC]|[b [u [m [Bb [Cu h']]]]]].
      -- by left; split => //; right; exists a, t', k'.
      -- right; exists (a ⋅ b), u, m; split; first by exists a, b.
        split => //; apply: tsim_trans h _.
        apply: tsim_trans (tsim_mul_l a h') _.
        by apply: tsim_equiv; rewrite assoc.
  + case=> [[[[At neB]|[a [t' [k' [Aa [Bt' h]]]]]] neC]|].
    * by left.
    * by right; exists a, t', k'; do !split => //; left.
    * case=> c [u [m [[a [b [ec [Aa Bb]]]] [Cu h]]]].
      right; exists a, (b ⋅ u), m; do !split => //.
      -- by right; exists b, u, m; do !split => //; apply: tsim_refl.
      -- apply: tsim_trans h _; apply: tsim_equiv.
        by rewrite ec assoc.
- move=> A; split.
    exact: (left_id 1 (⋅) (om_fin A)).
  move=> t k; rewrite om_tok_mul; split.
  + case=> [[[]]|[a [t' [k' [ea [At' h]]]]]].
    apply: om_tok_closed At'; apply: tsim_sym; apply: tsim_trans h _.
    by apply: tsim_equiv; rewrite ea left_id.
  + move=> At; right; exists 1, t, k; split; first by simpl; reflexivity.
    split => //; apply: tsim_equiv; by rewrite left_id.
- move=> A; split.
    exact: (right_id 1 (⋅) (om_fin A)).
  move=> t k; rewrite om_tok_mul; split.
  + by case=> [[]|[? [? [? [_ [[] _]]]]]].
  + move=> At; left; split => //; left; exists 1; simpl; reflexivity.
- move=> A1 A2 [eA1 eA2] B1 B2 [eB1 eB2]; split.
  + by rewrite /= eA1 eB1.
  + have eB : nonempty B1 ↔ nonempty B2.
    { rewrite /nonempty; split; case.
      -- by case=> x ?; left; exists x; rewrite -(eB1 x).
      -- by case=> t [k ?]; right; exists t, k; rewrite -eB2.
      -- by case=> x ?; left; exists x; rewrite (eB1 x).
      -- by case=> t [k ?]; right; exists t, k; rewrite eB2. }
    move=> t k; rewrite !om_tok_mul eA2 eB; split.
    * case=> [?|[a [t' [k' [Aa [Bt' h]]]]]]; first by left.
      by right; exists a, t', k'; rewrite -(eA1 a) -eB2.
    * case=> [?|[a [t' [k' [Aa [Bt' h]]]]]]; first by left.
      by right; exists a, t', k'; rewrite (eA1 a) eB2.
Qed.

Canonical Structure omega_monoid :=
  @Monoid' omega _ _ _ _ omega_monoid_mixin.

Global Instance omega_sqsubseteq : SqSubsetEq omega := default_sqsubseteq.

Lemma omega_semi_lattice_mixin : SemiLatticeMixin omega.
Proof.
apply: default_semi_lattice_mixin.
- move=> A B C; split.
    exact: (assoc (⊔) (om_fin A) (om_fin B) (om_fin C)).
  by move=> t k; rewrite !om_tok_join; tauto.
- move=> A B; split.
    exact: (comm (⊔) (om_fin A) (om_fin B)).
  by move=> t k; rewrite !om_tok_join; tauto.
- move=> A; split.
    exact: (left_id ⊥ (⊔) (om_fin A)).
  by move=> t k; rewrite !om_tok_join /=; tauto.
- move=> A; split.
    exact: (idemp (⊔) (om_fin A)).
  by move=> t k; rewrite !om_tok_join; tauto.
- move=> A1 A2 [eA1 eA2] B1 B2 [eB1 eB2]; split.
  + by rewrite /= eA1 eB1.
  + by move=> t k; rewrite !om_tok_join eA2 eB2.
Qed.

Canonical Structure omega_semi_lattice :=
  @SemiLattice' omega _ _ _ _ _ omega_semi_lattice_mixin.

Lemma star_fin_one (L : lang M) : star L 1.
Proof. by exists 0; simpl; reflexivity. Qed.

Lemma star_fin_cons (L : lang M) a f : L a → star L f → star L (a ⋅ f).
Proof. by move=> La [n Ln]; exists (S n), a, f; split; first reflexivity. Qed.

Lemma omega_star_unfold A : star A ≡ 1 ⊔ A ⋅ star A.
Proof.
split.
  exact: (pre_ka_star_unfold (om_fin A)).
move=> t k; rewrite om_tok_join om_tok_mul om_tok_star /=; split.
- case=> f [[n Af]] Hf.
  case: n Af => [|n] /= Af.
  + case: Hf => [[t' [k' [At' h]]]|[k' [run h]]].
    * right; left; split.
      -- apply: om_tok_closed At'; apply: tsim_sym; apply: tsim_trans h _.
        by apply: tsim_equiv; rewrite Af left_id.
      -- by left; exists 1; apply: star_fin_one.
    * right; right; exists (r k'), 1, (S k'); do !split.
      -- exact: run.
      -- exists 1; split; first exact: star_fin_one.
        right; exists (S k'); split; first by move=> j ?; apply: run; lia.
        exact: tsim_refl.
      -- apply: tsim_trans h _; apply: tsim_trans (tsim_equiv k' Af) _.
        apply: tsim_trans (tsim_step 1 k') _.
        by apply: tsim_equiv; rewrite left_id right_id.
  + case: Af => a [f' [ef [Aa Af']]].
    right; right.
    case: Hf => [[t' [k' [At' h]]]|[k' [run h]]].
    * exists a, (f' ⋅ t'), k'; do !split => //.
      -- exists f'; split; first by exists n.
        by left; exists t', k'; split => //; apply: tsim_refl.
      -- by apply: tsim_trans h _; apply: tsim_equiv; rewrite ef assoc.
    * exists a, f', k'; do !split => //.
      -- exists f'; split; first by exists n.
        by right; exists k'; split => //; apply: tsim_refl.
      -- by apply: tsim_trans h _; apply: tsim_equiv; rewrite ef.
- case=> [[]|[[At _]|[a [t' [k' [Aa [Ht' h]]]]]]].
  + exists 1; split; first exact: star_fin_one.
    by left; exists t, k; split => //; apply: tsim_equiv; rewrite left_id.
  + case: Ht' => f [Af [[u [m [Au h']]]|[m [run h']]]];
      exists (a ⋅ f); (split; first exact: star_fin_cons);
      [left; exists u, m|right; exists m]; split => //;
      apply: tsim_trans h _; apply: tsim_trans (tsim_mul_l a h') _;
      apply: tsim_equiv; by rewrite ?assoc.
Qed.

Lemma omega_pre_ka_mixin : PreKAMixin omega.
Proof.
constructor.
- move=> A B C; split.
    exact: (pre_ka_right_dist (om_fin A) (om_fin B) (om_fin C)).
  move=> t k /=; rewrite nonempty_join.
  split.
  + case=> [[At [?|?]]|[a [t' [k' [Aa [[?|?] h]]]]]].
    * by left; left.
    * by right; left.
    * by left; right; exists a, t', k'.
    * by right; right; exists a, t', k'.
  + case=> [[[At ?]|[a [t' [k' [Aa [? h]]]]]]|[[At ?]|[a [t' [k' [Aa [? h]]]]]]].
    * by left; split; [|left].
    * by right; exists a, t', k'; do !split => //; left.
    * by left; split; [|right].
    * by right; exists a, t', k'; do !split => //; right.
- move=> A B C; split.
    exact: (pre_ka_left_dist (om_fin A) (om_fin B) (om_fin C)).
  move=> t k /=.
  split.
  + case=> [[[?|?] ne]|[a [t' [k' [[?|?] [Ct' h]]]]]].
    * by left; left.
    * by right; left.
    * by left; right; exists a, t', k'.
    * by right; right; exists a, t', k'.
  + case=> [[[??]|[a [t' [k' [? [? h]]]]]]|[[??]|[a [t' [k' [? [? h]]]]]]].
    * by left; split => //; left.
    * by right; exists a, t', k'; do !split => //; left.
    * by left; split => //; right.
    * by right; exists a, t', k'; do !split => //; right.
- move=> A; split.
    exact: (left_absorb ⊥ (⋅) (om_fin A)).
  move=> t k; rewrite om_tok_mul /=; split => //.
  by case=> [[[]]|[? [? [? [[] _]]]]].
- move=> A; split.
    exact: (right_absorb ⊥ (⋅) (om_fin A)).
  move=> t k; rewrite om_tok_mul /=; split => //.
  case=> [[_ [[? []]|[? [? []]]]]|[? [? [? [_ [[] _]]]]]].
- exact: omega_star_unfold.
- move=> A B [eA eB]; split; first by rewrite /= eA.
  have er : ∀ k, runs_in (om_fin A) k ↔ runs_in (om_fin B) k.
  { by move=> k; split=> run j kj; [rewrite -(eA (r j))|rewrite (eA (r j))];
      apply: run. }
  move=> t k; rewrite !om_tok_star; split.
  + case=> f [Af Hf]; exists f; split; first by rewrite -eA.
    case: Hf => [[t' [k' [? h]]]|[k' [? h]]].
    * by left; exists t', k'; rewrite -eB.
    * by right; exists k'; rewrite -er.
  + case=> f [Af Hf]; exists f; split; first by rewrite eA.
    case: Hf => [[t' [k' [? h]]]|[k' [? h]]].
    * by left; exists t', k'; rewrite eB.
    * by right; exists k'; rewrite er.
Qed.

Canonical Structure omega_pre_ka :=
  @PreKA' omega _ _ _ _ _ _ _ _
    omega_monoid_mixin omega_semi_lattice_mixin omega_pre_ka_mixin.

(** ** Interpreting terms *)

Program Definition omega_sing x : omega :=
  {| om_fin := lang_sing x; om_tok := λ _ _, False |}.
Next Obligation. by move=> ?????? []. Qed.

Global Instance omega_sing_morphism :
  MonoidMorphism (omega_sing : M → omega_monoid).
Proof.
constructor.
- move=> x y e; split => //=.
  by rewrite e.
- by split.
- move=> x y; split; first exact: monoid_morphism_mul.
  move=> t k; rewrite om_tok_mul /=; split => //.
  by case=> [[[]]|[? [? [? [_ [[] _]]]]]].
Qed.

Definition den : ka_term M → omega_pre_ka := ka_term_elim omega_sing.

Global Instance den_morphism : PreKAMorphism den.
Proof. rewrite /den; apply _. Qed.

Lemma den_mul e f : den (e ⋅ f) = den e ⋅ den f.
Proof. by []. Qed.

Lemma den_join e f : den (e ⊔ f) = den e ⊔ den f.
Proof. by []. Qed.

Lemma den_star e : den (star e) = star (den e).
Proof. by []. Qed.

Lemma den_fin e : om_fin (den e) ≡ l e.
Proof.
elim: e => /=.
- by [].
- by [].
- by move=> e1 IH1 e2 IH2; rewrite /= IH1 IH2.
- by move=> e1 IH1 e2 IH2; rewrite /= IH1 IH2.
- by move=> e IH; rewrite /= IH.
Qed.

Lemma den_fin_unit e x : om_fin (den e) x ↔ Unit x ⊑ e.
Proof. by rewrite (den_fin e x) l_alt. Qed.

(** Tokens are preserved by pre-KA inequalities. *)

Lemma den_tok_le e f t k : e ⊑ f → om_tok (den e) t k → om_tok (den f) t k.
Proof.
move=> /sqsubseteq_iff /(pre_ka_morphism_proper (f := den)) [_ ef] et.
by rewrite -ef /=; left.
Qed.

(** ** Producing tokens *)

Lemma den_tok_star e k :
  (∀ j, k ≤ j → Unit (r j) ⊑ e) → om_tok (den (star e)) 1 k.
Proof.
move=> run; exists 1; split; first exact: star_fin_one.
right; exists k; split; last exact: tsim_refl.
by move=> j kj; apply/den_fin_unit; apply: run.
Qed.

Lemma den_tok_unit_mul x e t k :
  om_tok (den e) t k → om_tok (den (Unit x ⋅ e)) (x ⋅ t) k.
Proof.
move=> et; right; exists x, t, k; split; first by simpl; reflexivity.
split => //; exact: tsim_refl.
Qed.

(** ** Token-free terms *)

Definition tokfree A := ∀ t k, ¬ om_tok A t k.

Lemma tokfree_unit x : tokfree (den (Unit x)).
Proof. by move=> ?? []. Qed.

Lemma tokfree_bottom : tokfree (den ⊥).
Proof. by move=> ?? []. Qed.

Lemma tokfree_join A B : tokfree A → tokfree B → tokfree (A ⊔ B).
Proof. by move=> hA hB t k [/hA|/hB]. Qed.

Lemma tokfree_mul A B : tokfree A → tokfree B → tokfree (A ⋅ B).
Proof.
move=> hA hB t k [[/hA //]|[? [? [? [_ [/hB //]]]]]].
Qed.

Lemma tokfree_star A :
  tokfree A → (∀ j, ¬ om_fin A (r j)) → tokfree (star A).
Proof.
move=> hA hr t k [f [_ [[t' [k' [/hA //]]]|[k' [run _]]]]].
by apply: (hr k'); apply: run.
Qed.

Lemma tokfree_proper e e' : e ≡ e' → tokfree (den e) → tokfree (den e').
Proof.
move=> /(pre_ka_morphism_proper (f := den)) [_ ee'] h t k.
by rewrite -ee'; apply: h.
Qed.

Lemma tokfree_join_list {X : Type} (f : X → ka_term M) (xs : list X) :
  (∀ y, tokfree (den (f y))) → tokfree (den (join_list f xs)).
Proof.
move=> hf; elim: xs => [|y xs IH] /=; first exact: tokfree_bottom.
exact: tokfree_join.
Qed.

Section TokfreeMap.

Variables (S : monoid) (g : S → M).
Context `{!MonoidMorphism g}.

Lemma tokfree_map_star (e : ka_term S) :
  tokfree (star (den (ka_term_map g e))) →
  tokfree (den (ka_term_map g (star e))).
Proof. by []. Qed.

Lemma tokfree_map (e : ka_term S) :
  (∀ s j, ¬ g s ≡ r j) → tokfree (den (ka_term_map g e)).
Proof.
move=> hg; elim: e => /=.
- move=> ?; exact: tokfree_unit.
- exact: tokfree_bottom.
- by move=> e1 IH1 e2 IH2; apply: tokfree_join.
- by move=> e1 IH1 e2 IH2; apply: tokfree_mul.
- move=> e IH; apply: tokfree_star => // j.
  rewrite (den_fin _ (r j)) (l_natural (f:=g) e (r j)).
  by case=> s [e_s _]; apply: (hg s j); rewrite e_s.
Qed.

End TokfreeMap.

(** ** Bad tokens

    Given a property [Bad] of monoid elements that is stable under right
    multiplication (in DirectUndec/NonHalting.v: "the two components
    disagree at some position"), a token is bad when some finite
    approximation of it is bad. Badness is invariant under tsim, and is
    inherited by products whose left factor only has bad elements. *)

Section Bad.

Variable Bad : M → Prop.
Context `{!Proper ((≡) ==> iff) Bad}.
Hypothesis Bad_mul : ∀ x y, Bad x → Bad (x ⋅ y).

Definition tbad t k := ∃ n, Bad (t ⋅ rseg k n).

Lemma tbad_tsim t k t' k' : tsim t k t' k' → tbad t k → tbad t' k'.
Proof.
case=> n0 [n0' [e1 e2]] [n1 b].
exists (n0' + n1); rewrite -(tsim_extend n1 e1 e2).
have -> : n0 + n1 = n1 + n0 by lia.
by rewrite rseg_add assoc; apply: Bad_mul.
Qed.

Lemma tbad_mul_tok A B t k :
  (∀ t k, om_tok A t k → tbad t k) →
  (∀ a, om_fin A a → Bad a) →
  om_tok (A ⋅ B) t k → tbad t k.
Proof.
move=> hA hA' [[/hA //]|[a [t' [k' [Aa [_ h]]]]]].
apply: tbad_tsim (tsim_sym h) _; exists 0.
by apply: Bad_mul; apply: Bad_mul; apply: hA'.
Qed.

Lemma bad_mul_fin A B x :
  (∀ a, om_fin A a → Bad a) → om_fin (A ⋅ B) x → Bad x.
Proof.
move=> hA [x1 [x2 [-> [Ax1 _]]]].
by apply: Bad_mul; apply: hA.
Qed.

End Bad.

End OmegaModel.
