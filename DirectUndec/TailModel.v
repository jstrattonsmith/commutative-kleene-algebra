(* A second non-standard pre-KA model, for upper bounds in which the star
   being refuted also occurs as a prefix: tokens with finite tails.

   DirectUndec/OmegaModel.v's tokens absorb everything multiplied on their
   right, so a token of star x also lies in star x ⋅ y for every non-empty
   y. Here a
   token is a triple (t, k, u), standing for t ⋅ r k ⋅ r (k+1) ⋅ ... ⋅ u
   (an infinite word followed by a finite one); a product of two tokens is
   a junk element. The monoid tk of finite elements, tokens and junk is
   ordinary, and the model is just languages over tk (KA/lang.v), except
   for the star:

     star' A := star A ⋅ (1 ⊔ Z A ⋅ star A)
     where Z A = {(1, k, 1) | r j ∈ A for j ≥ k}.

   It satisfies the unfolding axiom because (1, k, 1) = r k ⋅ (1, k+1, 1).
   den_fin: the finite part of a term's interpretation is its language;
   pre_mul/pre_star: how a token with empty tail that continues a given
   finite prefix into the run can arise in a product or a star. *)

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
From kacc Require Import DirectUndec.OmegaModel.

Section TailModel.

Variable M : monoid.
Variable r : nat → M.

(** In a free monoid, only 1 ⋅ 1 is 1. *)
Hypothesis unit_split : ∀ x y : M, x ⋅ y ≡ 1 → x ≡ 1 ∧ y ≡ 1.

Implicit Types (x y t u a : M) (k j : nat).

Notation tsim := (tsim r).

(** ** Finite elements, tokens and junk *)

Inductive tk := TFin (x : M) | TTok (t : M) (k : nat) (u : M) | TJunk.

Definition tk_eq (p q : tk) : Prop :=
  match p, q with
  | TFin x, TFin y => x ≡ y
  | TTok t k u, TTok t' k' u' => tsim t k t' k' ∧ u ≡ u'
  | TJunk, TJunk => True
  | _, _ => False
  end.

Global Instance tk_equiv : Equiv tk := tk_eq.

Global Instance tk_equivalence : Equivalence (≡@{tk}).
Proof.
rewrite /equiv /tk_equiv; split.
- move=> [x|t k u|] /=; [reflexivity| |done].
  by split; [apply: tsim_refl|reflexivity].
- move=> [x|t k u|] [y|t' k' u'|] //= H;
    first [by symmetry
          |by case: H => h e; split; [apply: tsim_sym|symmetry]].
- move=> [x|t k u|] [y|t' k' u'|] [z|t'' k'' u''|] //= H1 H2;
    first [by transitivity y
          |by case: H1 => h1 e1; case: H2 => h2 e2;
              split; [apply: tsim_trans h1 h2|transitivity u']].
Qed.

Canonical Structure tk_setoid := @Setoid tk _ _.

Global Instance tk_one : One tk := TFin 1.

Global Instance tk_mul : Mul tk := λ p q,
  match p, q with
  | TFin x, TFin y => TFin (x ⋅ y)
  | TFin x, TTok t k u => TTok (x ⋅ t) k u
  | TTok t k u, TFin y => TTok t k (u ⋅ y)
  | _, _ => TJunk
  end.

Lemma tk_monoid_mixin : MonoidMixin tk.
Proof.
constructor.
- case=> [x|t k u|] [y|t' k' u'|] [z|t'' k'' u''|] //=;
    rewrite /equiv /tk_equiv /=;
    first [ by rewrite assoc
          | by split; [apply: tsim_equiv; rewrite ?assoc|rewrite ?assoc] ].
- case=> [x|t k u|] //=; rewrite /equiv /tk_equiv /=;
    first [ by rewrite left_id
          | by split; [apply: tsim_equiv; rewrite left_id|] ].
- case=> [x|t k u|] //=; rewrite /equiv /tk_equiv /=;
    first [ by rewrite right_id
          | by split; [apply: tsim_refl|rewrite right_id] ].
- case=> [x|t k u|] [x'|t' k' u'|] //= e1 [y|s m v|] [y'|s' m' v'|] //= e2;
    rewrite /equiv /tk_equiv /= in e1 e2 *.
  + by rewrite e1 e2.
  + case: e2 => h ->; split => //.
    apply: tsim_trans (tsim_mul_l x h) _.
    by apply: tsim_equiv; rewrite e1.
  + by case: e1 => h ->; rewrite e2.
Qed.

Canonical Structure tk_monoid := @Monoid' tk _ _ _ _ tk_monoid_mixin.

Global Instance TFin_morphism : MonoidMorphism (TFin : M → tk_monoid).
Proof. by split => //; move=> x y e. Qed.

Lemma tk_mul_TFin_inv p q x : p ⋅ q ≡ TFin x →
  ∃ a b, p = TFin a ∧ q = TFin b ∧ x ≡ a ⋅ b.
Proof.
case: p => [a|???|]; case: q => [b|???|] //= e.
by exists a, b.
Qed.

(** ** The model *)

Record tlang := TL { tl : lang tk_monoid }.

Implicit Types A B C : tlang.

Global Instance tlang_equiv : Equiv tlang := λ A B, tl A ≡ tl B.

Global Instance tlang_equivalence : Equivalence (≡@{tlang}).
Proof.
split.
- by move=> A; rewrite /equiv /tlang_equiv.
- by move=> A B; rewrite /equiv /tlang_equiv.
- by move=> A B C; rewrite /equiv /tlang_equiv => ->.
Qed.

Canonical Structure tlang_setoid := @Setoid tlang _ _.

Definition runs_in (L : lang tk_monoid) k := ∀ j, k ≤ j → L (TFin (r j)).

Program Definition Zr (L : lang tk_monoid) : lang tk_monoid :=
  {| lang_car := λ p, ∃ k, p ≡ TTok 1 k 1 ∧ runs_in L k |}.
Next Obligation.
by move=> L p q e; split; case=> k [ep h]; exists k; split => //;
  [rewrite -e|rewrite e].
Qed.

Global Instance Zr_proper : Proper ((≡) ==> (≡)) Zr.
Proof.
move=> L L' e p /=; split; case=> k [ep h]; exists k; split => // j kj.
- by rewrite -(e (TFin (r j))); apply: h.
- by rewrite (e (TFin (r j))); apply: h.
Qed.

Definition star' (L : lang tk_monoid) : lang tk_monoid :=
  star L ⋅ (1 ⊔ Zr L ⋅ star L).

Global Instance tlang_one : One tlang := TL 1.
Global Instance tlang_bottom : Bottom tlang := TL ⊥.
Global Instance tlang_join : Join tlang := λ A B, TL (tl A ⊔ tl B).
Global Instance tlang_mul : Mul tlang := λ A B, TL (tl A ⋅ tl B).
Global Instance tlang_star : Star tlang := λ A, TL (star' (tl A)).
Global Instance tlang_sqsubseteq : SqSubsetEq tlang := default_sqsubseteq.

Lemma tlang_monoid_mixin : MonoidMixin tlang.
Proof.
constructor.
- move=> A B C; exact: (assoc (⋅) (tl A) (tl B) (tl C)).
- move=> A; exact: (left_id 1 (⋅) (tl A)).
- move=> A; exact: (right_id 1 (⋅) (tl A)).
- move=> A A' eA B B' eB.
  have {}eA : tl A ≡ tl A' := eA; have {}eB : tl B ≡ tl B' := eB.
  by rewrite /equiv /tlang_equiv /= eA eB.
Qed.

Canonical Structure tlang_monoid :=
  @Monoid' tlang _ _ _ _ tlang_monoid_mixin.

Lemma tlang_semi_lattice_mixin : SemiLatticeMixin tlang.
Proof.
apply: default_semi_lattice_mixin.
- move=> A B C; exact: (assoc (⊔) (tl A) (tl B) (tl C)).
- move=> A B; exact: (comm (⊔) (tl A) (tl B)).
- move=> A; exact: (left_id ⊥ (⊔) (tl A)).
- move=> A; exact: (idemp (⊔) (tl A)).
- move=> A A' eA B B' eB.
  have {}eA : tl A ≡ tl A' := eA; have {}eB : tl B ≡ tl B' := eB.
  by rewrite /equiv /tlang_equiv /= eA eB.
Qed.

Canonical Structure tlang_semi_lattice :=
  @SemiLattice' tlang _ _ _ _ _ tlang_semi_lattice_mixin.

Lemma star'_unfold (L : lang tk_monoid) : star' L ≡ 1 ⊔ L ⋅ star' L.
Proof.
move=> p; split.
- case=> p1 [p2 [ep [[n Ln] Hp2]]].
  case: n Ln => [|n] /= Ln.
  + case: Hp2 => [e2|[z [y [e2 [[k [ez run]] Ly]]]]].
    * have {}e2 : p2 ≡@{tk} 1 := e2.
      have {}Ln : p1 ≡@{tk} 1 := Ln.
      by left; rewrite /= ep Ln e2 left_id.
    * right; exists (TFin (r k)), (TTok 1 (S k) 1 ⋅ y); split.
      -- have {}Ln : p1 ≡@{tk} 1 := Ln.
         have {}ez : z ≡@{tk} TTok 1 k 1 := ez.
         rewrite ep Ln left_id e2 ez assoc.
         apply: (monoid_proper (T := tk_monoid)); last reflexivity.
         rewrite /equiv /tk_equiv /=; split; last reflexivity.
         apply: tsim_trans (tsim_step r 1 k) _.
         by apply: tsim_equiv; rewrite left_id right_id.
      -- split; first by apply: run.
         exists 1, (TTok 1 (S k) 1 ⋅ y); split; first by rewrite left_id.
         split; first by exists 0; simpl; reflexivity.
         right; exists (TTok 1 (S k) 1), y; split => //; split => //.
         exists (S k); split => // j kj; apply: run; lia.
  + case: Ln => a [b [e1 [La Lb]]].
    right; exists a, (b ⋅ p2); split; first by rewrite ep e1 assoc.
    split => //; exists b, p2; split => //; split => //; by exists n.
- case=> [e1|[a [s [ep [La [s1 [s2 [es [[n Ls1] Hs2]]]]]]]]].
  + have {}e1 : p ≡@{tk} 1 := e1.
    exists 1, 1; split; first by rewrite e1 left_id.
    split; first by exists 0; simpl; reflexivity.
    by left; simpl; reflexivity.
  + exists (a ⋅ s1), s2; split; first by rewrite ep es assoc.
    split => //; exists (S n), a, s1; split => //.
Qed.

Lemma star'_proper : Proper ((≡) ==> (≡)) star'.
Proof. by move=> L L' e; rewrite /star' e. Qed.

Lemma tlang_pre_ka_mixin : PreKAMixin tlang.
Proof.
constructor.
- move=> A B C; exact: (pre_ka_right_dist (tl A) (tl B) (tl C)).
- move=> A B C; exact: (pre_ka_left_dist (tl A) (tl B) (tl C)).
- move=> A; exact: (left_absorb ⊥ (⋅) (tl A)).
- move=> A; exact: (right_absorb ⊥ (⋅) (tl A)).
- move=> A; exact: (star'_unfold (tl A)).
- move=> A A' e; exact: star'_proper e.
Qed.

Canonical Structure tlang_pre_ka :=
  @PreKA' tlang _ _ _ _ _ _ _ _
    tlang_monoid_mixin tlang_semi_lattice_mixin tlang_pre_ka_mixin.

(** ** Interpreting terms *)

Definition tsing x : tlang := TL (lang_sing (TFin x)).

Global Instance tsing_morphism : MonoidMorphism (tsing : M → tlang_monoid).
Proof.
constructor.
- by move=> x y e p; rewrite /= e.
- by move=> p.
- move=> x y p; rewrite /=; split.
  + move=> e; exists (TFin x), (TFin y); split; first exact: e.
    by split; reflexivity.
  + case=> p1 [p2 [e [e1 e2]]]; apply: transitivity e _.
    exact: (monoid_proper (T := tk_monoid) e1 e2).
Qed.

Definition tden : ka_term M → tlang_pre_ka := ka_term_elim tsing.

Global Instance tden_morphism : PreKAMorphism tden.
Proof. rewrite /tden; apply _. Qed.

Notation D e := (tl (tden e)).

Lemma tden_le e f p : e ⊑ f → D e p → D f p.
Proof.
move=> /sqsubseteq_iff /(pre_ka_morphism_proper (f := tden)) ef ep.
by rewrite -(ef p); left.
Qed.

(** Finite elements of a power, and of a star', are finite products. *)

Lemma power_TFin (L : lang tk_monoid) (L' : lang M) n x :
  (∀ y, L (TFin y) ↔ L' y) → (L ^ n) (TFin x) ↔ (L' ^ n) x.
Proof.
move=> hL; elim: n x => [|n IH] x /=; first by [].
split.
- case=> p1 [p2 [e [La Lb]]].
  have [a [b [ea [eb {}e]]]] :=
    tk_mul_TFin_inv (symmetry (e : TFin x ≡ p1 ⋅ p2)).
  subst p1 p2.
  by exists a, b; split => //; split; [apply/hL|apply/IH].
- case=> a [b [e [La Lb]]]; exists (TFin a), (TFin b); split.
  + by rewrite /= e.
  + by split; [apply/hL|apply/IH].
Qed.

Lemma den_fin e x : D e (TFin x) ↔ l e x.
Proof.
elim: e x => /=.
- by [].
- by [].
- by move=> e1 IH1 e2 IH2 x; rewrite IH1 IH2.
- move=> e1 IH1 e2 IH2 x; split.
  + case=> p1 [p2 [e [h1 h2]]].
    have [a [b [ea [eb {}e]]]] :=
      tk_mul_TFin_inv (symmetry (e : TFin x ≡ p1 ⋅ p2)).
    subst p1 p2.
    by exists a, b; split => //; split; [apply/IH1|apply/IH2].
  + case=> a [b [e [h1 h2]]]; exists (TFin a), (TFin b); split.
    * by rewrite /= e.
    * by split; [apply/IH1|apply/IH2].
- move=> e IH x; split.
  + case=> p1 [p2 [ex' [[n h1] h2]]].
    have [a [b [ea [eb ex]]]] :=
      tk_mul_TFin_inv (symmetry (ex' : TFin x ≡ p1 ⋅ p2)).
    subst p1 p2.
    case: h2 => [e1|[z [y [ez [[k [ez' _]] _]]]]].
    * have {}e1 : b ≡ 1 := e1.
      exists n; rewrite ex e1 right_id.
      by apply/(power_TFin (L' := l e)) => // y; apply: IH.
    * have {}ez : TFin b ≡ z ⋅ y := ez.
      have {}ez' : z ≡ TTok 1 k 1 := ez'.
      move: ez; rewrite ez'.
      by case: y.
  + case=> n hn; exists (TFin x), 1; split.
      by rewrite /= right_id.
    split; last by left; simpl; reflexivity.
    by exists n; apply/(power_TFin (L' := l e)) => // y; apply: IH.
Qed.

(** ** Token-free interpretations *)

Definition tokfree (L : lang tk_monoid) := ∀ t k u, ¬ L (TTok t k u).

Lemma tokfree_mul (L L' : lang tk_monoid) :
  tokfree L → tokfree L' → tokfree (L ⋅ L').
Proof.
move=> h h' t k u [p1 [p2 [e [L1 L2]]]].
have {}e : TTok t k u ≡ p1 ⋅ p2 := e; move: e.
case: p1 L1 => [a|t1 k1 u1|] L1; case: p2 L2 => [b|t2 k2 u2|] L2 //= _.
- exact: (h' _ _ _ L2).
- exact: (h _ _ _ L1).
Qed.

Lemma tokfree_power (L : lang tk_monoid) n : tokfree L → tokfree (L ^ n).
Proof.
move=> h; elim: n => [|n IH] /=; first by move=> ??? [].
exact: tokfree_mul.
Qed.

Lemma tokfree_star' (L : lang tk_monoid) :
  tokfree L → (∀ k, ¬ runs_in L k) → tokfree (star' L).
Proof.
move=> h hr t k u [p1 [p2 [e [[n Lp1] Hp2]]]].
case: Hp2 => [e2|[z [y [_ [[k' [_ run]] _]]]]]; last exact: hr run.
have : tokfree (L ^ n) by exact: tokfree_power.
have {}e2 : p2 ≡@{tk} 1 := e2.
move=> hn; move: e; rewrite e2 right_id => e.
by apply: (hn t k u); rewrite e.
Qed.

Lemma tokfree_tden_unit x : tokfree (D (Unit x)).
Proof. by move=> ??? []. Qed.

Lemma tokfree_tden_bottom : tokfree (D ⊥).
Proof. by move=> ??? []. Qed.

Lemma tokfree_tden_join e f :
  tokfree (D e) → tokfree (D f) → tokfree (D (e ⊔ f)).
Proof. by move=> h h' t k u [/h|/h']. Qed.

Lemma tokfree_tden_mul e f :
  tokfree (D e) → tokfree (D f) → tokfree (D (e ⋅ f)).
Proof. exact: tokfree_mul. Qed.

Lemma tokfree_tden_star e :
  tokfree (D e) → (∀ k, ∃ j, k ≤ j ∧ ¬ l e (r j)) → tokfree (D (star e)).
Proof.
move=> h hr; apply: tokfree_star' => // k run.
case: (hr k) => j [kj nj]; apply: nj; apply/den_fin; exact: run.
Qed.

Lemma tokfree_tden_join_list {X : Type} (f : X → ka_term M) (xs : list X) :
  (∀ i, tokfree (D (f i))) → tokfree (D (join_list f xs)).
Proof.
move=> hf; elim: xs => [|i xs IH] /=; first exact: tokfree_tden_bottom.
exact: tokfree_tden_join.
Qed.

(** ** Tokens continuing a prefix into the run

    [PreT h p]: p is a token with empty tail that, preceded by h, is the
    run from its start. *)

Definition PreT (h : M) (p : tk) : Prop :=
  ∃ t k, p ≡ TTok t k 1 ∧ tsim (h ⋅ t) k 1 0.

Lemma PreT_proper h p q : p ≡ q → PreT h p → PreT h q.
Proof. by move=> e [t [k [ep h']]]; exists t, k; rewrite -e. Qed.

Lemma pre_mul (L L' : lang tk_monoid) h p :
  (L ⋅ L') p → PreT h p →
  (∃ a p', L (TFin a) ∧ L' p' ∧ PreT (h ⋅ a) p') ∨
  (∃ p', L p' ∧ PreT h p' ∧ L' (TFin 1)).
Proof.
case=> p1 [p2 [e [L1 L2]]] [t [k [ep ht]]].
move: e; rewrite ep.
case: p1 L1 => [a|t1 k1 u1|] L1; case: p2 L2 => [b|t2 k2 u2|] L2 //=.
- case=> h1 e2; left; exists a, (TTok t2 k2 u2); split => //; split => //.
  exists t2, k2; split; first by split; [apply: tsim_refl|symmetry].
  eapply tsim_trans; last exact: ht.
  eapply tsim_trans; last exact: (tsim_mul_l h (tsim_sym h1)).
  by apply: tsim_equiv; rewrite assoc.
- case=> h1 e; have [e1 eb] := unit_split (symmetry e); right.
  exists (TTok t1 k1 u1); split => //; split.
  + exists t1, k1; split; first by split; [apply: tsim_refl|].
    eapply tsim_trans; last exact: ht.
    apply: tsim_mul_l; exact: tsim_sym.
  + by rewrite -eb.
Qed.

Lemma pre_star (L : lang tk_monoid) h p :
  tokfree L → star' L p → PreT h p →
  ∃ a k, star L (TFin a) ∧ runs_in L k ∧ tsim (h ⋅ a) k 1 0.
Proof.
move=> hL Sp Pp.
case: (pre_mul Sp Pp) => [[a [p' [La [Hp' Pp']]]]|[p' [Lp' [Pp' _]]]].
- case: Hp' => [e1|Hz].
  + by case: Pp' => t [k [ep _]]; move: e1; rewrite ep.
  + case: (pre_mul Hz Pp')
      => [[z [p'' [[k [ez _]] _]]]|[z [[k [ez run]] [Pz _]]]].
    * by move: ez.
    * exists a, k; split => //; split => //.
      case: Pz => t [k' [ez' ht]]; move: ez'; rewrite ez /=.
      case=> h1 _; apply: tsim_trans _ ht.
      eapply tsim_trans; last exact: (tsim_mul_l (h ⋅ a) h1).
      by apply: tsim_equiv; rewrite right_id.
- case: Lp' => n Ln; case: Pp' => t [k [ep _]].
  move: Ln; rewrite ep => Ln; exfalso.
  exact: (tokfree_power hL Ln).
Qed.

End TailModel.
