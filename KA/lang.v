(* Formal languages over word monoids: the `lang` record and the
   interpretation `l : ka_term T -> lang` sending a KA term to the
   language it denotes. Establishes `l_alt` (string membership agrees
   with term ordering), `l_inj_finite`, and `either_empty_or_nonzero` --
   foundational language-semantics facts (the paper's Theorem 5,
   Corollaries 7-8) that KA/automata.v and KA/repr_rel.v build on. *)

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

From kacc Require Import KA.utils KA.algebra KA.pre_ka.

Section Languages.

Variable T : monoid.

Implicit Types x y z : T.

Record lang := Lang {
  lang_car :> T → Prop;
  lang_car_proper : Proper ((≡) ==> iff) lang_car;
}.

Implicit Types A B C : lang.

Global Instance lang_equiv : Equiv lang := λ A B,
  ∀ x : T, A x ↔ B x.

Global Instance lang_equivalence : Equivalence (≡@{lang}).
Proof.
split.
- by move=> A x.
- by move=> A B e x; rewrite (e x).
- by move=> A B C e1 e2 x; rewrite (e1 x) (e2 x).
Qed.

Canonical Structure lang_setoid :=
  @Setoid lang _ _.

Global Existing Instance lang_car_proper.

Global Instance lang_proper : Proper ((≡) ==> (≡) ==> iff) lang_car.
Proof.
move=> A B e1 x y e2.
by rewrite (lang_car_proper _ e2) (e1 y).
Qed.

Global Program Instance lang_one : One lang :=
  {| lang_car := λ x, x ≡ 1 |}.
Next Obligation. by move=> x y ->. Qed.

Global Program Instance lang_mul : Mul lang := λ A B,
  {| lang_car := λ x, ∃ x1 x2, x ≡ x1 ⋅ x2 ∧ A x1 ∧ B x2 |}.
Next Obligation.
move=> A B x y e; split.
- by case=> x1 [] x2 e'; exists x1, x2; rewrite -e.
- by case=> x1 [] x2 e'; exists x1, x2; rewrite e.
Qed.

Lemma lang_monoid_mixin : MonoidMixin lang.
Proof.
constructor.
- move=> A B C x; split; case=> x1 [] x2 [] ex [] H1 H2.
  + case: H2=> x21 [] x22 [] ex2 [] H21 H22.
    exists (x1 ⋅ x21), x22; rewrite -assoc -ex2; split => //.
    split => //. exists x1, x21; eauto.
  + case: H1=> x11 [] x12 [] ex1 [] H11 H12.
    exists x11, (x12 ⋅ x2); rewrite [_ ⋅ _]assoc -ex1; split => //.
    split => //. exists x12, x2; eauto.
- move=> A x; split.
  + by case=> x1 [] x2 [] -> [] ->; rewrite left_id.
  + move=> ?; exists 1, x; rewrite left_id; do !split => //.
    rewrite {1}/one /lang_one /=; reflexivity.
- move=> A x; split.
  + by case=> x1 [] x2 [] -> [] ? ->; rewrite right_id.
  + move=> ?; exists x, 1; rewrite right_id; do !split => //.
    rewrite {1}/one /lang_one /=; reflexivity.
- move=> A1 A2 eA B1 B2 eB x; split; case=> x1 [] x2.
  + by rewrite eA eB => H; exists x1, x2.
  + by rewrite -eA -eB => H; exists x1, x2.
Qed.

Canonical Structure lang_monoid :=
  @Monoid' lang _ _ _ _
           lang_monoid_mixin.

Global Program Instance lang_bottom : Bottom lang :=
  {| lang_car := λ x, False |}.

Global Program Instance lang_join : Join lang := λ A B,
  {| lang_car := λ x, A x ∨ B x |}.
Next Obligation. by move=> A B x y ->. Qed.

Global Instance lang_sqsubseteq : SqSubsetEq lang := λ A B,
  ∀ x, A x → B x.

Lemma lang_semi_lattice_mixin : SemiLatticeMixin lang.
Proof.
rewrite /lang_bottom /lang_join /lang_sqsubseteq; constructor.
- by move=> A B C x; rewrite /union /= assoc.
- by move=> A B x; rewrite /union /= [_ ∨ _]comm.
- by move=> A x; rewrite /union /empty /= left_id.
- move=> A x; rewrite /union /=; tauto.
- by move=> A1 A2 eA B1 B2 eB x; rewrite /union /= eA eB.
- move=> A B; split.
  + by move=> AB x /=; firstorder.
  + by move=> AB x Ax; rewrite -(AB x); left.
Qed.

Canonical Structure lang_semi_lattice :=
  @SemiLattice' lang _ _ _ _ _
                lang_semi_lattice_mixin.

Global Program Instance lang_star : Star lang := λ A,
  {| lang_car := λ x, ∃ n, (A ^ n) x |}.
Next Obligation. solve_proper. Qed.

Lemma lang_pre_ka_mixin : PreKAMixin lang.
Proof.
rewrite /lang_bottom /lang_one /lang_join /lang_mul /lang_star.
constructor; rewrite /union /empty /mul /one /star /=.
- by move=> A B C x /=; firstorder.
- by move=> A B C x /=; firstorder.
- by move=> A x /=; firstorder.
- by move=> A x /=; firstorder.
- move=> A x /=; split.
  + case=> [] [|n] /= Ax; eauto.
    case: Ax => x1 [] x2 [] ex [] Ax1 Ax2.
    right; exists x1, x2. rewrite ex; eauto.
  + case=> [ex|[] x1 [] x2 [] ex [] Ax1 [] n Ax2]; first by exists 0.
    exists (S n); rewrite /=; firstorder.
- solve_proper.
Qed.

Canonical Structure lang_pre_ka :=
  @PreKA' lang _ _ _ _ _ _ _ _
          lang_monoid_mixin
          lang_semi_lattice_mixin
          lang_pre_ka_mixin.

Lemma elem_of_lang_join_list {I : Type}
    (f : I → lang) (Bs : list I) x :
  join_list f Bs x ↔
  ∃ b, b ∈ Bs ∧ f b x.
Proof.
elim: Bs => /= [|B Bs ->].
- by split => // - [? [] /elem_of_nil].
- split =>
    [[B_x|[B' [] B'_Bs B'_x]]
    |[B' [] /elem_of_cons [->|]]].
  + by exists B; rewrite elem_of_cons; eauto.
  + exists B'; rewrite elem_of_cons; eauto.
  + by eauto.
  + by move=> B'_Bs B'_x;
      right; exists B'; eauto.
Qed.

Program Definition lang_sing (x : T) : lang :=
  {| lang_car := λ y, y ≡ x |}.
Next Obligation. by move=> x y1 y2 ->. Qed.

Global Instance lang_sing_proper : Proper ((≡) ==> (≡)) lang_sing.
Proof. solve_proper. Qed.

Global Instance lang_sing_monoid_morphism : MonoidMorphism lang_sing.
Proof.
constructor=> //.
- apply _.
- move=> x y z /=; split.
  + by move=> ez; exists x, y; eauto.
  + by case=> x1 [] x2 [] -> [] -> ->.
Qed.

Definition l : ka_term T → lang := ka_term_elim lang_sing.

Global Instance l_pre_ka_morphism : PreKAMorphism l.
Proof. rewrite /l. apply _. Qed.

Global Instance l_semi_lattice_morphism : SemiLatticeMorphism l.
Proof. apply _. Qed.

Program Definition lang_top : lang :=
  {| lang_car := λ x, True |}.

Lemma lang_topP L : L ⊑ lang_top.
Proof. by []. Qed.

Lemma lang_top_sqsubseteq L : lang_top ⊑ L → L ≡ lang_top.
Proof. move=> H x; split => // _; exact: H. Qed.

(* Theorem 5 *)

Lemma l_alt e x : l e x ↔ Unit x ⊑ e.
Proof.
split; last first.
  move=> x_e; have: l (Unit x) ⊑ l e.
    by apply: semi_lattice_morphism_sqsubseteq_proper.
  by move=> /(_ x); apply => /=.
elim: e => //= [y|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e IH] in x *.
- by move=> ->.
- case=> [/IH1 IH|/IH2 IH]; apply (transitivity IH).
  + exact: sqsubseteq_join_left.
  + exact: sqsubseteq_join_right.
- case=> x1 [] x2 [] ex [] /IH1 e1x1 /IH2 e2x2.
  rewrite ex monoid_morphism_mul; exact: pre_ka_mul_mono.
- case=> n; elim: n => /= [|n IHn] in x *.
    move=> ->; exact: pre_ka_one_star.
  case=> x1 [] x2 [] ex [] /IH ex1 /IHn ex2; rewrite ex monoid_morphism_mul.
  apply: (transitivity _ (pre_ka_mul_star e)).
  by apply: pre_ka_mul_mono.
Qed.

Lemma Unit_inj (x y : T) : Unit x ≡ Unit y → x ≡ y.
Proof.
move=> Heq.
have /l_alt Hx : Unit x ⊑ Unit x by reflexivity.
have /l_alt : Unit x ⊑ Unit y by rewrite Heq.
by move=> /= ->.
Qed.

Lemma l_reflects_order xs ys :
  l (⨆ x ∈ xs, Unit x) ⊑
  l (⨆ y ∈ ys, Unit y) →
  (⨆ x ∈ xs, Unit x) ⊑
  (⨆ y ∈ ys, Unit y).
Proof.
move=> l_sub;
  apply/join_list_sqsubseteq => a a_xs.
have /l_alt : Unit a ⊑ ⨆ x ∈ xs, Unit x
  by exact: sqsubseteq_join_list.
move=> /l_sub.
rewrite semi_lattice_morphism_join_list
  elem_of_lang_join_list.
case=> b [] b_ys /= ->.
by exact: sqsubseteq_join_list.
Qed.

(* Corollary 7 *)

Lemma l_inj_finite xs ys :
  l (⨆ x ∈ xs, Unit x) ≡
  l (⨆ y ∈ ys, Unit y) →
  (⨆ x ∈ xs, Unit x) ≡
  (⨆ y ∈ ys, Unit y).
Proof.
move=> l_eq; apply: anti_symm; by apply/l_reflects_order; rewrite l_eq.
Qed.

(* Corollary 8 *)

Lemma either_empty_or_nonzero e : (e ≡ ⊥) + {s | l e s}.
Proof.
elim: e => /=; try by eauto.
- rewrite -[@ka_term_join T]/(@join _ _) -[ka_term_elim lang_sing]/(l).
  move=> e1 [e1B|[x1 e1_x1]] e2 [e2B|[x2 e2_x2]]; eauto.
  by left; rewrite e1B e2B left_id.
- rewrite -[@ka_term_mul T]/(@mul _ _) -[ka_term_elim lang_sing]/(l).
  move=> e1 [e1B|[x1 e1_x1]] e2 [e2B|[x2 e2_x2]].
  + by left; rewrite e1B left_absorb.
  + by left; rewrite e1B left_absorb.
  + by left; rewrite e2B right_absorb.
  + by eauto 10.
- rewrite -[@ka_term_star T]/(@star _ _) -[ka_term_elim lang_sing]/(l).
  by move=> e _; right; exists 1, 0 => /=.
Qed.

End Languages.

Section LangMap.

Variables (T S : monoid) (f : T → S).
Context `{!MonoidMorphism f}.

Program Definition lang_map (L : lang T) : lang S :=
  {| lang_car := λ s, ∃ t, s ≡ f t ∧ L t |}.
Next Obligation.
move=> L s1 s2 es; split; case=> t [] et Lt; exists t; split => //.
- by rewrite -es.
- by rewrite es.
Qed.

Global Instance lang_map_proper : Proper ((≡) ==> (≡)) lang_map.
Proof.
move=> L1 L2 eL s /=; split; case=> t [] et Lt; exists t; split => //;
by [rewrite (eL t)|rewrite -(eL t)].
Qed.

Lemma lang_map_one : lang_map 1 ≡ (1 : lang S).
Proof.
move=> s /=; split.
- by case=> t [] -> /= ->; rewrite monoid_morphism_one.
- by move=> es; exists 1; rewrite monoid_morphism_one; split.
Qed.

Lemma lang_map_mul (A B : lang T) : lang_map (A ⋅ B) ≡ lang_map A ⋅ lang_map B.
Proof.
move=> s /=; split.
- case=> t [] et [] t1 [] t2 [] et12 [] At1 Bt2.
  exists (f t1), (f t2); split; first by rewrite et et12 monoid_morphism_mul.
  split; [exists t1 | exists t2]; eauto.
- case=> s1 [] s2 [] es [] [t1 [] et1 At1] [t2 [] et2 Bt2].
  exists (t1 ⋅ t2); split; first by rewrite monoid_morphism_mul -et1 -et2.
  by exists t1, t2.
Qed.

Global Instance lang_map_monoid_morphism : MonoidMorphism lang_map.
Proof.
split.
- exact: lang_map_proper.
- exact: lang_map_one.
- exact: lang_map_mul.
Qed.

Lemma lang_map_bottom : lang_map ⊥ ≡ (⊥ : lang S).
Proof.
by move=> s /=; split => // - [t []].
Qed.

Lemma lang_map_join (A B : lang T) : lang_map (A ⊔ B) ≡ lang_map A ⊔ lang_map B.
Proof.
move=> s /=; split.
- case=> t [] et [At|Bt]; [left|right]; exists t; eauto.
- case=> [[t [] et At]|[t [] et Bt]]; exists t; split => //; [left|right] => //.
Qed.

Lemma lang_map_star (A : lang T) : lang_map (star A) ≡ star (lang_map A).
Proof.
move=> s /=; split.
- case=> t [] et [n Hn]; exists n.
  by rewrite -(monoid_morphism_power (f := lang_map) A n); exists t.
- case=> [n]; rewrite -(monoid_morphism_power (f := lang_map) A n).
  by case=> t [] et Hn; exists t; split => //; exists n.
Qed.

Lemma lang_map_pre_ka_mixin : PreKAMixin (lang S).
Proof. exact: lang_pre_ka_mixin. Qed.

Global Instance lang_map_pre_ka_morphism : PreKAMorphism lang_map.
Proof.
constructor.
- exact: lang_map_proper.
- exact: lang_map_one.
- exact: lang_map_mul.
- exact: lang_map_bottom.
- exact: lang_map_join.
- exact: lang_map_star.
Qed.

End LangMap.

Section LangNaturality.

Variables (M N : monoid) (f : M → N).
Context `{!MonoidMorphism f}.

Lemma l_natural (e : ka_term M) :
  l (ka_term_map f e) ≡ lang_map f (l e).
Proof.
apply: (@ka_term_ext _ _ (fun e => l (ka_term_map f e))
                         (fun e => lang_map f (l e)) _ _).
by move=> x y /=; split; eauto; case=> _ [-> ->].
Qed.

End LangNaturality.

Section LangTop.

Context `{!MonoidGen G T, !EqDecision G, !Finite G}.

Lemma l_pseudo_top : l pseudo_top ≡ @lang_top T.
Proof.
move=> x; split=> // _.
by apply/l_alt; exact: unit_le_pseudo_top.
Qed.

End LangTop.

Section TermProperties.

Variables (T : monoid).

Lemma ka_term_diag_spec (e : ka_term T) (sl sr : T) :
  Unit (sl, sr) ⊑ ka_term_diag e ↔ sl ≡ sr ∧ Unit sl ⊑ e.
Proof.
rewrite -!l_alt l_natural /= /pair_mor /=.
split.
- by case=> t [[] /= -> -> He]; split.
- case=> eqs He; exists sl; split => //; split => /=; by [|symmetry].
Qed.

Lemma Unit_sqsubseteq (s1 s2 : T) :
  Unit s1 ⊑ Unit s2 ↔ s1 ≡ s2.
Proof.
split=> [s1_s2|->] //.
have {}s1_s2: l (Unit s1) ⊑ l (Unit s2).
  exact: semi_lattice_morphism_sqsubseteq_proper.
by move/(_ s1): s1_s2; apply; rewrite /=.
Qed.

End TermProperties.
