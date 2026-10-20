(* Kleene algebras: `KAMixin` adds Kozen's two star induction rules to the
   pre-KA structure of KA/pre_ka.v. Languages form a KA (`lang_ka`).

   `free_ka P` is the free KA over a pre-KA `P`: terms over the elements of
   `P`, modulo the least congruence that contains the pre-KA laws, the
   operation table of `P` (`Unit (x ⊔ y) ≡ Unit x ⊔ Unit y`, etc.) and is
   closed under star induction. `free_ka_unit : P → free_ka P` is a pre-KA
   morphism through which every pre-KA morphism into a KA factors uniquely
   (`free_ka_lift`, `free_ka_lift_unit`, `free_ka_ext`). The unit need not be
   injective: it identifies whatever `P` distinguishes only through the
   absence of star induction. Pulling the free KA over the free pre-KA
   `ka_term M` back to `ka_term M` gives the free KA over a monoid, `fka M`:
   boxed terms (`FKA`, a coercion), compared by KA derivability, so that
   `FKA e1 ⊑ e2` reads "KA proves `e1 ⊑ e2`". It is sound for languages
   (`fka_lang`).

   In any KA, the star of a sum of commuting elements splits as
   `star (x ⊔ y) ≡ (1 ⊔ x ⋅ star x ⊔ y ⋅ star y) ⋅ star (x ⋅ y)`
   (`ka_star_join_comm`), and over a finitely generated monoid `pseudo_top`
   is the greatest element of the free KA (`fka_top_greatest`). Both use
   star induction. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.

(** Kleene algebras *)

Record KAMixin T `{!Equiv T, Join T, Mul T, Star T, SqSubsetEq T} := {
  mixin_ka_star_ind_l : ∀ x y z : T, y ⊔ x ⋅ z ⊑ z → star x ⋅ y ⊑ z;
  mixin_ka_star_ind_r : ∀ x y z : T, y ⊔ z ⋅ x ⊑ z → y ⋅ star x ⊑ z;
}.
Arguments KAMixin T {_ _ _ _ _}.

Structure ka : Type := KA' {
  ka_car :> Type;
  ka_equiv : Equiv ka_car;
  ka_join : Join ka_car;
  ka_bottom : Bottom ka_car;
  ka_sqsubseteq : SqSubsetEq ka_car;
  ka_mul : Mul ka_car;
  ka_one : One ka_car;
  ka_star : Star ka_car;
  ka_setoid_mixin : Equivalence (≡@{ka_car});
  ka_monoid_mixin : MonoidMixin ka_car;
  ka_semi_lattice_mixin : SemiLatticeMixin ka_car;
  ka_pre_ka_mixin : PreKAMixin ka_car;
  ka_mixin : KAMixin ka_car;
}.
Global Arguments ka_car : simpl never.
Global Arguments ka_equiv : simpl never.
Global Arguments ka_join : simpl never.
Global Arguments ka_bottom : simpl never.
Global Arguments ka_sqsubseteq : simpl never.
Global Arguments ka_mul : simpl never.
Global Arguments ka_one : simpl never.
Global Arguments ka_star : simpl never.
Global Arguments ka_setoid_mixin : simpl never.
Global Arguments ka_monoid_mixin : simpl never.
Global Arguments ka_semi_lattice_mixin : simpl never.
Global Arguments ka_pre_ka_mixin : simpl never.
Global Arguments ka_mixin : simpl never.
Coercion ka_setoid (T : ka) :=
  @Setoid T _ (ka_setoid_mixin T).
Coercion ka_monoid (T : ka) :=
  @Monoid' T _ _ _ (ka_setoid_mixin T) (ka_monoid_mixin T).
Coercion ka_semi_lattice (T : ka) :=
  @SemiLattice' T _ _ _ _ (ka_setoid_mixin T) (ka_semi_lattice_mixin T).
Coercion ka_pre_ka (T : ka) :=
  @PreKA' T _ _ _ _ _ _ _ (ka_setoid_mixin T) (ka_monoid_mixin T)
    (ka_semi_lattice_mixin T) (ka_pre_ka_mixin T).
Canonical Structure ka_setoid.
Canonical Structure ka_monoid.
Canonical Structure ka_semi_lattice.
Canonical Structure ka_pre_ka.

Section KATheory.

Variable T : ka.

Implicit Types x y z : T.

Lemma ka_star_ind_l x y z : y ⊔ x ⋅ z ⊑ z → star x ⋅ y ⊑ z.
Proof. exact: (mixin_ka_star_ind_l (ka_mixin T)). Qed.

Lemma ka_star_ind_r x y z : y ⊔ z ⋅ x ⊑ z → y ⋅ star x ⊑ z.
Proof. exact: (mixin_ka_star_ind_r (ka_mixin T)). Qed.

Lemma ka_star_ind_l' x y : x ⋅ y ⊑ y → star x ⋅ y ⊑ y.
Proof. by move=> H; apply: ka_star_ind_l; apply/join_sqsubseteq. Qed.

Lemma ka_star_ind_r' x y : y ⋅ x ⊑ y → y ⋅ star x ⊑ y.
Proof. by move=> H; apply: ka_star_ind_r; apply/join_sqsubseteq. Qed.

Lemma ka_star_le x y : 1 ⊔ x ⋅ y ⊑ y → star x ⊑ y.
Proof. by move=> /ka_star_ind_l; rewrite right_id. Qed.

Global Instance ka_star_mono : Proper ((⊑) ==> (⊑)) (@star T _).
Proof.
move=> x y xy; apply: ka_star_le; apply/join_sqsubseteq; split.
  exact: pre_ka_one_star.
rewrite xy; exact: pre_ka_mul_star.
Qed.

Lemma ka_star_one : star (1 : T) ≡ 1.
Proof.
apply: (anti_symm (⊑)); last exact: pre_ka_one_star.
by apply: ka_star_le; rewrite left_id idemp.
Qed.

Lemma ka_star_mul_star x : star x ⋅ star x ≡ star x.
Proof.
apply: (anti_symm (⊑)).
  apply: ka_star_ind_l; apply/join_sqsubseteq; split => //.
  exact: pre_ka_mul_star.
rewrite -{1}[star x](left_id 1); apply: pre_ka_mul_mono => //.
exact: pre_ka_one_star.
Qed.

(* Commuting elements commute with stars (Kozen). *)
Lemma ka_star_comm x y : x ⋅ y ≡ y ⋅ x → star x ⋅ y ≡ y ⋅ star x.
Proof.
move=> exy; apply: (anti_symm (⊑)).
- apply: ka_star_ind_l; apply/join_sqsubseteq; split.
    rewrite -{1}[y](right_id 1); apply: pre_ka_mul_mono => //.
    exact: pre_ka_one_star.
  by rewrite assoc exy -assoc pre_ka_mul_star.
- apply: ka_star_ind_r; apply/join_sqsubseteq; split.
    rewrite -{1}[y](left_id 1); apply: pre_ka_mul_mono => //.
    exact: pre_ka_one_star.
  rewrite -assoc -exy assoc; apply: pre_ka_mul_mono => //.
  rewrite -{2}(ka_star_mul_star x); apply: pre_ka_mul_mono => //.
  exact: pre_ka_star_infl.
Qed.

Lemma ka_mul_le_star x y z : x ⊑ star z → y ⊑ star z → x ⋅ y ⊑ star z.
Proof.
by move=> -> ->; rewrite ka_star_mul_star.
Qed.

(* The star of a sum of commuting elements: every word over `x` and `y` is
   a power of `x ⋅ y` preceded by a power of `x` or of `y`. *)
Lemma ka_star_join_comm x y :
  x ⋅ y ≡ y ⋅ x →
  star (x ⊔ y) ≡ (1 ⊔ x ⋅ star x ⊔ y ⋅ star y) ⋅ star (x ⋅ y).
Proof.
move=> exy; set C := star (x ⋅ y).
have Cx : star x ⋅ (x ⋅ y) ≡ (x ⋅ y) ⋅ star x.
  by apply: ka_star_comm; rewrite -assoc -exy.
have Cy : star y ⋅ (x ⋅ y) ≡ (x ⋅ y) ⋅ star y.
  by apply: ka_star_comm; rewrite assoc -exy.
have xS : x ⊑ star (x ⊔ y).
  rewrite -pre_ka_star_infl; exact: sqsubseteq_join_left.
have yS : y ⊑ star (x ⊔ y).
  rewrite -pre_ka_star_infl; exact: sqsubseteq_join_right.
have xsS : star x ⊑ star (x ⊔ y).
  apply: ka_star_mono; exact: sqsubseteq_join_left.
have ysS : star y ⊑ star (x ⊔ y).
  apply: ka_star_mono; exact: sqsubseteq_join_right.
have CC : (x ⋅ y) ⋅ C ⊑ C by exact: pre_ka_mul_star.
apply: (anti_symm (⊑)).
- apply: ka_star_le; apply/join_sqsubseteq; split.
    rewrite -{1}(left_id 1 (⋅) 1); apply: pre_ka_mul_mono.
      by rewrite -!sqsubseteq_join_left.
    exact: pre_ka_one_star.
  rewrite -[1 ⊔ x ⋅ star x]pre_ka_star_unfold.
  rewrite pre_ka_left_dist; apply/join_sqsubseteq; split.
  + rewrite assoc pre_ka_right_dist pre_ka_left_dist.
    apply/join_sqsubseteq; split.
      apply: pre_ka_mul_mono => //; rewrite -sqsubseteq_join_left.
      exact: pre_ka_mul_star.
    rewrite assoc -[(x ⋅ y) ⋅ star y]Cy -assoc CC.
    apply: pre_ka_mul_mono => //.
    rewrite {1}[star y]pre_ka_star_unfold; apply/join_sqsubseteq; split.
      rewrite -sqsubseteq_join_left; exact: pre_ka_one_star.
    exact: sqsubseteq_join_right.
  + rewrite assoc pre_ka_right_dist pre_ka_left_dist.
    apply/join_sqsubseteq; split.
      rewrite {1}[star x]pre_ka_star_unfold pre_ka_right_dist right_id.
      rewrite pre_ka_left_dist; apply/join_sqsubseteq; split.
        apply: pre_ka_mul_mono => //; rewrite -sqsubseteq_join_right.
        rewrite -{1}[y](right_id 1 (⋅)); apply: pre_ka_mul_mono => //.
        exact: pre_ka_one_star.
      rewrite assoc -exy -[(x ⋅ y) ⋅ star x]Cx -assoc CC.
      apply: pre_ka_mul_mono => //.
      exact: sqsubseteq_join_left.
    apply: pre_ka_mul_mono => //; rewrite -sqsubseteq_join_right.
    apply: pre_ka_mul_mono => //; exact: pre_ka_mul_star.
- rewrite -[star (x ⊔ y)]ka_star_mul_star; apply: pre_ka_mul_mono.
    apply/join_sqsubseteq; split; last exact: ka_mul_le_star.
    apply/join_sqsubseteq; split; last exact: ka_mul_le_star.
    exact: pre_ka_one_star.
  apply: ka_star_le; apply/join_sqsubseteq; split.
    exact: pre_ka_one_star.
  apply: ka_mul_le_star => //; exact: ka_mul_le_star.
Qed.

End KATheory.

(** Languages form a Kleene algebra. *)

Section LangKA.

Variable T : monoid.

Lemma lang_ka_mixin : KAMixin (lang T).
Proof.
constructor.
- move=> A B C /join_sqsubseteq [BC AC].
  have H : ∀ n, A ^ n ⋅ B ⊑ C.
    elim=> [|n IH] /=; first by rewrite left_id.
    by rewrite -assoc IH.
  move=> x [x1 [x2 [ex [[n Hn] Hx2]]]].
  by apply: (H n); exists x1, x2.
- move=> A B C /join_sqsubseteq [BC CA].
  have H : ∀ n B', B' ⊑ C → B' ⋅ A ^ n ⊑ C.
    elim=> [|n IH] B' B'C /=; first by rewrite right_id.
    rewrite -/(power A n) assoc; apply: IH.
    by rewrite B'C.
  move=> x [x1 [x2 [ex [Hx1 [n Hn]]]]].
  by apply: (H n B BC); exists x1, x2.
Qed.

Canonical Structure lang_ka :=
  @KA' (lang T) _ _ _ _ _ _ _ _
       (lang_monoid_mixin T)
       (lang_semi_lattice_mixin T)
       (lang_pre_ka_mixin T)
       lang_ka_mixin.

End LangKA.

(** * The free Kleene algebra over a pre-Kleene algebra

    Its elements are terms over `P` in a box, so that their instances do not
    conflict with those of `ka_term P`. *)

Section FreeKA.

Variable P : pre_ka.

Implicit Types (x y : P) (e : ka_term P).

(* `ka_eq` provides the pre-KA laws on terms, together with the monoid
   part of the operation table of `P` (`Unit (x ⋅ y)`, `Unit 1 = 1`,
   compatibility of `Unit` with `≡`). *)
Inductive free_ka_eq : relation (ka_term P) :=
  | fk_refl e : free_ka_eq e e
  | fk_sym e1 e2 : free_ka_eq e1 e2 → free_ka_eq e2 e1
  | fk_trans e1 e2 e3 :
      free_ka_eq e1 e2 → free_ka_eq e2 e3 → free_ka_eq e1 e3
  | fk_pre e1 e2 : e1 ≡@{ka_term P} e2 → free_ka_eq e1 e2
  | fk_join_proper e1 e1' e2 e2' :
      free_ka_eq e1 e1' → free_ka_eq e2 e2' →
      free_ka_eq (e1 ⊔ e2) (e1' ⊔ e2')
  | fk_mul_proper e1 e1' e2 e2' :
      free_ka_eq e1 e1' → free_ka_eq e2 e2' →
      free_ka_eq (e1 ⋅ e2) (e1' ⋅ e2')
  | fk_star_proper e e' : free_ka_eq e e' → free_ka_eq (star e) (star e')
  | fk_unit_bottom : free_ka_eq (Unit ⊥) ⊥
  | fk_unit_join x y : free_ka_eq (Unit (x ⊔ y)) (Unit x ⊔ Unit y)
  | fk_unit_star x : free_ka_eq (Unit (star x)) (star (Unit x))
  | fk_star_ind_l e1 e2 e3 :
      free_ka_eq ((e2 ⊔ e1 ⋅ e3) ⊔ e3) e3 →
      free_ka_eq (star e1 ⋅ e2 ⊔ e3) e3
  | fk_star_ind_r e1 e2 e3 :
      free_ka_eq ((e2 ⊔ e3 ⋅ e1) ⊔ e3) e3 →
      free_ka_eq (e2 ⋅ star e1 ⊔ e3) e3.

Record free_ka_car := FreeKA { free_ka_term : ka_term P }.

Global Instance free_ka_equiv : Equiv free_ka_car :=
  λ a b, free_ka_eq (free_ka_term a) (free_ka_term b).
Global Instance free_ka_join : Join free_ka_car :=
  λ a b, FreeKA (free_ka_term a ⊔ free_ka_term b).
Global Instance free_ka_bottom : Bottom free_ka_car := FreeKA ⊥.
Global Instance free_ka_mul : Mul free_ka_car :=
  λ a b, FreeKA (free_ka_term a ⋅ free_ka_term b).
Global Instance free_ka_one : One free_ka_car := FreeKA 1.
Global Instance free_ka_star : Star free_ka_car :=
  λ a, FreeKA (star (free_ka_term a)).
Global Instance free_ka_sqsubseteq : SqSubsetEq free_ka_car :=
  default_sqsubseteq.

Global Instance free_ka_equivalence : Equivalence (≡@{free_ka_car}).
Proof.
constructor.
- move=> ?; exact: fk_refl.
- move=> ??; exact: fk_sym.
- move=> ???; exact: fk_trans.
Qed.

Lemma free_ka_monoid_mixin : MonoidMixin free_ka_car.
Proof.
constructor.
- by move=> ???; apply: fk_pre; apply: ka_mul_assoc.
- by move=> ?; apply: fk_pre; apply: ka_mul_left_id.
- by move=> ?; apply: fk_pre; apply: ka_mul_right_id.
- by move=> ?? H1 ?? H2; apply: fk_mul_proper.
Qed.

Lemma free_ka_semi_lattice_mixin : SemiLatticeMixin free_ka_car.
Proof.
apply: default_semi_lattice_mixin.
- by move=> ???; apply: fk_pre; apply: ka_join_assoc.
- by move=> ??; apply: fk_pre; apply: ka_join_comm.
- by move=> ?; apply: fk_pre; apply: ka_join_left_id.
- by move=> ?; apply: fk_pre; apply: ka_join_idemp.
- by move=> ?? H1 ?? H2; apply: fk_join_proper.
Qed.

Lemma free_ka_pre_ka_mixin : PreKAMixin free_ka_car.
Proof.
constructor.
- by move=> ???; apply: fk_pre; apply: ka_mul_join_right.
- by move=> ???; apply: fk_pre; apply: ka_mul_join_left.
- by move=> ?; apply: fk_pre; apply: ka_mul_left_absorb.
- by move=> ?; apply: fk_pre; apply: ka_mul_right_absorb.
- by move=> ?; apply: fk_pre; apply: ka_star_unfold.
- by move=> ?? H; apply: fk_star_proper.
Qed.

Lemma free_ka_ka_mixin : KAMixin free_ka_car.
Proof.
constructor=> a b c /default_sqsubseteq_eq H; apply/default_sqsubseteq_eq.
- exact: fk_star_ind_l.
- exact: fk_star_ind_r.
Qed.

Canonical Structure free_ka :=
  @KA' free_ka_car _ _ _ _ _ _ _ _
       free_ka_monoid_mixin
       free_ka_semi_lattice_mixin
       free_ka_pre_ka_mixin
       free_ka_ka_mixin.

Definition free_ka_unit (x : P) : free_ka := FreeKA (Unit x).

Global Instance free_ka_unit_morphism : PreKAMorphism free_ka_unit.
Proof.
constructor.
- by move=> ???; apply: fk_pre; apply: ka_unit_proper.
- by [].
- by move=> ??; apply: fk_pre; apply: ka_mul_distr.
- exact: fk_unit_bottom.
- exact: fk_unit_join.
- exact: fk_unit_star.
Qed.

Section Lift.

Variables (K : ka) (f : P → K).
Context `{!PreKAMorphism f}.

Definition free_ka_lift (a : free_ka) : K := ka_term_elim f (free_ka_term a).

Global Instance free_ka_lift_morphism : PreKAMorphism free_ka_lift.
Proof.
constructor => //=.
- move=> [e1] [e2] H; change (free_ka_eq e1 e2) in H.
  rewrite /free_ka_lift /=; elim: e1 e2 / H => /=.
  + by [].
  + by move=> ?? _ ->.
  + by move=> ??? _ -> _ ->.
  + by move=> e1 e2 /(pre_ka_morphism_proper (f := ka_term_elim f)).
  + by move=> ???? _ -> _ ->.
  + by move=> ???? _ -> _ ->.
  + by move=> ?? _ ->.
  + exact: pre_ka_morphism_bottom.
  + exact: pre_ka_morphism_join.
  + exact: pre_ka_morphism_star.
  + move=> e1 e2 e3 _ /sqsubseteq_iff H; apply/sqsubseteq_iff.
    exact: ka_star_ind_l.
  + move=> e1 e2 e3 _ /sqsubseteq_iff H; apply/sqsubseteq_iff.
    exact: ka_star_ind_r.
- rewrite /free_ka_lift /=; exact: pre_ka_morphism_one.
Qed.

Lemma free_ka_lift_unit x : free_ka_lift (free_ka_unit x) = f x.
Proof. by []. Qed.

End Lift.

(* Morphisms out of the free KA are determined by their action on the
   generators. *)
Lemma free_ka_ext (S : pre_ka) (g h : free_ka → S) :
  PreKAMorphism g → PreKAMorphism h →
  (∀ x, g (free_ka_unit x) ≡ h (free_ka_unit x)) →
  ∀ a : free_ka, g a ≡ h a.
Proof.
move=> Hg Hh Hunit [e]; elim: e.
- exact: Hunit.
- change (g ⊥ ≡ h ⊥); by rewrite !pre_ka_morphism_bottom.
- move=> e1 IH1 e2 IH2; change (g (FreeKA e1 ⊔ FreeKA e2) ≡
                                 h (FreeKA e1 ⊔ FreeKA e2)).
  by rewrite !pre_ka_morphism_join IH1 IH2.
- move=> e1 IH1 e2 IH2; change (g (FreeKA e1 ⋅ FreeKA e2) ≡
                                 h (FreeKA e1 ⋅ FreeKA e2)).
  by rewrite !pre_ka_morphism_mul IH1 IH2.
- move=> e IH; change (g (star (FreeKA e)) ≡ h (star (FreeKA e))).
  by rewrite !pre_ka_morphism_star IH.
Qed.

End FreeKA.

Add Printing Constructor free_ka_car.

(** * The free Kleene algebra over a monoid

    `fka M` boxes the terms over `M`. Its operations are those of
    `ka_term M`, and two terms are equivalent when KA proves them equal,
    i.e. when the free KA over the free pre-KA `ka_term M` identifies them.
    `FKA` is a coercion, so `FKA e1 ⊑ e2` states that KA proves
    `e1 ⊑ e2`. *)

Section FKA.

Variable M : monoid.

Implicit Types (e : ka_term M).

Record fka := FKA { fka_term : ka_term M }.

Definition fka_embed (a : fka) : free_ka (ka_term_pre_ka M) :=
  free_ka_unit (fka_term a).

Global Instance fka_equiv : Equiv fka := λ a b, fka_embed a ≡ fka_embed b.
Global Instance fka_join : Join fka := λ a b, FKA (fka_term a ⊔ fka_term b).
Global Instance fka_bottom : Bottom fka := FKA ⊥.
Global Instance fka_mul : Mul fka := λ a b, FKA (fka_term a ⋅ fka_term b).
Global Instance fka_one : One fka := FKA 1.
Global Instance fka_star : Star fka := λ a, FKA (star (fka_term a)).
Global Instance fka_sqsubseteq : SqSubsetEq fka := default_sqsubseteq.

Global Instance fka_equivalence : Equivalence (≡@{fka}).
Proof.
constructor.
- by move=> a; rewrite /equiv /fka_equiv.
- by move=> a b; rewrite /equiv /fka_equiv.
- by move=> a b c; rewrite /equiv /fka_equiv => ->.
Qed.

Lemma fka_of_pre e1 e2 : e1 ≡ e2 → FKA e1 ≡ FKA e2.
Proof. exact: (pre_ka_morphism_proper (f := free_ka_unit (P := _))). Qed.

Lemma fka_embed_join a b : fka_embed (a ⊔ b) ≡ fka_embed a ⊔ fka_embed b.
Proof. exact: pre_ka_morphism_join. Qed.

Lemma fka_embed_mul a b : fka_embed (a ⋅ b) ≡ fka_embed a ⋅ fka_embed b.
Proof. exact: pre_ka_morphism_mul. Qed.

Lemma fka_embed_star a : fka_embed (star a) ≡ star (fka_embed a).
Proof. exact: pre_ka_morphism_star. Qed.

Lemma fka_monoid_mixin : MonoidMixin fka.
Proof.
constructor.
- by move=> ???; apply: fka_of_pre; apply: ka_mul_assoc.
- by move=> ?; apply: fka_of_pre; apply: ka_mul_left_id.
- by move=> ?; apply: fka_of_pre; apply: ka_mul_right_id.
- move=> ?? H1 ?? H2; move: H1 H2; rewrite /equiv /fka_equiv => H1 H2.
  by rewrite !fka_embed_mul H1 H2.
Qed.

Lemma fka_semi_lattice_mixin : SemiLatticeMixin fka.
Proof.
apply: default_semi_lattice_mixin.
- by move=> ???; apply: fka_of_pre; apply: ka_join_assoc.
- by move=> ??; apply: fka_of_pre; apply: ka_join_comm.
- by move=> ?; apply: fka_of_pre; apply: ka_join_left_id.
- by move=> ?; apply: fka_of_pre; apply: ka_join_idemp.
- move=> ?? H1 ?? H2; move: H1 H2; rewrite /equiv /fka_equiv => H1 H2.
  by rewrite !fka_embed_join H1 H2.
Qed.

Lemma fka_pre_ka_mixin : PreKAMixin fka.
Proof.
constructor.
- by move=> ???; apply: fka_of_pre; apply: ka_mul_join_right.
- by move=> ???; apply: fka_of_pre; apply: ka_mul_join_left.
- by move=> ?; apply: fka_of_pre; apply: ka_mul_left_absorb.
- by move=> ?; apply: fka_of_pre; apply: ka_mul_right_absorb.
- by move=> ?; apply: fka_of_pre; apply: ka_star_unfold.
- move=> ?? H; move: H; rewrite /equiv /fka_equiv => H.
  by rewrite !fka_embed_star H.
Qed.

Lemma fka_ka_mixin : KAMixin fka.
Proof.
constructor=> a b c /default_sqsubseteq_eq H; apply/default_sqsubseteq_eq;
  move: H; rewrite /equiv /fka_equiv !fka_embed_join !fka_embed_mul
    fka_embed_star => /sqsubseteq_iff H; apply/sqsubseteq_iff.
- exact: ka_star_ind_l.
- exact: ka_star_ind_r.
Qed.

Canonical Structure fka_ka :=
  @KA' fka _ _ _ _ _ _ _ _
       fka_monoid_mixin
       fka_semi_lattice_mixin
       fka_pre_ka_mixin
       fka_ka_mixin.

Canonical Structure fka_setoid := @Setoid fka _ fka_equivalence.
Canonical Structure fka_monoid := @Monoid' fka _ _ _ _ fka_monoid_mixin.
Canonical Structure fka_semi_lattice :=
  @SemiLattice' fka _ _ _ _ _ fka_semi_lattice_mixin.
Canonical Structure fka_pre_ka :=
  @PreKA' fka _ _ _ _ _ _ _ _
          fka_monoid_mixin fka_semi_lattice_mixin fka_pre_ka_mixin.

Global Instance FKA_morphism :
  PreKAMorphism (T := ka_term_pre_ka M) (S := fka_ka) FKA.
Proof. constructor => //; exact: fka_of_pre. Qed.

(* Every inequality of pre-KA holds in KA. *)
Lemma fka_le_of_pre e1 e2 : e1 ⊑ e2 → FKA e1 ⊑ FKA e2.
Proof.
exact: (semi_lattice_morphism_sqsubseteq_proper
          (T := ka_term_pre_ka M) (S := fka_ka) (f := FKA)).
Qed.

Section Lift.

Variables (K : ka) (f : M → K).
Context `{!MonoidMorphism f}.

Definition fka_lift (a : fka) : K := ka_term_elim f (fka_term a).

Global Instance fka_lift_morphism : PreKAMorphism fka_lift.
Proof.
constructor => //=.
- move=> a b H.
  exact: (pre_ka_morphism_proper (f := free_ka_lift (ka_term_elim f)) H).
- rewrite /fka_lift /=; exact: monoid_morphism_one.
Qed.

Lemma fka_lift_unit x : fka_lift (FKA (Unit x)) = f x.
Proof. by []. Qed.

End Lift.

Lemma fka_ext (S : pre_ka) (g h : fka → S) :
  PreKAMorphism g → PreKAMorphism h →
  (∀ x, g (FKA (Unit x)) ≡ h (FKA (Unit x))) →
  ∀ a, g a ≡ h a.
Proof.
move=> Hg Hh Hunit [e]; elim: e.
- exact: Hunit.
- change (g ⊥ ≡ h ⊥); by rewrite !pre_ka_morphism_bottom.
- move=> e1 IH1 e2 IH2; change (g (FKA e1 ⊔ FKA e2) ≡ h (FKA e1 ⊔ FKA e2)).
  by rewrite !pre_ka_morphism_join IH1 IH2.
- move=> e1 IH1 e2 IH2; change (g (FKA e1 ⋅ FKA e2) ≡ h (FKA e1 ⋅ FKA e2)).
  by rewrite !pre_ka_morphism_mul IH1 IH2.
- move=> e IH; change (g (star (FKA e)) ≡ h (star (FKA e))).
  by rewrite !pre_ka_morphism_star IH.
Qed.

(* KA is sound for languages. *)
Lemma fka_lang e1 e2 : FKA e1 ⊑ FKA e2 → l e1 ⊑ l e2.
Proof.
exact: (semi_lattice_morphism_sqsubseteq_proper
          (f := fka_lift (K := lang_ka M) (lang_sing (T := M)))).
Qed.

End FKA.

(* Always printed, so that `FKA e1 ⊑ FKA e2` (KA) is not displayed like
   `e1 ⊑ e2` (pre-KA). *)
#[warnings="-uniform-inheritance"]
Coercion FKA : ka_term >-> fka.
Add Printing Coercion FKA.
Add Printing Constructor fka.

(** * `pseudo_top` is the top element of the free KA

    Over a finitely generated monoid, the star of all generators is above
    every term in KA. *)

Section PseudoTopKA.

Context {G : Type} {M : monoid} `{!MonoidGen G M, !EqDecision G, !Finite G}.

Notation top := (FKA (@pseudo_top G M _ _ _)).

Lemma fka_top_star :
  top = star (FKA (⨆ g ∈ enum G, Unit (generator_interp g))).
Proof. by []. Qed.

Lemma fka_top_closed_mul (a b : fka M) : a ⊑ top → b ⊑ top → a ⋅ b ⊑ top.
Proof. rewrite fka_top_star; exact: ka_mul_le_star. Qed.

Lemma fka_top_closed_star (a : fka M) : a ⊑ top → star a ⊑ top.
Proof.
move=> Ha; apply: ka_star_le; apply/join_sqsubseteq; split.
  rewrite fka_top_star; exact: pre_ka_one_star.
exact: fka_top_closed_mul.
Qed.

Theorem fka_top_greatest (a : fka M) : a ⊑ top.
Proof.
case: a => e; elim: e.
- by move=> x; apply: fka_le_of_pre; exact: unit_le_pseudo_top.
- exact: bottom_sqsubseteq.
- move=> e1 IH1 e2 IH2; change (FKA e1 ⊔ FKA e2 ⊑ top).
  by apply/join_sqsubseteq.
- move=> e1 IH1 e2 IH2; change (FKA e1 ⋅ FKA e2 ⊑ top).
  exact: fka_top_closed_mul.
- move=> e IH; change (star (FKA e) ⊑ top).
  exact: fka_top_closed_star.
Qed.

(* Universality: `Σ* ⊑ e` and `e ≡ Σ*` coincide in KA. *)
Corollary fka_top_iff (a : fka M) : top ⊑ a ↔ a ≡ top.
Proof.
split => [H|->]; last by [].
apply: (anti_symm (⊑)) => //; exact: fka_top_greatest.
Qed.

End PseudoTopKA.
