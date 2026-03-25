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

From kacc Require Import utils algebra.

(** Pre Kleene Algebras *)

Class Star T := star : T → T.
Global Hint Mode Star ! : typeclass_instances.
Global Instance: Params (@star) 1 := {}.

Record PreKAMixin T
    `{!Equiv T, Join T, Bottom T, Mul T, One T, Star T} := {
  mixin_pre_ka_right_dist : ∀ x y z : T, x ⋅ (y ⊔ z) ≡ x ⋅ y ⊔ x ⋅ z;
  mixin_pre_ka_left_dist : ∀ x y z : T, (y ⊔ z) ⋅ x ≡ y ⋅ x ⊔ z ⋅ x;
  mixin_pre_ka_left_absorb : LeftAbsorb (≡@{T}) ⊥ (⋅);
  mixin_pre_ka_right_empty : RightAbsorb (≡@{T}) ⊥ (⋅);
  mixin_pre_ka_star_unfold : ∀ x : T, star x ≡ 1 ⊔ x ⋅ star x;
  mixin_pre_ka_star_proper : Proper ((≡) ==> (≡)) (@star T _);
}.
Arguments PreKAMixin T {_ _ _ _ _ _}.

Structure pre_ka : Type := PreKA' {
  pre_ka_car :> Type;
  pre_ka_equiv : Equiv pre_ka_car;
  pre_ka_join : Join pre_ka_car;
  pre_ka_bottom : Bottom pre_ka_car;
  pre_ka_sqsubseteq : SqSubsetEq pre_ka_car;
  pre_ka_mul : Mul pre_ka_car;
  pre_ka_one : One pre_ka_car;
  pre_ka_star : Star pre_ka_car;
  pre_ka_setoid_mixin : Equivalence (≡@{pre_ka_car});
  pre_ka_monoid_mixin : MonoidMixin pre_ka_car;
  pre_ka_semi_lattice_mixin : SemiLatticeMixin pre_ka_car;
  pre_ka_mixin : PreKAMixin pre_ka_car;
}.
Global Arguments pre_ka_car : simpl never.
Global Arguments pre_ka_equiv : simpl never.
Global Arguments pre_ka_join : simpl never.
Global Arguments pre_ka_bottom : simpl never.
Global Arguments pre_ka_sqsubseteq : simpl never.
Global Arguments pre_ka_mul : simpl never.
Global Arguments pre_ka_one : simpl never.
Global Arguments pre_ka_star : simpl never.
Global Arguments pre_ka_setoid_mixin : simpl never.
Global Arguments pre_ka_monoid_mixin : simpl never.
Global Arguments pre_ka_semi_lattice_mixin : simpl never.
Global Arguments pre_ka_mixin : simpl never.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Star _) =>
  refine (@pre_ka_star _); shelve : typeclass_instances.
Coercion pre_ka_setoid (T : pre_ka) :=
  @Setoid T (≡) (pre_ka_setoid_mixin T).
Coercion pre_ka_monoid (T : pre_ka) :=
  @Monoid' T _ _ _ (pre_ka_setoid_mixin T) (pre_ka_monoid_mixin T).
Coercion pre_ka_semi_lattice (T : pre_ka) :=
  @SemiLattice' T _ _ _ _ (pre_ka_setoid_mixin T) (pre_ka_semi_lattice_mixin T).
Canonical Structure pre_ka_setoid.
Canonical Structure pre_ka_monoid.
Canonical Structure pre_ka_semi_lattice.

Section PreKATheory.

Variable T : pre_ka.

Implicit Types x y z : T.

Lemma pre_ka_right_dist : ∀ x y z : T, x ⋅ (y ⊔ z) ≡ x ⋅ y ⊔ x ⋅ z.
Proof. exact: (mixin_pre_ka_right_dist (pre_ka_mixin _)). Qed.

Lemma pre_ka_left_dist : ∀ x y z : T, (y ⊔ z) ⋅ x ≡ y ⋅ x ⊔ z ⋅ x.
Proof. exact: (mixin_pre_ka_left_dist (pre_ka_mixin _)). Qed.

Global Instance pre_ka_left_absorb : LeftAbsorb (≡@{T}) ⊥ (⋅).
Proof. exact: (mixin_pre_ka_left_absorb (pre_ka_mixin _)). Qed.

Global Instance pre_ka_right_absorb : RightAbsorb (≡@{T}) ⊥ (⋅).
Proof. exact: (mixin_pre_ka_right_empty (pre_ka_mixin _)). Qed.

Lemma pre_ka_star_unfold : ∀ x : T, star x ≡ 1 ⊔ x ⋅ star x.
Proof. exact: (mixin_pre_ka_star_unfold (pre_ka_mixin _)). Qed.

Global Instance pre_ka_star_proper : Proper ((≡) ==> (≡)) (@star T _).
Proof. exact: (mixin_pre_ka_star_proper (pre_ka_mixin _)). Qed.

Global Instance pre_ka_mul_mono : Proper ((⊑@{T}) ==> (⊑) ==> (⊑)) (⋅).
Proof.
move=> x1 x2 ex y1 y2 ey.
rewrite !sqsubseteq_iff in ex ey; rewrite -ex -ey.
rewrite pre_ka_left_dist !pre_ka_right_dist -!assoc.
exact: sqsubseteq_join_left.
Qed.

Lemma join_list_right_dist x ys : x ⋅ ⨆ ys ≡ ⨆ (map (λ y, x ⋅ y) ys).
Proof.
elim: ys => [|y ys IH]; rewrite /= ?right_absorb //.
by rewrite pre_ka_right_dist IH.
Qed.

Lemma join_list_left_dist xs y : ⨆ xs ⋅ y ≡ ⨆ (map (λ x, x ⋅ y) xs).
Proof.
elim: xs => [|x xs IH]; rewrite /= ?left_absorb //.
by rewrite pre_ka_left_dist IH.
Qed.

Lemma join_list_dist2 xs ys :
  ⨆ xs ⋅ ⨆ ys ≡ ⨆ (map (λ p : T * T, p.1 ⋅ p.2) (all_pairs xs ys)).
Proof.
rewrite join_list_left_dist; apply (anti_symm _).
- rewrite join_list_sqsubseteq=> _ /elem_of_list_fmap [x [] -> x_xs].
  rewrite join_list_right_dist join_list_sqsubseteq.
  move=> _ /elem_of_list_fmap [y [] -> y_ys].
  apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
  by exists (x, y); split => //; apply/elem_of_all_pairs; eauto.
- rewrite join_list_sqsubseteq => _ /elem_of_list_fmap [[x y] [] -> p_ps].
  case/elem_of_all_pairs: p_ps=> x_xs y_ys.
  transitivity (x ⋅ ⨆ ys).
  + rewrite join_list_right_dist.
    by apply sqsubseteq_join_list; apply/elem_of_list_fmap; eauto.
  + by apply sqsubseteq_join_list; apply/elem_of_list_fmap; eauto.
Qed.

Lemma pre_ka_one_star x : 1 ⊑ star x.
Proof.
rewrite pre_ka_star_unfold.
exact: sqsubseteq_join_left.
Qed.

Lemma pre_ka_mul_star x : x ⋅ star x ⊑ star x.
Proof.
rewrite {2}pre_ka_star_unfold.
exact: sqsubseteq_join_right.
Qed.

Lemma pre_ka_star_infl x : x ⊑ star x.
Proof.
rewrite -pre_ka_mul_star.
trans (x ⋅ 1); first by rewrite right_id.
by rewrite pre_ka_one_star.
Qed.

Lemma star_bottom : star (⊥ : T) ≡ 1.
Proof. by rewrite pre_ka_star_unfold left_absorb right_id. Qed.

Definition pre_ka_of_bool (b : bool) : T :=
  if b then 1 else ⊥.

Lemma pre_ka_of_bool_and b1 b2 :
  pre_ka_of_bool (b1 && b2) ≡
  pre_ka_of_bool b1 ⋅ pre_ka_of_bool b2.
Proof.
by case: b1 b2 => [] []; rewrite /= ?right_id // right_absorb.
Qed.

Lemma pre_ka_of_bool_or b1 b2 :
  pre_ka_of_bool (b1 || b2) ≡
  pre_ka_of_bool b1 ⊔ pre_ka_of_bool b2.
Proof.
by case: b1 b2 => [] []; rewrite /= ?idemp // ?right_id // left_id.
Qed.

End PreKATheory.

Arguments pre_ka_of_bool {T}.

Inductive ka_term (T : Type) : Type :=
  | Unit of T
  | ka_term_bottom : Bottom (ka_term T)
  | ka_term_join : Join (ka_term T)
  | ka_term_mul : Mul (ka_term T)
  | ka_term_star : Star (ka_term T).

Arguments Unit {T} _.
Arguments ka_term_bottom {T}.
Global Existing Instance ka_term_bottom.
Global Existing Instance ka_term_join.
Global Existing Instance ka_term_mul.
Global Existing Instance ka_term_star.

Global Instance ka_term_one `{!One T} : One (ka_term T) :=
  Unit 1.

Section KATermTheory.

Variable T : monoid.

Implicit Types x y z : T.
Implicit Types e : ka_term T.

Inductive ka_eq : Equiv (ka_term T) :=
  | ka_eq_refl : Reflexive ka_eq
  | ka_eq_sym : Symmetric ka_eq
  | ka_eq_trans : Transitive ka_eq

  | ka_mul_distr : ∀ x y : T, Unit (x ⋅ y) ≡ Unit x ⋅ Unit y

  | ka_unit_proper : Proper ((≡) ==> (≡)) (@Unit T)
  | ka_mul_proper : Proper ((≡) ==> (≡) ==> (≡)) (⋅)
  | ka_join_proper :  Proper ((≡) ==> (≡) ==> (≡)) (⊔)
  | ka_star_proper : Proper ((≡) ==> (≡)) star

  | ka_mul_assoc : Assoc (≡) (⋅)
  | ka_mul_left_id : LeftId (≡) 1 (⋅)
  | ka_mul_right_id : RightId (≡) 1 (⋅)

  | ka_join_assoc : Assoc (≡) (⊔)
  | ka_join_comm : Comm (≡) (⊔)
  | ka_join_left_id : LeftId (≡) ⊥ (⊔)
  | ka_join_idemp : IdemP (≡) (⊔)

  | ka_mul_left_absorb : LeftAbsorb (≡) ⊥ (⋅)
  | ka_mul_right_absorb : RightAbsorb (≡) ⊥ (⋅)

  | ka_mul_join_right e1 e2 e3 : e1 ⋅ (e2 ⊔ e3) ≡ e1 ⋅ e2 ⊔ e1 ⋅ e3
  | ka_mul_join_left e1 e2 e3 : (e1 ⊔ e2) ⋅ e3 ≡ e1 ⋅ e3 ⊔ e2 ⋅ e3

  | ka_star_unfold t : star t ≡ 1 ⊔ (t ⋅ (star t)).

Global Existing Instance ka_eq.
Global Existing Instance ka_unit_proper.

Global Instance ka_eq_equivalence : Equivalence (≡@{ka_term T}).
Proof.
constructor.
- apply ka_eq_refl.
- apply ka_eq_sym.
- apply ka_eq_trans.
Defined.

Canonical Structure ka_term_setoid :=
  @Setoid (ka_term T) _ ka_eq_equivalence.

Lemma ka_term_monoid_mixin : MonoidMixin (ka_term T).
Proof.
constructor.
- apply ka_mul_assoc.
- apply ka_mul_left_id.
- apply ka_mul_right_id.
- apply ka_mul_proper.
Qed.

Global Instance ka_term_sqsubseteq : SqSubsetEq (ka_term T) :=
  default_sqsubseteq.

Lemma ka_term_semi_lattice_mixin : SemiLatticeMixin (ka_term T).
Proof.
apply default_semi_lattice_mixin.
- apply ka_join_assoc.
- apply ka_join_comm.
- apply ka_join_left_id.
- apply ka_join_idemp.
- apply ka_join_proper.
Qed.

Lemma ka_term_pre_ka_mixin : PreKAMixin (ka_term T).
Proof.
constructor.
- by move=> *; rewrite ka_mul_join_right.
- by move=> *; rewrite ka_mul_join_left.
- apply ka_mul_left_absorb.
- apply ka_mul_right_absorb.
- apply ka_star_unfold.
- apply ka_star_proper.
Qed.

Canonical Structure ka_term_monoid :=
  @Monoid' (ka_term T) _ _ _ _
    ka_term_monoid_mixin.

Canonical Structure ka_term_semi_lattice :=
  @SemiLattice' (ka_term T) _ _ _ _ _
    ka_term_semi_lattice_mixin.

Canonical Structure ka_term_pre_ka :=
  @PreKA' (ka_term T) _ _ _ _ _ _ _ _
    ka_term_monoid_mixin
    ka_term_semi_lattice_mixin
    ka_term_pre_ka_mixin.

Global Instance pre_ka_unit_monoid_morphism : MonoidMorphism (@Unit T).
Proof.
constructor => //=.
- apply _.
- by move=> ??; rewrite ka_mul_distr.
Qed.

Lemma ka_join_right_id (e : ka_term T) : e ⊔ ⊥ ≡ e.
Proof.
  by rewrite ka_join_comm; constructor.
Qed.

End KATermTheory.

Canonical Structure bool_setoid :=
  eq_setoid bool.

Global Instance bool_leibniz_equiv : LeibnizEquiv bool.
Proof. move=> ??; apply. Qed.

Global Instance bool_one : One bool := true.
Global Instance bool_mul : Mul bool := andb.
Lemma bool_monoid_mixin : MonoidMixin bool.
Proof.
split.
- by case=> [] [] [].
- by case.
- by case.
- solve_proper.
Qed.

Canonical bool_monoid :=
  @Monoid' bool _ _ _
    _
    bool_monoid_mixin.

Global Instance bool_bottom : Bottom bool := false.
Global Instance bool_join : Join bool := orb.
Global Instance bool_sqsubseteq : SqSubsetEq bool :=
  default_sqsubseteq.
Lemma bool_semi_lattice_mixin : SemiLatticeMixin bool.
Proof.
split.
- by case=> [] [] [].
- by case=> [] [].
- by case=> [].
- by case.
- solve_proper.
- exact: default_sqsubseteq_eq.
Qed.

Canonical bool_semi_lattice :=
  @SemiLattice' bool _ _ _ _
    _
    bool_semi_lattice_mixin.

Global Instance bool_star : Star bool := λ _, 1.
Lemma bool_pre_ka_mixin : PreKAMixin bool.
Proof.
split.
- by case=> [] [] [].
- by case=> [] [] [].
- by case.
- by case.
- by case.
- solve_proper.
Qed.

Canonical bool_pre_ka :=
  @PreKA' bool _ _ _ _ _ _ _
    _
    bool_monoid_mixin
    bool_semi_lattice_mixin
    bool_pre_ka_mixin.

Variant count :=
| CountEmpty  : Bottom count
| CountFinite : One count
| CountStarred.

Global Instance count_eq_dec : EqDecision count.
Proof.
  unfold EqDecision.
  move=> x y; rewrite /Decision.
  decide equality.
Qed.

Global Existing Instance CountEmpty.
Global Existing Instance CountFinite.

Global Instance count_mul : Mul count := λ c1 c2,
  match c1, c2 with
  | CountEmpty, _ => CountEmpty
  | _, CountEmpty => CountEmpty
  | CountFinite, CountFinite => CountFinite
  | CountStarred, _ => CountStarred
  | _, CountStarred => CountStarred
  end.

Canonical Structure count_setoid :=
  @eq_setoid count.

Global Instance count_leibniz : LeibnizEquiv count.
Proof.
  by move=> ??.
Qed.

Lemma count_monoid_mixin : MonoidMixin count.
Proof.
constructor => //=.
- by case=> [] [] [].
- by case.
- by case.
- solve_proper.
Qed.

Canonical Structure count_monoid :=
  @Monoid' count _ _ _ _
           count_monoid_mixin.

Global Instance count_join : Join count := λ c1 c2,
  match c1, c2 with
  | CountEmpty, c => c
  | c, CountEmpty => c
  | CountFinite, c => c
  | c, CountFinite => c
  | CountStarred, CountStarred => CountStarred
  end.

Global Instance count_sqsubseteq : SqSubsetEq count :=
  default_sqsubseteq.

Lemma count_semi_lattice_mixin : SemiLatticeMixin count.
Proof.
apply default_semi_lattice_mixin; last solve_proper.
- by case=> [] [] [].
- by case=> [] [].
- by case=> [].
- by case=> [].
Qed.

Canonical Structure count_semi_lattice :=
  @SemiLattice' count _ _ _ _ _
                count_semi_lattice_mixin.

Lemma count_join_empty (c1 c2 : count) : c1 ⊔ c2 = ⊥ ↔ c1 = ⊥ ∧ c2 = ⊥.
Proof.
split=> [|[-> ->]] //=.
case: c1 c2 => [] [] //; eauto.
Qed.

Global Instance count_star : Star count := λ c,
  match c with
  | CountEmpty => CountFinite
  | _ => CountStarred
  end.

Lemma count_pre_ka_mixin : PreKAMixin count.
Proof.
constructor; try solve_proper.
- by case=> [] [] [].
- by case=> [] [] [].
- by case.
- by case.
- by case.
Qed.

Canonical Structure count_pre_ka :=
  @PreKA' count _ _ _ _ _ _ _ _
          count_monoid_mixin
          count_semi_lattice_mixin
          count_pre_ka_mixin.

Lemma count_mul_empty (c1 c2 : count) : c1 ⋅ c2 = ⊥ ↔ c1 = ⊥ ∨ c2 = ⊥.
Proof.
split=> [|[->|->]] //=; rewrite ?right_absorb //.
case: c1 c2 => [] [] //=; eauto.
Qed.

Lemma count_mul_one (c1 c2 : count) :
  c1 ⋅ c2 ⊑ 1 ↔ (c1 = ⊥ ∨ c2 = ⊥) ∨ c1 ⊑ 1 ∧ c2 ⊑ 1.
Proof.
split; last first.
  case=> [H|[-> -> //]]; rewrite sqsubseteq_iff.
  by case: H=> ->; rewrite ?left_absorb ?right_absorb.
rewrite !sqsubseteq_iff.
by case: c1 c2 => [] [] //=; eauto.
Qed.

Lemma count_star_one (c : count) : star c ⊑ 1 ↔ c ≡ ⊥.
Proof.
split=> [|-> //].
by rewrite sqsubseteq_iff; case: c=> //=.
Qed.

Class PreKAMorphism (T S : pre_ka) (f : T → S) := {
  pre_ka_morphism_proper :: Proper ((≡) ==> (≡)) f;
  pre_ka_morphism_one : f 1 ≡ 1;
  pre_ka_morphism_mul : ∀ x y, f (x ⋅ y) ≡ f x ⋅ f y;
  pre_ka_morphism_bottom : f ⊥ ≡ ⊥;
  pre_ka_morphism_join : ∀ x y, f (x ⊔ y) ≡ f x ⊔ f y;
  pre_ka_morphism_star : ∀ x, f (star x) ≡ star (f x);
}.

Section PreKAMorphismTheory.

Variables (T S : pre_ka) (f : T → S).

Context `{H : PreKAMorphism T S f}.

Global Instance pre_ka_morphism_monoid_morphism :
  MonoidMorphism f.
Proof. by constructor; case: (H). Qed.

Global Instance pre_ka_morphism_semi_lattice_morphism :
  SemiLatticeMorphism f.
Proof. by constructor; case: (H). Qed.

End PreKAMorphismTheory.

Global Instance compose_pre_ka_morphism (T S R : pre_ka)
  (f : T → S) (g : S → R) :
  PreKAMorphism f → PreKAMorphism g →
  PreKAMorphism (g ∘ f).
Proof.
move=> ??; constructor.
- solve_proper.
- by rewrite /= !pre_ka_morphism_one.
- by move=> ??; rewrite /= !pre_ka_morphism_mul.
- by rewrite /= !pre_ka_morphism_bottom.
- by move=> ??; rewrite /= !pre_ka_morphism_join.
- by move=> ?; rewrite /= !pre_ka_morphism_star.
Qed.

Fixpoint ka_term_elim (T : Type) (S : pre_ka) (f : T → S) (e : ka_term T) : S :=
  match e with
  | Unit x => f x
  | ka_term_bottom => ⊥
  | ka_term_join e1 e2 => ka_term_elim f e1 ⊔ ka_term_elim f e2
  | ka_term_mul e1 e2 => ka_term_elim f e1 ⋅ ka_term_elim f e2
  | ka_term_star e => star (ka_term_elim f e)
  end.

Section KATermElim.

Variables (T : monoid) (S : pre_ka) (f : T → S).
Context `{MonoidMorphism T S f}.

Global Instance ka_term_elim_morphism :
  PreKAMorphism (ka_term_elim f).
Proof.
constructor=> //=.
- move=> e1 e2; elim: e1 e2 / => //=.
  + by move=> e1 e2 e3 _ ->.
  + by move=> ??; rewrite monoid_morphism_mul.
  + by move=> ?? ->.
  + by move=> e11 e12 _ IH1 e21 e22 _ IH2; rewrite IH1 IH2.
  + by move=> e11 e12 _ IH1 e21 e22 _ IH2; rewrite IH1 IH2.
  + by move=> e1 e2 _ ->.
  + by move=> ???; rewrite assoc.
  + by move=> ?; rewrite monoid_morphism_one left_id.
  + by move=> ?; rewrite monoid_morphism_one right_id.
  + by move=> ???; rewrite assoc.
  + by move=> ??; rewrite comm.
  + by move=> ?; rewrite left_id.
  + by move=> ?; rewrite semi_lattice_idemp.
  + by move=> ?; rewrite left_absorb.
  + by move=> ?; rewrite right_absorb.
  + by move=> ???; rewrite pre_ka_right_dist.
  + by move=> ???; rewrite pre_ka_left_dist.
  + by move=> ?; rewrite monoid_morphism_one {1}pre_ka_star_unfold.
- by rewrite /= monoid_morphism_one.
Qed.

End KATermElim.

Section KATermUP.

Variables (T : monoid) (S : pre_ka) (g h : ka_term T → S).
Context `{!PreKAMorphism g, !PreKAMorphism h}.

Lemma ka_term_ext :
  (∀ x, g (Unit x) ≡ h (Unit x)) →
  ∀ e, g e ≡ h e.
Proof.
move=> Hunit; elim=> /=.
- exact: Hunit.
- by rewrite !pre_ka_morphism_bottom.
- by move=> e1 IH1 e2 IH2; rewrite !pre_ka_morphism_join IH1 IH2.
- by move=> e1 IH1 e2 IH2; rewrite !pre_ka_morphism_mul IH1 IH2.
- by move=> e IH; rewrite !pre_ka_morphism_star IH.
Qed.

End KATermUP.

Definition ka_term_map {T} {S : monoid} (f : T → S) : ka_term T → ka_term S :=
  ka_term_elim (Unit ∘ f).

Section KATermMap.

Context {T} {S} `{MonoidMorphism T S f}.

Global Instance ka_term_map_morphism :
  PreKAMorphism (ka_term_map f).
Proof. apply _. Qed.

End KATermMap.

Section CountTerm.

Context {T : monoid}.

Definition count_term : ka_term T → count :=
  ka_term_elim (λ x, 1).

Global Instance count_term_morphism : PreKAMorphism count_term.
Proof. apply _. Qed.

(* Definition count_leq (c1 c2 : count) : bool :=
  match c1, c2 with
  | CountEmpty, _ => true
  | _, CountEmpty => false
  | CountFinite, CountFinite => true
  | CountFinite, CountStarred => true
  | CountStarred, _ => false
  end. *)

Lemma count_emptyP e : count_term e = ⊥ ↔ e ≡ ⊥.
Proof.
split => [|->] //=; elim: e=> //=.
- move=> e1 IH1 e2 IH2.
  rewrite semi_lattice_morphism_join count_join_empty.
  rewrite -[ka_term_join e1 e2]/(e1 ⊔ e2).
  by case=> /IH1 -> /IH2 ->; rewrite idemp.
- move=> e1 IH1 e2 IH2; rewrite -[ka_term_mul e1 e2]/(e1 ⋅ e2).
  rewrite monoid_morphism_mul count_mul_empty.
  by case=> [/IH1|/IH2] ->; rewrite ?left_absorb // right_absorb.
- by move=> e _; rewrite pre_ka_morphism_star; case: (count_term e).
Qed.

Lemma count_finiteP e : count_term e ⊑ 1 ↔ ∃ xs, e ≡ ⨆ (map Unit xs).
Proof.
split=> [|[xs ->]]; last first.
  rewrite semi_lattice_morphism_join_list map_map join_list_sqsubseteq.
  by move=> c /elem_of_list_fmap [x [] ->].
elim: e => //=.
- by move=> x _; exists [x]; rewrite /= right_id.
- by move=> _; exists [].
- move=> e1 IH1 e2 IH2; rewrite semi_lattice_morphism_join.
  rewrite join_sqsubseteq; case => /IH1 [xs1 ex1] /IH2 [xs2 ex2].
  by exists (xs1 ++ xs2); rewrite map_app join_list_app -ex1 -ex2.
- move=> e1 IH1 e2 IH2; rewrite monoid_morphism_mul -/(e1 ⋅ e2).
  case/count_mul_one=> [H|[/IH1 [xs1 exs1] /IH2 [xs2 exs2]]].
    exists [].
    by case: H=> /count_emptyP ->; rewrite ?left_absorb ?right_absorb.
  exists (map (λ p, p.1 ⋅ p.2) (all_pairs xs1 xs2)).
  rewrite exs1 exs2 join_list_dist2 all_pairs_map !map_map /=.
  have -> // : map (λ p, Unit p.1 ⋅ Unit p.2) (all_pairs xs1 xs2)
               ≡ map (λ p, Unit (p.1 ⋅ p.2)) (all_pairs xs1 xs2).
  apply: list_fmap_proper => // x y [-> ->].
  by rewrite ka_mul_distr.
- move=> e IH; rewrite pre_ka_morphism_star=> /count_star_one /count_emptyP eE.
  by exists [1]; rewrite eE [X in X ≡ _]star_bottom /= right_id.
Qed.

End CountTerm.

Section HasOne.

Class IsOne (T : monoid) := {
  is_one : T → bool;
  #[global] is_one_monoid_morphism :: MonoidMorphism is_one;
  is_one_eq : ∀ x, is_one x = true ↔ x ≡ 1;
}.

Context `{IsOne T}.

Definition has_one : ka_term T → bool := ka_term_elim is_one.

Global Instance has_one_morphism : PreKAMorphism has_one.
Proof. apply _. Qed.

Lemma has_oneP e : has_one e = true ↔ 1 ⊑ e.
Proof.
split; last first.
  move=> e_gt1; have: 1 ⊑ has_one e.
    rewrite -[1](@monoid_morphism_one _ _ (@is_one T _)).
    (* FIXME: Why do we need to unfold this in two steps? *)
    by rewrite -[is_one 1]/(has_one (Unit 1)) -[Unit 1]/1 e_gt1.
  by move=> /sqsubseteq_iff/leibniz_equiv_iff; case: has_one.
elim: e => //.
- by move=> x /is_one_eq ->.
- by move=> e1 IH1 e2 IH2; case/orb_true_iff=> [/IH1 e1_gt1|/IH2 e2_gt1];
  apply: sqsubseteq_join; eauto.
- move=> e1 IH1 e2 IH2; case/andb_true_iff=> /IH1 e1_gt1 /IH2 e2_gt1.
  by rewrite -{1}[1](left_id 1) {1}e1_gt1 e2_gt1.
- move=> e _ _; exact: pre_ka_one_star.
Qed.

End HasOne.

Section ListIsOne.

Context {T : setoid} `{!LeibnizEquiv T}.

Definition list_is_one (xs : list T) : bool :=
  match xs with [] => true | _ => false end.

Global Instance list_is_one_morphism : MonoidMorphism list_is_one.
Proof.
split.
- by move=> ?? /leibniz_equiv_iff ->.
- by [].
- by case=> [|x xs] [|y ys].
Qed.

Global Program Instance list_is_one_instance : IsOne (list_monoid T) := {|
  is_one := list_is_one;
|}.
Next Obligation.
by case=> [|x xs] /=; split => // /leibniz_equiv_iff.
Qed.

End ListIsOne.

Section ProdIsOne.

Context {T S : monoid} `{!IsOne T, !IsOne S}.

Definition prod_is_one (p : T * S) : bool :=
  is_one p.1 && is_one p.2.

Global Instance prod_is_one_morphism : MonoidMorphism prod_is_one.
Proof.
split.
- move=> [a1 a2] [b1 b2] [/= e1 e2].
  by rewrite /prod_is_one /= e1 e2.
- by rewrite /prod_is_one /= !monoid_morphism_one.
- move=> [x1 x2] [y1 y2]; rewrite /prod_is_one /=.
  rewrite !monoid_morphism_mul /=.
  by case: (is_one x1); case: (is_one x2); case: (is_one y1); case: (is_one y2).
Qed.

Global Program Instance prod_is_one_instance : IsOne (prod_monoid T S) := {|
  is_one := prod_is_one;
|}.
Next Obligation.
move=> [x y]; rewrite /prod_is_one /=.
split.
- move=> /andb_true_iff [/is_one_eq ex /is_one_eq ey]; by split.
- case=> [/= ex ey]; apply/andb_true_iff; split; apply/is_one_eq => //.
Qed.

End ProdIsOne.

Section PseudoTop.

Context `{!MonoidGen G T, !EqDecision G, !Finite G}.

Definition pseudo_top : ka_term T :=
  star (⨆ (map (λ g, Unit (generator_interp g)) (enum G))).

Lemma pseudo_top_absorb x : Unit x ⋅ pseudo_top ⊑ pseudo_top.
Proof.
case: (generate x) => xs -> {x}; elim: xs=> [|x xs IH] //=.
  by rewrite left_id.
rewrite monoid_morphism_mul -assoc IH /pseudo_top.
set f := λ x', Unit (generator_interp x').
have /sqsubseteq_join_list x_gen: f x ∈ map f (enum G).
  apply/elem_of_list_fmap; exists x; split => //.
  exact: elem_of_enum.
rewrite /f in x_gen; rewrite x_gen; exact: pre_ka_mul_star.
Qed.

(* Theorem 9 *)

Lemma pseudo_top_finite e :
  count_term e ⊑ 1 →
  e ⋅ pseudo_top ⊑ pseudo_top.
Proof.
case/count_finiteP=> {e} xs ->.
rewrite join_list_left_dist map_map.
apply/join_list_sqsubseteq=> _ /elem_of_list_fmap [x [] -> x_xs].
exact: pseudo_top_absorb.
Qed.

End PseudoTop.

Arguments pseudo_top {G T _ _ _}.
