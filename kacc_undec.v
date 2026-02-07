Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
Require Import Undecidability.MinskyMachines.MM2.
From stdpp Require Import base list finite gmap mapset.
(* From Coq Require Import Lia. *)
From Stdlib Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma elem_of_concat {T} (x : T) xss :
  x ∈ concat xss ↔ ∃ xs, xs ∈ xss ∧ x ∈ xs.
Proof.
rewrite elem_of_list_In in_concat.
split=> [[xs []]|[xs []]].
- by rewrite -!elem_of_list_In; eauto.
- by rewrite !elem_of_list_In; eauto.
Qed.

Section FiniteGMap.

Context `{!EqDecision K, !Countable K, !Finite K}.
Context `{!EqDecision V, !Countable V, !Finite V}.

Implicit Types (k : K) (ks : list K) (v : V).
Implicit Types (m : gmap K V) (ms : list (gmap K V)).

Definition add_bindings1 k m :=
  m :: map (λ v, <[k := v]> m) (enum V).

Definition add_bindings k ms :=
  flat_map (add_bindings1 k) ms.

Definition gmap_enum_on ks :=
  foldr add_bindings [∅] ks.

Definition gmap_enum : list (gmap K V) :=
  gmap_enum_on (enum K).

Lemma elem_of_add_bindings1_dom k m :
  k ∉ dom m →
  (∀ m', m' ∈ add_bindings1 k m ↔ m = delete k m').
Proof.
move=> k_m m'; rewrite /add_bindings1 elem_of_cons elem_of_list_fmap.
split=> [[-> {m'}|[v [] -> _]]|m_m'].
- apply: map_subseteq_size_eq.
  + apply/map_subseteq_spec => k' v m_k'.
    rewrite lookup_delete_ne // => ne; move/not_elem_of_dom: k_m.
    by rewrite ne m_k'.
  + rewrite map_size_delete_None //; exact/not_elem_of_dom.
- by rewrite delete_insert //; apply/not_elem_of_dom.
- destruct (m' !! k) as [v|] eqn:m'_k.
  + right; exists v; split; last exact: elem_of_enum.
    by rewrite m_m' insert_delete.
  + by left; rewrite {}m_m' delete_notin.
Qed.

Lemma subseteq_union_difference (X Y Z : gset K) :
  X ⊆ Y ∪ Z ↔ X ∖ Y ⊆ Z.
Proof.
split=> H x.
- case/elem_of_difference; set_solver.
- move=> x_X; apply/elem_of_union; case: (decide (x ∈ Y))=> x_Y.
  + set_solver.
  + by right; apply: H; apply/elem_of_difference; split.
Qed.

Lemma elem_of_add_bindings k ms ks :
  k ∉ ks →
  (∀ m, m ∈ ms ↔ dom m ⊆ list_to_set ks) →
  (∀ m, m ∈ add_bindings k ms ↔ dom m ⊆ {[k]} ∪ list_to_set ks).
Proof.
move=> k_ks ms_ks m; rewrite /add_bindings flat_map_concat_map.
rewrite subseteq_union_difference -dom_delete_L -ms_ks elem_of_concat.
split.
- case=> _ [] /elem_of_list_fmap [] m' [] -> /ms_ks dom_m'.
  have k_m': k ∉ dom m' by set_solver.
  move=> /(elem_of_add_bindings1_dom k_m') <-; exact/ms_ks.
- move=> /ms_ks dom_m; exists (add_bindings1 k (delete k m)).
  have k_m: k ∉ dom (delete k m).
    rewrite dom_delete elem_of_difference elem_of_singleton.
    by tauto.
  split; last exact/(elem_of_add_bindings1_dom k_m).
  apply/elem_of_list_fmap; eexists _; split; eauto.
  exact/ms_ks.
Qed.

Lemma elem_of_gmap_enum_on m ks :
  NoDup ks →
  m ∈ gmap_enum_on ks ↔ dom m ⊆ list_to_set ks.
Proof.
move=> nd; elim: ks / nd => [|k ks k_ks _ IH] /= in m *.
- rewrite elem_of_list_singleton.
  split=> [->|m_0]; first by rewrite dom_empty.
  apply: dom_empty_inv_L; exact/equiv_empty_L.
- move: m; exact: elem_of_add_bindings.
Qed.

Lemma elem_of_gmap_enum m : m ∈ gmap_enum.
Proof.
have : dom m ⊆ list_to_set (enum K).
  move=> k _; rewrite elem_of_list_to_set; exact: elem_of_enum.
by rewrite -(elem_of_gmap_enum_on _ (NoDup_enum K)).
Qed.

Global Program Instance gmap_finite : Finite (gmap K V) := {|
  (* FIXME: This removal step should not be needed because gmap_enum is
     duplicate free. *)
  enum := remove_dups gmap_enum;
|}.

Next Obligation. exact: NoDup_remove_dups. Qed.
Next Obligation.
move=> m; rewrite elem_of_remove_dups; exact: elem_of_gmap_enum.
Qed.

End FiniteGMap.

Section FiniteGSet.

Context `{!EqDecision T, !Countable T, !Finite T}.

Implicit Types (x : T) (X : gset T).

Global Program Instance gset_finite : Finite (gset T) := {|
  enum := map Mapset (enum (gmap T unit));
|}.

Next Obligation.
apply: NoDup_fmap_2; last exact: NoDup_enum.
by move=> ?? [?].
Qed.

Next Obligation.
case=> X; apply/elem_of_list_fmap; exists X; split => //.
exact: elem_of_enum.
Qed.

End FiniteGSet.

Section AllPairs.

Variables T S : Type.

Implicit Types (x : T) (xs : list T).
Implicit Types (y : S) (ys : list S).

Definition all_pairs xs ys :=
  concat (map (λ x, map (pair x) ys) xs).

Lemma elem_of_all_pairs p xs ys :
  p ∈ all_pairs xs ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys.
Proof.
rewrite /all_pairs elem_of_concat; split.
- case=> ps [] /elem_of_list_fmap [] x [] -> x_xs.
  by case/elem_of_list_fmap=> y [] ->; eauto.
- case: p=> [x y] [x_xs y_ys]; exists (map (pair x) ys); split.
  + by apply/elem_of_list_fmap; exists x; eauto.
  + by apply/elem_of_list_fmap; exists y; eauto.
Qed.

End AllPairs.

Section AllPairsMap.

Variables T1 T2 S1 S2 : Type.
Implicit Types (x : T1) (xs : list T1).
Implicit Types (y : S1) (ys : list S1).
Implicit Types (f : T1 → T2) (g : S1 → S2).

Lemma all_pairs_map f g xs ys :
  all_pairs (map f xs) (map g ys) =
  map (λ p, (f p.1, g p.2)) (all_pairs xs ys).
Proof.
rewrite /all_pairs; elim: xs => //= x xs ->.
by rewrite map_app !map_map.
Qed.

End AllPairsMap.

Declare Scope ka_scope.
Delimit Scope ka_scope with ka.
Open Scope ka_scope.

(** Setoids *)

Structure setoid := Setoid {
  setoid_car :> Type;
  setoid_equiv : Equiv setoid_car;
  setoid_equiv_equivalence : Equivalence (@equiv setoid_car _);
}.
Global Arguments setoid_car : simpl never.
Global Arguments setoid_equiv : simpl never.
Global Arguments setoid_equiv_equivalence : simpl never.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Equiv _) =>
  refine (@setoid_equiv _); shelve : typeclass_instances.

Section SetoidTheory.

Variable T : setoid.

Global Existing Instance setoid_equiv_equivalence.

End SetoidTheory.

Section EqSetoid.

Variable T : Type.

Definition eq_setoid :=
  @Setoid T eq eq_equivalence.

End EqSetoid.

Section ListSetoid.

Variable T : setoid.

Canonical Structure list_setoid :=
  @Setoid (list T) (≡) (list_equivalence _).

End ListSetoid.

Global Instance Proper_map' {A B : setoid} :
  Proper (((≡) ==> (≡)) ==> (≡) ==> (≡)) (@map A B).
Proof.
move=> f g efg xs ys; elim: xs ys / => //= x y xs ys exy _ ->.
by rewrite (efg _ _ exy).
Qed.

Section ProductSetoid.

Variables T S : setoid.

Canonical Structure prod_setoid :=
  @Setoid (T * S) (≡) (prod_equivalence _ _).

End ProductSetoid.

Section GSetSetoid.

Context `{Countable T}.

Canonical Structure gset_setoid :=
  @Setoid (gset T) (≡) _.

End GSetSetoid.

(** Monoids *)

Class Mul T := mul : T -> T -> T.
Global Hint Mode Mul ! : typeclass_instances.
Global Instance: Params (@mul) 2 := {}.
Infix "⋅" := mul (at level 40, left associativity) : ka_scope.
Notation "(⋅)" := mul (only parsing) : ka_scope.

Class One T := one : T.
Global Hint Mode One ! : typeclass_instances.
Notation "1" := one : ka_scope.

Record MonoidMixin T `{!Equiv T, Mul T, One T} := {
  mixin_monoid_assoc : Assoc (≡) ((⋅) : T → T → T);
  mixin_monoid_left_id : LeftId (≡) (1 : T) (⋅);
  mixin_monoid_right_id : RightId (≡) (1 : T) (⋅);
  mixin_monoid_proper : Proper ((≡) ==> (≡) ==> (≡)) (@mul T _);
}.
Arguments MonoidMixin T {_ _ _}.

Structure monoid : Type := Monoid' {
  monoid_car :> Type;
  monoid_equiv : Equiv monoid_car;
  monoid_mul : Mul monoid_car;
  monoid_one : One monoid_car;
  monoid_setoid_mixin : Equivalence (@equiv monoid_car _);
  monoid_mixin : MonoidMixin monoid_car;
}.

Global Arguments monoid_car : simpl never.
Global Arguments monoid_equiv : simpl never.
Global Arguments monoid_mul : simpl never.
Global Arguments monoid_one : simpl never.
Global Arguments monoid_setoid_mixin : simpl never.
Global Arguments monoid_mixin : simpl never.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Mul _) =>
  refine (@monoid_mul _); shelve : typeclass_instances.
Global Hint Extern 0 (One _) =>
  refine (@monoid_one _); shelve : typeclass_instances.
Coercion monoid_setoid (T : monoid) :=
  @Setoid T (≡) (monoid_setoid_mixin T).
Canonical Structure monoid_setoid.

Section MonoidTheory.

Variable T : monoid.

Implicit Types x y z : T.

Global Instance monoid_assoc : Assoc (≡) ((⋅) : T → T → T).
Proof. exact: (mixin_monoid_assoc (monoid_mixin T)). Defined.

Global Instance monoid_left_id : LeftId (≡) (1 : T) (⋅).
Proof. exact: (mixin_monoid_left_id (monoid_mixin T)). Defined.

Global Instance monoid_right_id : RightId (≡) (1 : T) (⋅).
Proof. exact: (mixin_monoid_right_id (monoid_mixin T)). Defined.

Global Instance monoid_proper : Proper ((≡) ==> (≡) ==> (≡)) (@mul T _).
Proof. exact: (mixin_monoid_proper (monoid_mixin T)). Defined.

Definition power x n : T :=
  Nat.iter n (mul x) 1.

Local Notation "x ^ n" := (power x n) : ka_scope.

Global Instance power_proper : Proper ((≡) ==> (=) ==> (≡)) power.
Proof.
move=> x y e n _ <-.
by elim: n => // n IH /=; rewrite IH e.
Qed.

Lemma power_add x n m : x ^ (n + m) ≡ (x ^ n) ⋅ (x ^ m).
Proof.
by elim: n => [|n IH] /=; rewrite ?left_id // IH assoc.
Qed.

Lemma power_one x : x ^ 1 ≡ x.
Proof. by rewrite /= right_id. Qed.

Definition mul_list : list T → T := foldr (⋅) 1.

Notation "∏" := mul_list.

Lemma mul_list_one xs :
  (∀ x, x ∈ xs → x ≡ 1) →
  ∏ xs ≡ 1.
Proof.
elim: xs => //= x xs IH xs_1.
rewrite (xs_1 x) ?elem_of_cons ?left_id; eauto.
rewrite IH // => x' x'_xs; apply: xs_1.
by rewrite elem_of_cons; eauto.
Qed.

End MonoidTheory.

Notation "x ^ n" := (power x n) : ka_scope.
Notation "∏" := mul_list : ka_scope.

Class MonoidMorphism (T S : monoid) (f : T → S) := {
  monoid_morphism_proper :: Proper ((≡) ==> (≡)) f;
  monoid_morphism_one : f 1 ≡ 1;
  monoid_morphism_mul : ∀ x y, f (x ⋅ y) ≡ f x ⋅ f y;
}.

Lemma monoid_morphism_mul_list `{MonoidMorphism T1 T2 f} (xs : list T1) :
  f (∏ xs) ≡ ∏ (map f xs).
Proof.
elim: xs => //= [|x xs IH].
- by rewrite monoid_morphism_one.
- by rewrite monoid_morphism_mul IH.
Qed.

Global Instance one_monoid_morphism (T S : monoid) :
  MonoidMorphism (λ x : T, @one S _).
Proof.
split => //.
- solve_proper.
- by move=> _ _; rewrite left_id.
Qed.

Global Instance id_monoid_morphism (T : monoid) : MonoidMorphism (@id T).
Proof. split => //; solve_proper. Qed.

Global Instance compose_monoid_morphism (T S R : monoid)
  (f : T → S) (g : S → R) :
  MonoidMorphism f → MonoidMorphism g →
  MonoidMorphism (g ∘ f).
Proof.
move=> ??; split.
- solve_proper.
- by rewrite /= !monoid_morphism_one.
- by move=> ??; rewrite /= !monoid_morphism_mul.
Qed.

Class FinGenMonoid (T : monoid) := {
  generators : list T;
  generate x : {l : list T | x ≡ ∏ l ∧ l ⊆ generators};
}.

Section ListMonoid.

Variable T : setoid.

Global Instance list_one : One (list T) := [].
Global Instance list_mul : Mul (list T) := @app T.

Lemma list_monoid_mixin : MonoidMixin (list T).
Proof.
constructor.
- move=> l1 l2 l3 /=; by rewrite assoc.
- move=> l; reflexivity.
- by move=> l; rewrite right_id.
- apply _.
Qed.

Canonical Structure list_monoid :=
  @Monoid' (list T) _ _ _
           (list_equivalence _)
           list_monoid_mixin.

End ListMonoid.

Section ListFinGen.

Context {T : setoid} `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Global Program Instance list_fin_gen : FinGenMonoid (list_monoid T) := {|
  generators := map (λ x, [x]) (enum T);
|}.
Next Obligation.
move=> l; exists (map (λ x, [x]) l); split.
- apply leibniz_equiv_iff; by elim: l => //= x l <-.
- move=> l'; rewrite elem_of_list_fmap; case=> y [] -> y_l.
  rewrite elem_of_list_fmap; exists y; split => //.
  exact: elem_of_enum.
Qed.

End ListFinGen.

Global Instance mul_list_monoid_morphism (T : monoid) :
  MonoidMorphism (@mul_list T).
Proof.
split => //.
- by move=> l1 l2; elim: l1 l2 / => //= x1 x2 l1 l2 -> _ ->.
- move=> l1 l2; elim: l1=> //= [|x l1 IH].
  + by rewrite [1 ⋅ _]left_id.
  + by rewrite IH assoc.
Qed.

Section ProdMonoid.

Variables T S : monoid.

Global Instance prod_one : One (T * S) := (1, 1).
Global Instance prod_mul : Mul (T * S) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).

Lemma prod_monoid_mixin : MonoidMixin (T * S).
Proof.
constructor.
- by case=> [x1 x2] [y1 y2] [z1 z2]; split; rewrite /= assoc.
- by case=> [x1 x2]; split; rewrite /= left_id.
- by case=> [x1 x2]; split; rewrite /= right_id.
- case=> [x1 x2] [x1' x2'] [/= ex1 ex2].
  case=> [y1 y2] [y1' y2'] [/= ey1 ey2].
  by split; rewrite /= ?ex1 ?ey1 // ex2 ey2.
Qed.

Canonical Structure prod_monoid :=
  @Monoid' (T * S) _ _ _
           (prod_equivalence _ _)
           prod_monoid_mixin.

Global Instance fst_monoid_morphism : MonoidMorphism (@fst T S).
Proof. split => //=. solve_proper. Qed.

Global Instance snd_monoid_morphism : MonoidMorphism (@snd T S).
Proof. split => //=. solve_proper. Qed.

Definition prod_inj1 : T → T * S := λ x, (x, 1).
Definition prod_inj2 : S → T * S := λ x, (1, x).

Global Instance prod_inj1_monoid_morphism :
  MonoidMorphism prod_inj1.
Proof.
by split => //= x y; split => //=; rewrite left_id.
Qed.

Global Instance prod_inj2_monoid_morphism :
  MonoidMorphism prod_inj2.
Proof.
by split => //= x y; split => //=; rewrite left_id.
Qed.

Section CaseProd.

Context {R : monoid} (f : T → R) (g : S → R).

Definition case_prod (p : T * S) := f p.1 ⋅ g p.2.

Lemma case_prod_morphism `{!MonoidMorphism f, !MonoidMorphism g} :
  (∀ x y, f x ⋅ g y ≡ g y ⋅ f x) →
  MonoidMorphism case_prod.
Proof.
move=> fgC; split.
- solve_proper.
- by rewrite /case_prod !monoid_morphism_one left_id.
- case=> x1 x2; case=> y1 y2; rewrite /case_prod /= !monoid_morphism_mul.
  by rewrite assoc -[_ ⋅ g x2]assoc fgC !assoc.
Qed.

End CaseProd.

Section PairMor.

Context {R : monoid} (f : R → T) (g : R → S).

Definition pair_mor : R → T * S :=
  λ x, (f x, g x).

Global Instance pair_mor_morphism
    `{!MonoidMorphism f, !MonoidMorphism g} :
  MonoidMorphism pair_mor.
Proof.
split => //=.
- solve_proper.
- by split => /=; rewrite monoid_morphism_one.
- by move=> ??; split; rewrite /= monoid_morphism_mul.
Qed.

End PairMor.

End ProdMonoid.

Arguments prod_inj1 {T S}.
Arguments prod_inj2 {T S}.

Section ProdFinGen.

Context `{!FinGenMonoid T1, !FinGenMonoid T2}.

Global Program Instance prod_fin_gen : FinGenMonoid (T1 * T2)%type := {|
  generators := map (λ g, (g, 1)) generators ++ map (λ g, (1, g)) generators;
|}.
Next Obligation.
case=> x y.
have [lx [] ex Hx] := generate x.
have [ly [] ey Hy] := generate y.
exists (map (λ g, (g, 1)) lx ⋅ map (λ g, (1, g)) ly); split; first split.
- rewrite monoid_morphism_mul /= !monoid_morphism_mul_list !map_map /=.
  rewrite map_id -ex mul_list_one ?right_id //.
  by move=> x' /elem_of_list_fmap [? [] ->].
- rewrite monoid_morphism_mul /= !monoid_morphism_mul_list !map_map /=.
  rewrite map_id -ey mul_list_one ?left_id //.
  by move=> x' /elem_of_list_fmap [? [] ->].
- case=> x' y' /elem_of_app [] /elem_of_list_fmap.
  + case=> _ [] [<- ->] x'_lx; apply/elem_of_app; left.
    by apply/elem_of_list_fmap; exists x'; eauto.
  + case=> _ [] [-> <-] y'_ly; apply/elem_of_app; right.
    by apply/elem_of_list_fmap; exists y'; eauto.
Qed.

End ProdFinGen.

(** Semi Lattices *)

Record SemiLatticeMixin T `{!Equiv T, Join T, Bottom T, SqSubsetEq T} := {
  mixin_semi_lattice_assoc : Assoc (≡@{T}) (⊔);
  mixin_semi_lattice_comm : Comm (≡@{T}) (⊔);
  mixin_semi_lattice_left_id : LeftId (≡@{T}) (⊥) (⊔);
  mixin_semi_lattice_idemp : IdemP (≡@{⊤}) (⊔);
  mixin_semi_lattice_proper : Proper ((≡) ==> (≡) ==> (≡@{T})) (⊔);
  mixin_semi_lattice_sqsubseteq_iff : ∀ x y : T, x ⊑ y ↔ x ⊔ y ≡ y;
}.
Arguments SemiLatticeMixin T {_ _ _ _}.

Structure semi_lattice : Type := SemiLattice' {
  semi_lattice_car :> Type;
  semi_lattice_equiv : Equiv semi_lattice_car;
  semi_lattice_join : Join semi_lattice_car;
  semi_lattice_bottom : Bottom semi_lattice_car;
  semi_lattice_sqsubseteq : SqSubsetEq semi_lattice_car;
  semi_lattice_setoid_mixin : Equivalence (≡@{semi_lattice_car});
  semi_lattice_mixin : SemiLatticeMixin semi_lattice_car;
}.
Global Arguments semi_lattice_car : simpl never.
Global Arguments semi_lattice_equiv : simpl never.
Global Arguments semi_lattice_join : simpl never.
Global Arguments semi_lattice_bottom : simpl never.
Global Arguments semi_lattice_sqsubseteq : simpl never.
Global Arguments semi_lattice_setoid_mixin : simpl never.
Global Arguments semi_lattice_mixin : simpl never.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Join _) =>
  refine (@semi_lattice_join _); shelve : typeclass_instances.
Global Hint Extern 0 (Bottom _) =>
  refine (@semi_lattice_bottom _); shelve : typeclass_instances.
Global Hint Extern 0 (SqSubsetEq _) =>
  refine (@semi_lattice_sqsubseteq _); shelve : typeclass_instances.
Coercion semi_lattice_setoid (T : semi_lattice) :=
  @Setoid T (≡) (semi_lattice_setoid_mixin T).
Canonical Structure semi_lattice_setoid.

Section DefaultSqSubsetEq.

Context `{!Equiv T, Join T, Bottom T}.
Implicit Types x y z : T.

Definition default_sqsubseteq_aux :
  {R : relation T | ∀ x y, R x y ↔ x ⊔ y ≡ y}.
Proof. by exists (λ x y, x ⊔ y ≡ y). Qed.

Definition default_sqsubseteq : SqSubsetEq T :=
  proj1_sig default_sqsubseteq_aux.

Lemma default_sqsubseteq_eq x y : default_sqsubseteq x y ↔ x ⊔ y ≡ y.
Proof. exact: (proj2_sig default_sqsubseteq_aux). Qed.

Definition default_semi_lattice_mixin HA HC HI HId HP :=
  @Build_SemiLatticeMixin T _ _ _ _ HA HC HI HId HP default_sqsubseteq_eq.

End DefaultSqSubsetEq.

Section SemiLatticeTheory.

Variables T : semi_lattice.

Implicit Types x y z : T.

Global Instance semi_lattice_assoc : Assoc (≡@{T}) (⊔).
Proof. exact: (mixin_semi_lattice_assoc (semi_lattice_mixin T)). Defined.

Global Instance semi_lattice_comm : Comm (≡@{T}) (⊔).
Proof. exact: (mixin_semi_lattice_comm (semi_lattice_mixin T)). Defined.

Global Instance semi_lattice_left_id : LeftId (≡@{T}) (⊥) (⊔).
Proof. exact: (mixin_semi_lattice_left_id (semi_lattice_mixin T)). Defined.

Global Instance semi_lattice_idemp : IdemP (≡@{T}) (⊔).
Proof. exact: (mixin_semi_lattice_idemp (semi_lattice_mixin T)). Defined.

Global Instance semi_lattice_proper : Proper ((≡) ==> (≡) ==> (≡@{T})) (⊔).
Proof. exact: (mixin_semi_lattice_proper (semi_lattice_mixin T)). Defined.

Global Instance semi_lattice_right_id : RightId (≡@{T}) (⊥) (⊔).
Proof. by move=> x; rewrite comm left_id. Qed.

Lemma sqsubseteq_iff x y : x ⊑ y ↔ x ⊔ y ≡ y.
Proof.
exact: (mixin_semi_lattice_sqsubseteq_iff (semi_lattice_mixin T)).
Defined.

Global Instance semi_lattice_sqsubseteq_proper :
  Proper ((≡) ==> (≡@{T}) ==> iff) (⊑).
Proof.
by move=> x1 x2 ex y1 y2 ey; rewrite !sqsubseteq_iff ex ey.
Qed.

Global Instance semi_lattice_sqsubseteq_refl : Reflexive (@sqsubseteq T _).
Proof. by move=> x; rewrite sqsubseteq_iff idemp. Qed.

Global Instance semi_lattice_sqsubseteq_trans : Transitive (@sqsubseteq T _).
Proof.
move=> x y z; rewrite !sqsubseteq_iff => e1 e2.
by rewrite -{1}e2 assoc e1.
Qed.

Global Instance sqsubseteq_preorder : PreOrder (⊑@{T}).
Proof. constructor; apply _. Qed.

Global Instance semi_lattice_sqsubseteq_antisym : AntiSymm (≡@{T}) (⊑).
Proof.
by move=> x y; rewrite !sqsubseteq_iff => {2}<- {1}<-; rewrite comm.
Qed.

Lemma join_sqsubseteq x y z : x ⊔ y ⊑ z ↔ x ⊑ z ∧ y ⊑ z.
Proof.
rewrite !sqsubseteq_iff; split; last first.
  by case=> ez1 ez2; rewrite -assoc ez2.
move=> ez; split; rewrite -{1}ez.
- by rewrite !assoc idemp.
- by rewrite !assoc [y ⊔ x]comm -[x ⊔ y ⊔ y]assoc idemp.
Qed.

Lemma sqsubseteq_join_left x y : x ⊑ x ⊔ y.
Proof.
have: x ⊔ y ⊑ x ⊔ y by [].
by rewrite join_sqsubseteq; case.
Qed.

Lemma sqsubseteq_join_right x y : y ⊑ x ⊔ y.
Proof.
have: x ⊔ y ⊑ x ⊔ y by [].
by rewrite join_sqsubseteq; case.
Qed.

Lemma bottom_sqsubseteq x : ⊥ ⊑ x.
Proof. by rewrite sqsubseteq_iff semi_lattice_left_id. Qed.

Definition join_list : list T → T := foldr join ⊥.

Global Instance join_list_proper : Proper ((≡) ==> (≡)) join_list.
Proof.
by move=> xs ys; elim: xs ys / => //= x y xs ys -> _ ->.
Qed.

Notation "⨆" := join_list.
Lemma join_list_app xs ys : ⨆ (xs ++ ys) ≡ ⨆ xs ⊔ ⨆ ys.
Proof.
elim: xs => [|x xs IH] //=.
- by rewrite left_id.
- by rewrite IH assoc.
Qed.

Lemma join_list_sqsubseteq (xs : list T) y :
  ⨆ xs ⊑ y ↔ ∀ x, x ∈ xs → x ⊑ y.
Proof.
elim: xs => [|x xs IH] /=; split.
- by move=> _ ?; rewrite elem_of_nil.
- move=> _; exact: bottom_sqsubseteq.
- rewrite join_sqsubseteq; case=> xy /IH xsy x'.
  by rewrite elem_of_cons; case=> [->|]; eauto.
- rewrite join_sqsubseteq IH => xsy; split.
  + by apply xsy; rewrite elem_of_cons; eauto.
  + by move=> x' x'_xs; apply xsy; rewrite elem_of_cons; eauto.
Qed.

Lemma sqsubseteq_join_list (xs : list T) x : x ∈ xs → x ⊑ ⨆ xs.
Proof. by move: x; apply/join_list_sqsubseteq. Qed.

Lemma list_subseteq_join_list (xs ys : list T) :
  xs ⊆ ys → ⨆ xs ⊑ ⨆ ys.
Proof.
move=> xs_ys; apply/join_list_sqsubseteq => x /xs_ys x_ys.
exact: sqsubseteq_join_list.
Qed.

Lemma join_list_assoc (xss : list (list T)) :
  ⨆ (map (λ xs, ⨆ xs) xss) ≡ ⨆ (concat xss).
Proof.
apply (anti_symm _).
- rewrite join_list_sqsubseteq=> _ /elem_of_list_fmap [xs [] -> xs_xss].
  rewrite join_list_sqsubseteq=> x x_xs; apply: sqsubseteq_join_list.
  by rewrite elem_of_concat; eauto.
- rewrite join_list_sqsubseteq=> x /elem_of_concat [xs [] xs_xss x_xs].
  transitivity (⨆ xs); first exact: sqsubseteq_join_list.
  by apply: sqsubseteq_join_list; apply/elem_of_list_fmap; eauto.
Qed.

Lemma join_list_bottom xs :
  (∀ x, x ∈ xs → x ≡ ⊥) →
  ⨆ xs ≡ ⊥.
Proof.
move=> const_x; apply: (anti_symm _).
- by rewrite join_list_sqsubseteq => x x_xs; rewrite (const_x _ x_xs).
- exact: bottom_sqsubseteq.
Qed.

Lemma join_mono x1 x2 y1 y2 :
  x1 ⊑ x2 →
  y1 ⊑ y2 →
  x1 ⊔ y1 ⊑ x2 ⊔ y2.
Proof.
move=> x12 y12; rewrite join_sqsubseteq; split.
- by etransitivity; last exact: sqsubseteq_join_left.
- by etransitivity; last exact: sqsubseteq_join_right.
Qed.

End SemiLatticeTheory.

Notation "⨆" := join_list : ka_scope.

Lemma join_list_join {T : Type} {S : semi_lattice}
    (f1 : T → S) (f2 : T → S) (xs : list T) :
  ⨆ (map (λ x, f1 x ⊔ f2 x) xs) ≡
  ⨆ (map f1 xs) ⊔ ⨆ (map f2 xs).
Proof.
elim: xs => //= [|x xs IH]; first by rewrite right_id.
rewrite IH [in X in _ ≡ X]assoc -[(f1 x ⊔ _) ⊔ f2 x]assoc.
by rewrite [⨆ _ ⊔ f2 x]comm !assoc.
Qed.

Section GSetSemiLattice.

Context `{Countable T}.

Global Instance gset_bottom : Bottom (gset T) := ∅ : gset T.
Global Instance gset_join : Join (gset T) := (∪).
Global Instance gset_sqsubseteq : SqSubsetEq (gset T) := (⊆).

Lemma gset_semi_lattice_mixin : SemiLatticeMixin (gset T).
Proof.
split.
- apply _.
- apply _.
- apply _.
- apply _.
- solve_proper.
- move=> X Y.
  by rewrite /sqsubseteq /gset_sqsubseteq subseteq_union.
Qed.

Canonical Structure gset_semi_lattice :=
  @SemiLattice' (gset T) _ _ _ _ _
    gset_semi_lattice_mixin.

End GSetSemiLattice.

Class SemiLatticeMorphism (T S : semi_lattice) (f : T → S) := {
  semi_lattice_morphism_proper :: Proper ((≡) ==> (≡)) f;
  semi_lattice_morphism_bottom : f ⊥ ≡ ⊥;
  semi_lattice_morphism_join : ∀ x y, f (x ⊔ y) ≡ f x ⊔ f y;
}.

Section SemiLatticeMorphismTheory.

Variables (T S : semi_lattice) (f : T → S).

Context `{SemiLatticeMorphism T S f}.

Global Instance semi_lattice_morphism_subseteq_proper : Proper ((⊑) ==> (⊑)) f.
Proof.
move=> x y; rewrite !sqsubseteq_iff => {2}<-.
by rewrite semi_lattice_morphism_join.
Qed.

Lemma semi_lattice_morphism_join_list (xs : list T) :
  f (⨆ xs) ≡ ⨆ (map f xs).
Proof.
elim: xs => /= [|x xs IH]; rewrite ?semi_lattice_morphism_bottom //.
by rewrite semi_lattice_morphism_join IH.
Qed.

End SemiLatticeMorphismTheory.

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

End KATermTheory.

Canonical Structure bool_setoid :=
  eq_setoid bool.

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

Section PseudoTop.

Context `{FinGenMonoid T}.

Definition pseudo_top : ka_term T :=
  star (⨆ (map Unit generators)).

Lemma pseudo_top_absorb x : Unit x ⋅ pseudo_top ⊑ pseudo_top.
Proof.
case: (generate x) => xs [] -> {x}; elim: xs=> [|x xs IH] sub /=.
  by rewrite left_id.
rewrite monoid_morphism_mul -assoc IH.
  move=> ? x_in; apply: sub; apply/elem_of_cons; eauto.
have x_gen: x ∈ generators by apply: sub; rewrite elem_of_cons; eauto.
have /sqsubseteq_join_list {}x_gen: Unit x ∈ map Unit generators.
  by apply/elem_of_list_fmap; eauto.
rewrite x_gen; exact: pre_ka_mul_star.
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

Arguments pseudo_top {T _}.

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

Lemma elem_of_lang_join_list (Bs : list lang) x :
  (⨆ Bs) x ↔ ∃ B, B ∈ Bs ∧ B x.
Proof.
elim: Bs => /= [|B Bs ->].
- by split => // - [? [] /elem_of_nil].
- split=> [[B_x|[B' [] B'_Bs B'_x]]|[B' [] /elem_of_cons [->|]]].
  + by exists B; rewrite elem_of_cons; eauto.
  + by exists B'; rewrite elem_of_cons; eauto.
  + by eauto.
  + by move=> B'_Bs B'_x; right; exists B'; eauto.
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

(* Theorem 5 *)

Lemma l_alt e x : l e x ↔ Unit x ⊑ e.
Proof.
split; last first.
  move=> x_e; have: l (Unit x) ⊑ l e.
    by apply: semi_lattice_morphism_subseteq_proper.
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

Lemma l_reflects_order xs ys :
  l (⨆ (map Unit xs)) ⊑ l (⨆ (map Unit ys)) →
  ⨆ (map Unit xs) ⊑ ⨆ (map Unit ys).
Proof.
move=> l_sub; apply/join_list_sqsubseteq => x /[dup].
case/elem_of_list_fmap => {}x [] -> x_xs /sqsubseteq_join_list /l_alt.
move=> /l_sub; rewrite semi_lattice_morphism_join_list elem_of_lang_join_list.
case=> _ [] /elem_of_list_fmap [y [] -> y_ys].
case/elem_of_list_fmap: y_ys=> {}y [] -> y_ys /= ->.
by apply/sqsubseteq_join_list/elem_of_list_fmap; eauto.
Qed.

(* Corollary 7 *)

Lemma l_inj_finite xs ys :
  l (⨆ (map Unit xs)) ≡ l (⨆ (map Unit ys)) →
  ⨆ (map Unit xs) ≡ ⨆ (map Unit ys).
Proof.
move=> l_eq; apply: anti_symm; by apply/l_reflects_order; rewrite l_eq.
Qed.

(* Corollary 8 *)

Lemma either_empty_or_nonzero e : e ≡ ⊥ ∨ ∃ s, l e s.
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

Section KATermProj.

Variables (T S : monoid).

Definition ka_term_proj1 : ka_term (T * S) → ka_term T :=
  ka_term_map fst.

Definition ka_term_proj2 : ka_term (T * S) → ka_term S :=
  ka_term_map snd.

Definition ka_term_inj1 : ka_term T → ka_term (T * S) :=
  ka_term_map prod_inj1.

Definition ka_term_inj2 : ka_term S → ka_term (T * S) :=
  ka_term_map prod_inj2.

Definition ka_term_diag : ka_term T → ka_term (T * T) :=
  ka_term_map (pair_mor id id).

Global Instance ka_term_proj1_morphism :
  PreKAMorphism ka_term_proj1.
Proof. apply _. Qed.

Global Instance ka_term_proj2_morphism :
  PreKAMorphism ka_term_proj2.
Proof. apply _. Qed.

Global Instance ka_term_inj1_morphism :
  PreKAMorphism ka_term_inj1.
Proof. apply _. Qed.

Global Instance ka_term_inj2_morphism :
  PreKAMorphism ka_term_inj2.
Proof. apply _. Qed.

Global Instance ka_term_diag_morphism :
  PreKAMorphism ka_term_diag.
Proof. apply _. Qed.

End KATermProj.

Section Automata.

Context (Σ : Type) `{!EqDecision Σ, !Finite Σ}.
Context (T : pre_ka) (f : Σ → T).

Record fsa := FSA {
  fsa_state : Type;
  fsa_elem : T;
  fsa_state_eq_dec : EqDecision fsa_state;
  fsa_state_finite : Finite fsa_state;
  fsa_initial : fsa_state;
  fsa_final : fsa_state → bool;
  fsa_interp : fsa_state → T;
  fsa_trans : Σ → fsa_state → fsa_state;
  fsa_interp_initial : fsa_interp fsa_initial ≡ fsa_elem;
  fsa_derivable : ∀ σ : fsa_state,
    fsa_interp σ ≡
    pre_ka_of_bool (fsa_final σ) ⊔
    ⨆ (map (λ x, f x ⋅ fsa_interp (fsa_trans x σ)) (enum Σ));
}.

Global Existing Instance fsa_state_eq_dec.
Global Existing Instance fsa_state_finite.

Implicit Types (A B : fsa).

Program Definition fsa_bottom : fsa := {|
  fsa_state := unit;
  fsa_elem := ⊥;
  fsa_initial := tt;
  fsa_final _ := false;
  fsa_interp σ := ⊥;
  fsa_trans x σ := tt;
|}.

Next Obligation. by []. Qed.

Next Obligation.
move=> []; rewrite left_id join_list_bottom // => x.
by case/elem_of_list_fmap => y [] ->; rewrite right_absorb.
Qed.

Program Definition fsa_join A B : fsa := {|
  fsa_state := fsa_state A * fsa_state B;
  fsa_elem := fsa_elem A ⊔ fsa_elem B;
  fsa_initial := (fsa_initial A, fsa_initial B);
  fsa_final := λ σ, fsa_final σ.1 || fsa_final σ.2;
  fsa_interp := λ σ, fsa_interp σ.1 ⊔ fsa_interp σ.2;
  fsa_trans := λ x σ, (fsa_trans x σ.1, fsa_trans x σ.2);
|}.

Next Obligation.
by move=> A B /=; rewrite !fsa_interp_initial.
Qed.

Next Obligation.
move=> A B [σA σB] /=.
rewrite (fsa_derivable σA) (fsa_derivable σB) pre_ka_of_bool_or.
set A1 := pre_ka_of_bool (fsa_final σA).
set B1 := pre_ka_of_bool (fsa_final σB).
rewrite assoc -[_ ⊔ _ ⊔ B1]assoc [_ ⊔ B1]comm assoc.
rewrite -[((A1 ⊔ B1) ⊔ _) ⊔ _]assoc -join_list_join.
set xs1 := map _ _; set xs2 := map _ _.
have -> // : xs1 ≡ xs2.
rewrite /xs1 /xs2; apply: (@Proper_map' (eq_setoid Σ)) => //= x y ->.
by rewrite pre_ka_right_dist.
Qed.

Record nfa := NFA {
  nfa_state : semi_lattice;
  nfa_state_leibniz : LeibnizEquiv nfa_state;
  nfa_state_eq_dec : EqDecision nfa_state;
  nfa_state_finite : Finite nfa_state;
  nfa_elem : T;
  nfa_initial : nfa_state;
  nfa_final : nfa_state → bool;
  nfa_interp : nfa_state → T;
  nfa_interp_bottom : nfa_interp ⊥ ≡ ⊥;
  nfa_interp_join : ∀ σ₁ σ₂,
    nfa_interp (σ₁ ⊔ σ₂) ≡ nfa_interp σ₁ ⊔ nfa_interp σ₂;
  nfa_trans : Σ → nfa_state → nfa_state;
  nfa_interp_initial : nfa_interp nfa_initial ≡ nfa_elem;
  nfa_derivable : ∀ σ : nfa_state,
    nfa_interp σ ≡
    pre_ka_of_bool (nfa_final σ) ⊔
    ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x σ)) (enum Σ));
}.

Global Existing Instance nfa_state_leibniz.
Global Existing Instance nfa_state_eq_dec.
Global Existing Instance nfa_state_finite.

Program Definition fsa_to_nfa A : nfa := {|
  nfa_state := gset (fsa_state A);
  nfa_elem := fsa_elem A;
  nfa_initial := {[fsa_initial A]};
  nfa_final Σ := existsb (λ σ, fsa_final σ) (elements Σ);
  nfa_interp Σ := ⨆ (map (λ σ, fsa_interp σ) (elements Σ));
  nfa_trans x Σ := list_to_set (map (fsa_trans x) (elements Σ));
|}.

Next Obligation.
by move=> A; rewrite /= elements_empty.
Qed.

Next Obligation.
move=> A Σ₁ Σ₂ /=; apply: (anti_symm _).
- rewrite join_list_sqsubseteq => _ /elem_of_list_fmap [σ [] ->].
  rewrite elem_of_elements elem_of_union; case=> [σ_Σ|σ_Σ].
  + etransitivity; last exact: sqsubseteq_join_left.
    apply/sqsubseteq_join_list/elem_of_list_fmap.
    by eexists _; split; rewrite // elem_of_elements.
  + etransitivity; last exact: sqsubseteq_join_right.
    apply/sqsubseteq_join_list/elem_of_list_fmap.
    by eexists _; split; rewrite // elem_of_elements.
- rewrite join_sqsubseteq; split.
  + rewrite join_list_sqsubseteq => _ /elem_of_list_fmap [σ [] ->].
    rewrite elem_of_elements => σ_Σ.
    apply/sqsubseteq_join_list/elem_of_list_fmap.
    by exists σ; split; rewrite // elem_of_elements elem_of_union; eauto.
  + rewrite join_list_sqsubseteq => _ /elem_of_list_fmap [σ [] ->].
    rewrite elem_of_elements => σ_Σ.
    apply/sqsubseteq_join_list/elem_of_list_fmap.
    by exists σ; split; rewrite // elem_of_elements elem_of_union; eauto.
Qed.

Next Obligation.
move=> A; rewrite /= elements_singleton /= right_id.
by rewrite fsa_interp_initial.
Qed.

Next Obligation.
move=> A Σ' /=; apply: (anti_symm _).
- rewrite join_list_sqsubseteq => _ /elem_of_list_fmap [σ' [] -> σ'_Σ'].
  rewrite fsa_derivable; apply: join_mono.
  + case final_σ': (fsa_final σ'); last exact: bottom_sqsubseteq.
    rewrite (_ : existsb _ _ = true) //.
    by apply/existsb_exists; exists σ'; split; rewrite // -elem_of_list_In.
  + rewrite join_list_sqsubseteq=> _ /elem_of_list_fmap [x [] -> _].
    transitivity (f x ⋅ ⨆ (map (λ σ, fsa_interp σ)
      (elements (list_to_set (map (fsa_trans x) (elements Σ')) : gset _)))).
    * apply: pre_ka_mul_mono=> //=.
      apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
      eexists _; split; rewrite // elem_of_elements elem_of_list_to_set.
      by apply/elem_of_list_fmap; eexists _; split.
    * apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
      exists x; split => //; exact: elem_of_enum.
- rewrite join_sqsubseteq; split.
  + case e: existsb; last exact: bottom_sqsubseteq.
    case/existsb_exists: e=> σ [] /elem_of_list_In σ_Σ' final_σ.
    transitivity (fsa_interp σ).
    * rewrite fsa_derivable final_σ; exact: sqsubseteq_join_left.
    * apply/sqsubseteq_join_list/elem_of_list_fmap.
      by exists σ; eauto.
  + rewrite join_list_sqsubseteq=> _ /elem_of_list_fmap [x [] -> _].
    rewrite join_list_right_dist map_map join_list_sqsubseteq.
    move=> _ /elem_of_list_fmap [σ [] ->].
    rewrite elem_of_elements elem_of_list_to_set.
    case/elem_of_list_fmap=> σ' [] -> σ'_Σ'.
    transitivity (fsa_interp σ').
    * rewrite (fsa_derivable σ').
      etransitivity; last exact: sqsubseteq_join_right.
      apply/sqsubseteq_join_list/elem_of_list_fmap.
      exists x; split => //; exact: elem_of_enum.
    * apply/sqsubseteq_join_list/elem_of_list_fmap.
      by exists σ'; split.
Qed.

Section FSAMul.

Variables (A : fsa) (B : nfa).

Implicit Types (σ : fsa_state A * nfa_state B).
Implicit Types (σA : fsa_state A) (σB : nfa_state B).

Let combine σ σB := (σ.1, σ.2 ⊔ σB).

Let from σA :=
  (σA, if fsa_final σA then nfa_initial B else ⊥).

Let final σ :=
  fsa_final σ.1 && nfa_final (nfa_initial B) || nfa_final σ.2.

Let interp σ := fsa_interp σ.1 ⋅ nfa_elem B ⊔ nfa_interp σ.2.

Let trans x σ :=
  combine (from (fsa_trans x σ.1)) (nfa_trans x σ.2).

Lemma interp_combine σ σB :
  interp (combine σ σB) ≡ interp σ ⊔ nfa_interp σB.
Proof. by rewrite /interp /= nfa_interp_join assoc. Qed.

Lemma interp_from σA :
  interp (from σA) ≡ fsa_interp σA ⋅ nfa_elem B.
Proof.
rewrite /interp /=.
case final_σA: (fsa_final σA); last by rewrite nfa_interp_bottom right_id.
have {2} ->: fsa_interp σA ≡ 1 ⊔ fsa_interp σA.
  by rewrite fsa_derivable final_σA /= assoc idemp.
by rewrite nfa_interp_initial pre_ka_left_dist left_id comm.
Qed.

Lemma pre_ka_of_bool_final σ :
  @pre_ka_of_bool T (final σ) ≡
  pre_ka_of_bool (fsa_final σ.1)
  ⋅ pre_ka_of_bool (nfa_final (nfa_initial B))
  ⊔ pre_ka_of_bool (nfa_final σ.2).
Proof.
by rewrite /final pre_ka_of_bool_or pre_ka_of_bool_and.
Qed.

Program Definition fsa_mul : fsa := {|
  fsa_state := fsa_state A * nfa_state B;
  fsa_elem := fsa_elem A ⋅ nfa_elem B;
  fsa_initial := from (fsa_initial A);
  fsa_final σ := nfa_final σ.2;
  fsa_interp := interp;
  fsa_trans := trans;
|}.

Next Obligation.
by rewrite interp_from fsa_interp_initial.
Qed.

Next Obligation.
move=> σ.
set F := λ x, f x ⋅ interp (trans x σ).
pose (F1 := λ x, f x ⋅ fsa_interp (fsa_trans x σ.1)).
pose (F2 := λ x, f x ⋅ nfa_interp (nfa_trans x σ.2)).
have ->: ⨆ (map F (enum Σ)) ≡
         (⨆ (map F1 (enum Σ))) ⋅ nfa_elem B ⊔ ⨆ (map F2 (enum Σ)).
{ }
rewrite /interp fsa_derivable nfa_derivable.
rewrite !assoc; apply: semi_lattice_proper => //.
rewrite [pre_ka_of_bool (nfa_final σ.2) ⊔ _]comm.
apply: semi_lattice_proper => //.
rewrite pre_ka_left_dist. ; apply: semi_lattice_proper => //.

Qed.


End Automata.



Section Derivatives.


Implicit Types (x y : T) (xs ys : list T) (e : ka_term (list T)).

Definition contains_one e : bool :=
  ka_term_elim (λ xs, ∏ (map (λ _, ⊥) xs)) e.

Fixpoint derivative x e : ka_term (list T) :=
  match e with
  | Unit [] =>
    ⊥
  | Unit (y :: ys) =>
    if bool_decide (x = y) then 1 else ⊥
  | ka_term_bottom =>
    ⊥
  | ka_term_join e1 e2 =>
    derivative x e1 ⊔ derivative x e2
  | ka_term_mul e1 e2 =>
    derivative x e1 ⋅ e2 ⊔
    (if contains_one e1 then 1 else ⊥) ⋅ derivative x e2
  | ka_term_star e =>
    derivative x e ⋅ star e
  end.




Record fsa : Type := {
  fsa_state : setoid;
  fsa_state_leibniz : LeibnizEquiv fsa_state;
  fsa_state_eq_dec : EqDecision fsa_state;
  fsa_state_finite : Finite fsa_state;
}.


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
  residue : ka_term (list T * list T);
  expand_rel :
    ∀ xs : list T,
      Unit (1, xs) ⋅ e ⊑
        Unit (xs, xs) ⋅ ⨆ (map (λ ys, Unit (1, ys)) (next xs))
        ⊔ ka_term_diag pseudo_top ⋅ diff ⋅ residue;
}.




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

Lemma star_leq : forall (t : ka_term T), 1 + t⋅t✶ ≤ t✶.
Proof.
  intros.
  rewrite - star_expand.
  apply leq_reflex.
Qed.

Definition build_term (side : T -> ka_term T) := fold_right (λ (n : T) t, side n ⋅ t).

Definition string_to_ka_term ls :=
  match ls with (l1, l2) =>
    (build_term L 1 l1)⋅(build_term R 1 l2)
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
Lemma leq_term__leq_term_star : ∀ (t t': ka_term T), t ≤ t' -> t ≤ t'✶.
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


Definition finite_term t := ∃ ls, ∀ s, In s ls <-> lang_interp t s.

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
Qed.

Lemma finite_term_dist_over_plus : ∀ t t', finite_term (t + t') <-> finite_term t ∧ finite_term t'.
Proof.
  intros t t'. split.
  - intros [ls H].
    simpl in H;
    unfold ka_pred_add in H.
    (* admit. *)
    split; unfold finite_term.
    + exists ls.
      intros s.
      rewrite H.
      split.
      * intros [G | G]; try assumption.
        admit.
      * intuition.
    + exists ls.
      intros s.
      rewrite H.
      split.
      * intros [G | G]; try assumption.
        admit.
      * intuition.
  - intros [[l1 H1] [l2 H2]].
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
Admitted.

Lemma finite_term_dist_over_dot : ∀ t t', finite_term (t ⋅ t') <-> finite_term t ∧ finite_term t'.
Proof.
Admitted.

(* Theorem 6' *)
Theorem finite_def : ∀ t,
  (∃ ls, t ≡ cstring_sum ls)
  <->
  finite_term t.
Proof.
  intros t; split.
  - intros [ls H].
    exists ls.
    intros s.
    rewrite H; clear H.
    induction ls as [| c ls IHls].
    + simpl. reflexivity.
    + simpl. unfold ka_pred_add.
      rewrite - IHls.
      rewrite string_interp_self.
      reflexivity.
  -
    (* intros [ls H].
    exists ls.
    induction t.
    + simpl in H. unfold ka_pred_zero in H.
      induction ls.
      * reflexivity.
      * specialize (H a0). simpl in H.
        exfalso; apply H. intuition.
    + simpl in H. unfold ka_pred_unit in H.
      induction ls as [| c ls IHls].
      * specialize (H ([], []));
        simpl in H.
        exfalso; intuition.
      * simpl in H.
        specialize (H c); simpl in H. *)
    (* unfold finite_term. *)
    (* intros [ls H]. *)
    induction t(* ; intros [ls H] *).
    + intros [ls H]. exists []. reflexivity.
    + intros [ls H]. exists [([], [])]. unfold cstring_sum. simpl.
      rewrite Dot_Id2; rewrite Plus_Id'.
      reflexivity.
    + intros [ls H]. exists [([t], [])]; unfold cstring_sum; simpl.
      repeat (rewrite Dot_Id1);
      rewrite Plus_Id'.
      reflexivity.
    + intros [ls H]. exists [([], [t])]; unfold cstring_sum; simpl.
      rewrite Dot_Id1;
      rewrite Dot_Id2;
      rewrite Plus_Id'.
      reflexivity.
    + rewrite finite_term_dist_over_plus. intros [H1 H2].
      apply IHt1 in H1 as [l1 H1].
      apply IHt2 in H2 as [l2 H2].
      exists (l1 ++ l2).
      simpl.
      rewrite cstring_app_commute.
      rewrite H1; rewrite H2.
      reflexivity.
    + admit.
    + intros [ls H].
      induction t.
      * exists [([], [])].
        unfold cstring_sum.
        simpl.
        rewrite zero_star.
        rewrite Plus_Com; rewrite Plus_Id;
        rewrite Dot_Id2.
        reflexivity.
      * exists [([], [])].
        unfold cstring_sum;
        simpl.
        rewrite one_star.
        rewrite Plus_Com; rewrite Plus_Id;
        rewrite Dot_Id2.
        reflexivity.
      *

    (* + rewrite finite_term_dist_over_dot. intros [H1 H2].
      apply IHt1 in H1 as [l1 H1].
      apply IHt2 in H2 as [l2 H2].

    intros [[l1 H1] [l2 H2]]. simpl in H.
      unfold ka_pred_add in H.
      unfold finite_term in IHt1, IHt2.
      induction ls as [|c ls IHls].
      * have [t_cond1 | [s1 t_cond1]] := either_empty_or_nonzero t1;
        have [t_cond2 | [s2 t_cond2]] := either_empty_or_nonzero t2;
        try (specialize (H s1); simpl in H; exfalso; rewrite H; intuition).
        -- exists []. rewrite t_cond1; rewrite t_cond2; rewrite Plus_Idemp.
           reflexivity.
        -- specialize (H s2).
           simpl in H.
           exfalso. rewrite H. intuition.
      * simpl in H.
        specialize (H c) as [c' H]. *)
Admitted.

(* Corollary 7' *)
Theorem finite_terms_interp__equiv : ∀ (t t' : ka_term T),
  finite_term t -> finite_term t' ->
    (∀ s, lang_interp t s <-> lang_interp t' s) ->
      t ≡ t'.
Proof.
  intros t t' Hft Hft' Hli.
  have Hft1 := Hft.
  have Hft1' := Hft'.
  apply finite_def in Hft1 as [ls Htsum], Hft1' as [ls' Htsum'].
  destruct Hft as [s Ht], Hft' as [s' Ht'].
  rewrite Hli in Ht.
  rewrite Htsum.
  rewrite Htsum'.
  unfold cstring_sum.
  unfold cstring_sum.
  induction ls as [|c ls IHls], ls' as [|c' ls'].
  - reflexivity.
  - simpl in *.
    unfold cstring_sum in Htsum.
    simpl in Htsum.
  induction ls as [|c ls IHls].
  - unfold cstring_sum in Htsum. simpl in Htsum. simpl.
  assert (G : cstring_sum ls ≡ cstring_sum ls').
  {
    unfold cstring_sum.
    unfold map.
    compute.
  }

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

End Theory.
(* -------------- *)

Definition R_M (P : list mm2_instr) :=
   term_list_to_term (map_indexed interp_single P).

(* Local Open Scope ka_scope. *)

Example string_to_ka_term__test1 :
  string_to_ka_term ([a; b; a; a], [a; b; a; a]) ≡ (lr a ⋅ lr b ⋅ lr a ⋅ lr a).
Proof.
  simpl; unfold lr_term.
  rewrite Dot_Id1.
  repeat (rewrite Dot_Assoc).
  reflexivity.
Qed.

Example string_to_ka_term__test2 :
  string_to_ka_term Σ_M [a; b; c_1] ≡ lr a ⋅ lr b ⋅ lr c_1.
Proof.
  simpl; unfold lr_term.
  rewrite Dot_Id1.
  repeat (rewrite Dot_Assoc).
  reflexivity.
Qed.

Check lang_interp.
Theorem term_leq_R_M__in_lang_interp : ∀ P s s', (string_to_ka_term Σ_M L s) ⋅ (string_to_ka_term Σ_M R s') ≤ R_M P <-> lang_interp Σ_M (R_M P) (s, s').
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
