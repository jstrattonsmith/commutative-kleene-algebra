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

Section EnumLists.

Context `{!EqDecision T, !Finite T}.

Implicit Types (n : nat) (x y : T) (xs ys : list T).

Fixpoint enum_list_eq n : list (list T) :=
  match n with
  | 0 => [[]]
  | S n => map (λ '(x, xs), x :: xs) (all_pairs (enum T) (enum_list_eq n))
  end.

Lemma concat_inj {A : Type} (ls ls' : list (list A)) : ls = ls' -> concat ls = concat ls'.
Proof.
by move=> ->.
Qed.

Lemma elem_of_enum_list_eq n xs : xs ∈ enum_list_eq n ↔ length xs = n.
Proof.
elim: n => [|n IH] /= in xs *.
  by rewrite elem_of_list_singleton -length_zero_iff_nil.
rewrite elem_of_list_fmap; split.
- by case=> [[x {}xs] [-> /= /elem_of_all_pairs [_ /IH <-]]].
- case: xs => //= x xs [/IH {}IH]; exists (x, xs); split=> //.
  rewrite elem_of_all_pairs /=; split => //.
  exact: elem_of_enum.
Qed.

Lemma enum_list_eq_Sn n : enum_list_eq (S n) =
  map (λ '(x, xs), x :: xs) (all_pairs (enum T) (enum_list_eq n)).
Proof. rewrite //=. Qed.

Lemma destruct_list_cons_len x xs :
  ∃ x' xs', x :: xs = xs' ++ [x'] ∧ length xs = length xs'.
elim: xs x => [x | x xs IH x']; first by exists x, []; by rewrite app_nil_l.
specialize (IH x).
move: IH => [y [ys [-> Hlen]]].
exists y, (x'::ys).
split; first by rewrite app_comm_cons.
rewrite length_app /=; lia.
Qed.

Lemma destruct_list_app_len x xs :
  ∃ x' xs', xs ++ [x] = x' :: xs' ∧ length xs = length xs'.
Proof.
elim: xs x => [x | x xs IH x']; first by exists x, []; by rewrite app_nil_l.
specialize (IH x').
rewrite -app_comm_cons.
move: IH => [y [ys [-> Hlen]]].
exists x, (y::ys).
split; first done.
by rewrite /= Hlen.
Qed.

Lemma flat_map_enum_list_eq_id k : flat_map enum_list_eq [k] = enum_list_eq k.
Proof.
  by rewrite //= app_nil_r.
Qed.

Definition enum_list_lt n : list (list T) :=
  flat_map enum_list_eq (seq 0 n).

Lemma elem_of_enum_list_lt n xs : xs ∈ enum_list_lt n ↔ length xs < n.
Proof.
rewrite /enum_list_lt flat_map_concat_map elem_of_concat; split.
- case=> [_ [] /elem_of_list_fmap [i [] ->]].
  move=> /elem_of_seq i_n /elem_of_enum_list_eq ->; lia.
- move=> xs_n; exists (enum_list_eq (length xs)).
  split; last by rewrite elem_of_enum_list_eq; lia.
  rewrite elem_of_list_fmap; exists (length xs); split => //.
  rewrite elem_of_seq; lia.
Qed.

End EnumLists.

Compute @enum_list_eq bool _ _ 3.
Compute map (λ '(x, xs), xs ++ [x]) (all_pairs (enum bool) (@enum_list_eq bool _ _ 2)).

Compute @enum_list_eq bool _ _ 3.
(* Compute @enum_list_eq' bool _ _ 3. *)

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
  @Setoid T equivL _.

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

(* Arguments mul_list {_}. *)

Lemma mul_list_one xs :
  (∀ x, x ∈ xs → x ≡ 1) →
  ∏ xs ≡ 1.
Proof.
elim: xs => //= x xs IH xs_1.
rewrite (xs_1 x) ?elem_of_cons ?left_id; eauto.
rewrite IH // => x' x'_xs; apply: xs_1.
by rewrite elem_of_cons; eauto.
Qed.

Lemma mul_list_app ls ls' :
  ∏ (ls ++ ls') ≡ (∏ ls) ⋅ (∏ ls').
Proof.
elim: ls => [|l ls IHls]; first by rewrite //= ?left_id.
by rewrite //= {}IHls assoc.
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
  generator : Type;
  generator_interp : generator → T;
  #[global] generator_eq_dec :: EqDecision generator;
  #[global] generator_finite :: Finite generator;
  generate x : {l : list generator | x ≡ ∏ (map generator_interp l) };
}.

Arguments generator T {_}.

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
  generator := T;
  generator_interp x := [x];
|}.

Next Obligation.
by move=> xs; exists xs; elim: xs => //= x xs <-.
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
  generator := generator T1 + generator T2;
  generator_interp (x : generator T1 + generator T2) :=
    match x return T1 * T2 with
    | inl x => (generator_interp x, 1)
    | inr x => (1, generator_interp x)
    end;
|}.

Next Obligation.
case=> x y.
have [[lx ex] [ly ey]] := (generate x, generate y).
exists (map inl lx ++ map inr ly).
rewrite map_app !map_map monoid_morphism_mul; split.
- rewrite monoid_morphism_mul !monoid_morphism_mul_list !map_map /= -ex.
  by rewrite mul_list_one ?right_id // => ? /elem_of_list_fmap [? [] -> _].
- rewrite monoid_morphism_mul !monoid_morphism_mul_list !map_map /= -ey.
  by rewrite mul_list_one ?left_id // => ? /elem_of_list_fmap [? [] -> _].
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

Lemma sqsubseteq_join x y z : x ⊑ y ∨ x ⊑ z → x ⊑ y ⊔ z.
Proof.
case=> ->; [exact: sqsubseteq_join_left|exact: sqsubseteq_join_right].
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

Lemma sqsubseteq_join_list' (xs : list T) x x' : x' ∈ xs -> x ⊑ x' -> x ⊑ ⨆ xs.
Proof.
move=> Helem ->; by apply sqsubseteq_join_list.
Qed.

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

Section DecidableSemiLattice.

Variable T : semi_lattice.
Context `{!EqDecision T, !LeibnizEquiv T}.

Global Instance semi_lattice_sqsubseteq_dec :
  RelDecision (⊑@{T}).
Proof.
  move=> x y.
  by case: (decide (x ⊔ y = y)) => H; [left|right];
  rewrite sqsubseteq_iff leibniz_equiv_iff.
Qed.

End DecidableSemiLattice.

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

Global Instance semi_lattice_morphism_sqsubseteq_proper : Proper ((⊑) ==> (⊑)) f.
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

Section PseudoTop.

Context `{FinGenMonoid T}.

Definition pseudo_top : ka_term T :=
  star (⨆ (map (λ g, Unit (generator_interp g)) (enum (generator T)))).

Lemma pseudo_top_absorb x : Unit x ⋅ pseudo_top ⊑ pseudo_top.
Proof.
case: (generate x) => xs -> {x}; elim: xs=> [|x xs IH] //=.
  by rewrite left_id.
rewrite monoid_morphism_mul -assoc IH /pseudo_top.
set f := λ x', Unit (generator_interp x').
have /sqsubseteq_join_list x_gen: f x ∈ map f (enum (generator T)).
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

Arguments fsa_trans {_}.

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
  nfa_final_bottom : nfa_final ⊥ = false;
  nfa_final_join : ∀ σ₁ σ₂,
    nfa_final (σ₁ ⊔ σ₂) = nfa_final σ₁ || nfa_final σ₂;
  nfa_interp : nfa_state → T;
  nfa_interp_bottom : nfa_interp ⊥ ≡ ⊥;
  nfa_interp_join : ∀ σ₁ σ₂,
    nfa_interp (σ₁ ⊔ σ₂) ≡ nfa_interp σ₁ ⊔ nfa_interp σ₂;
  nfa_interp_initial : nfa_interp nfa_initial ≡ nfa_elem;
  nfa_trans : Σ → nfa_state → nfa_state;
  nfa_trans_bottom : ∀ x, nfa_trans x ⊥ = ⊥;
  nfa_trans_join : ∀ x σ₁ σ₂,
    nfa_trans x (σ₁ ⊔ σ₂) = nfa_trans x σ₁ ⊔ nfa_trans x σ₂;
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
move=> A σ₁ σ₂; apply: eq_bool_prop_intro.
rewrite orb_True !existb_True !Exists_exists; split.
- case=> a [] /elem_of_elements-/elem_of_union [] a_σ final_a.
  + by left; exists a; split; rewrite // elem_of_elements.
  + by right; exists a; split; rewrite // elem_of_elements.
- by case; case=> a [] /elem_of_elements a_σ final_a; exists a;
  rewrite elem_of_elements elem_of_union; eauto.
Qed.

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
by move=> A x /=; rewrite elements_empty /=.
Qed.

Next Obligation.
move=> X x /= σ₁ σ₂; apply sets.set_eq=> a.
rewrite elem_of_union !elem_of_list_to_set; split.
- case/elem_of_list_fmap=> b [] -> /elem_of_elements.
  case/elem_of_union=> b_σ.
  + left; apply/elem_of_list_fmap; exists b; rewrite elem_of_elements.
    by eauto.
  + right; apply/elem_of_list_fmap; exists b; rewrite elem_of_elements.
    by eauto.
- case; case/elem_of_list_fmap=> b [] -> /elem_of_elements b_σ.
  + apply/elem_of_list_fmap; exists b; split => //.
    by rewrite elem_of_elements elem_of_union; left.
  + apply/elem_of_list_fmap; exists b; split => //.
    by rewrite elem_of_elements elem_of_union; right.
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

Let saturate σ :=
  (σ.1, σ.2 ⊔ if fsa_final σ.1 then nfa_initial B else ⊥).

Let final σ := nfa_final (saturate σ).2.

Let interp σ := fsa_interp σ.1 ⋅ nfa_elem B ⊔ nfa_interp σ.2.

Let trans x σ := (fsa_trans x σ.1, nfa_trans x σ.2).

Lemma mul_interp_trans_saturate x σ :
  interp (trans x (saturate σ)) ≡
  fsa_interp (fsa_trans x σ.1) ⋅ nfa_elem B ⊔
  nfa_interp (nfa_trans x σ.2) ⊔
  pre_ka_of_bool (fsa_final σ.1) ⋅ nfa_interp (nfa_trans x (nfa_initial B)).
Proof.
rewrite /interp /trans /saturate /=.
rewrite nfa_trans_join nfa_interp_join assoc.
case: fsa_final; rewrite //= ?left_id // left_absorb.
by rewrite nfa_trans_bottom nfa_interp_bottom.
Qed.

Lemma mul_derive_trans_saturate σ :
  ⨆ (map (λ x, f x ⋅ interp (trans x (saturate σ))) (enum Σ)) ≡
  ⨆ (map (λ x, f x ⋅ fsa_interp (fsa_trans x σ.1)) (enum Σ)) ⋅ nfa_elem B ⊔
  ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x σ.2)) (enum Σ)) ⊔
  pre_ka_of_bool (fsa_final σ.1) ⋅
    ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x (nfa_initial B))) (enum Σ)).
Proof.
rewrite join_list_right_dist map_map join_list_left_dist map_map.
rewrite -!join_list_join.
apply: join_list_proper.
apply: (@list_fmap_proper _ equivL) => //.
move=> x _ <-; rewrite mul_interp_trans_saturate !pre_ka_right_dist.
rewrite !assoc.
by case: fsa_final; rewrite /= ?(left_id, right_id, left_absorb, right_absorb).
Qed.

Lemma pre_ka_of_bool_final σ :
  @pre_ka_of_bool T (final σ) ≡
  pre_ka_of_bool (fsa_final σ.1) ⋅
    pre_ka_of_bool (nfa_final (nfa_initial B)) ⊔
  pre_ka_of_bool (nfa_final σ.2).
Proof.
rewrite /final /saturate /= nfa_final_join pre_ka_of_bool_or.
rewrite comm; apply: semi_lattice_proper => //.
case: fsa_final; rewrite /= ?nfa_final_bottom ?left_absorb //.
by rewrite left_id.
Qed.

Program Definition fsa_mul : fsa := {|
  fsa_state := fsa_state A * nfa_state B;
  fsa_elem := fsa_elem A ⋅ nfa_elem B;
  fsa_initial := (fsa_initial A, ⊥);
  fsa_final := final;
  fsa_interp := interp;
  fsa_trans x σ := trans x (saturate σ);
|}.

Next Obligation.
by rewrite /interp /= nfa_interp_bottom right_id fsa_interp_initial.
Qed.

Next Obligation.
move=> σ.
rewrite mul_derive_trans_saturate /interp.
rewrite pre_ka_of_bool_final.
rewrite [_ ⊔ pre_ka_of_bool (fsa_final σ.1) ⋅ _]comm assoc.
rewrite -[pre_ka_of_bool _ ⋅ _ ⊔ _ ⊔ _]assoc.
rewrite [_ ⊔ pre_ka_of_bool (fsa_final σ.1) ⋅ _]comm assoc.
rewrite -pre_ka_right_dist -nfa_derivable nfa_interp_initial !assoc.
rewrite -[_ ⋅ nfa_elem B ⊔ _ ⊔ _]assoc [_ ⊔ _ ⋅ nfa_elem B]comm assoc.
by rewrite -pre_ka_left_dist -fsa_derivable -assoc -nfa_derivable.
Qed.

End FSAMul.

Definition fsa_mul' (A B : fsa) : fsa :=
  fsa_mul A (fsa_to_nfa B).

Section FSAStar.

Variables (A : nfa).
Implicit Types (x : Σ) (σ : option (nfa_state A)).

Let interp σ :=
  pre_ka_of_bool (negb (nfa_final (nfa_initial A))) ⋅
  match σ with
  | Some σA => nfa_interp σA
  | None => 1
  end ⋅ star (nfa_elem A).

Let final σ :=
  negb (nfa_final (nfa_initial A)) &&
  match σ with
  | Some σA => nfa_final σA
  | None => true
  end.

Let elem :=
  pre_ka_of_bool (negb (nfa_final (nfa_initial A))) ⋅
  star (nfa_elem A).

Let trans x σ :=
  Some (nfa_trans x
          match σ with
          | Some σA =>
            (if nfa_final σA then nfa_initial A else ⊥) ⊔ σA
          | None =>
            nfa_initial A
          end).

Lemma star_interp_trans x σ :
  interp (trans x σ) ≡
  if nfa_final (nfa_initial A) then ⊥
  else
    pre_ka_of_bool (match σ with Some σA => nfa_final σA | None => true end) ⋅
    nfa_interp (nfa_trans x (nfa_initial A)) ⋅
    star (nfa_elem A) ⊔
    nfa_interp (nfa_trans x (match σ with Some σA => σA | None => ⊥ end)) ⋅
    star (nfa_elem A).
Proof.
rewrite /interp; case: (nfa_final _); rewrite /= ?left_absorb //.
rewrite left_id; case: σ => [σA|] /=; last first.
  by rewrite left_id nfa_trans_bottom nfa_interp_bottom left_absorb right_id.
case: nfa_final => /=.
- by rewrite nfa_trans_join nfa_interp_join pre_ka_left_dist left_id.
- rewrite nfa_trans_join nfa_trans_bottom nfa_interp_join nfa_interp_bottom.
  by rewrite left_id !left_absorb left_id.
Qed.

Lemma star_derive_trans σ :
  ⨆ (map (λ x, f x ⋅ interp (trans x σ)) (enum Σ)) ≡
  if nfa_final (nfa_initial A) then ⊥
  else match σ with
  | Some σA =>
    if nfa_final σA then
      ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x (nfa_initial A))) (enum Σ)) ⋅
      star (nfa_elem A) ⊔
      ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x σA)) (enum Σ)) ⋅
      star (nfa_elem A)
    else
      ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x σA)) (enum Σ)) ⋅
      star (nfa_elem A)
  | None =>
    ⨆ (map (λ x, f x ⋅ nfa_interp (nfa_trans x (nfa_initial A))) (enum Σ)) ⋅
    star (nfa_elem A)
  end.
Proof.
case final_A: nfa_final.
  rewrite join_list_bottom // => ?.
  case/elem_of_list_fmap => ? [] -> _.
  by rewrite star_interp_trans final_A right_absorb.
case: σ => [σA|] /=; last first.
  rewrite join_list_left_dist map_map.
  apply: join_list_proper.
  apply: (@list_fmap_proper _ equivL) => // ? ? ->.
  rewrite star_interp_trans final_A /= nfa_trans_bottom nfa_interp_bottom.
  by rewrite left_absorb right_id left_id assoc.
case final_σA: nfa_final; last first.
  rewrite join_list_left_dist map_map.
  apply: join_list_proper.
  apply: (@list_fmap_proper _ equivL) => // ? ? ->.
  by rewrite star_interp_trans final_A final_σA /= !left_absorb left_id assoc.
rewrite -pre_ka_left_dist -join_list_join join_list_left_dist map_map.
apply: join_list_proper.
apply: (@list_fmap_proper _ equivL) => // ? ? ->.
rewrite star_interp_trans /= final_A /= final_σA left_id pre_ka_left_dist.
by rewrite pre_ka_right_dist !assoc.
Qed.

Program Definition fsa_star : fsa := {|
  fsa_state := option (nfa_state A);
  fsa_elem := elem;
  fsa_initial := None;
  fsa_final := final;
  fsa_interp := interp;
  fsa_trans := trans;
|}.

Next Obligation.
by rewrite /elem /interp /= right_id.
Qed.

Next Obligation.
move=> σ; rewrite star_derive_trans /final {1}/interp.
case final_A: nfa_final; rewrite /= ?left_absorb ?left_id //.
case: σ=> [σA|] /=; last first.
  rewrite left_id {1}pre_ka_star_unfold -{1}nfa_interp_initial.
  by rewrite nfa_derivable final_A /= left_id.
rewrite nfa_derivable pre_ka_left_dist {1}pre_ka_star_unfold.
rewrite pre_ka_right_dist right_id -!assoc.
apply: semi_lattice_proper => //.
case final_σA: nfa_final; rewrite //= ?left_absorb ?left_id //.
apply: semi_lattice_proper => //.
by rewrite -{1}nfa_interp_initial nfa_derivable final_A left_id.
Qed.

End FSAStar.

Definition fsa_star' A : fsa := fsa_star (fsa_to_nfa A).

Lemma fsa_elem_star' A :
  fsa_final (fsa_initial A) = false → fsa_elem (fsa_star' A) ≡ star (fsa_elem A).
Proof.
by move=> final_A; rewrite /= elements_singleton /= final_A /= left_id.
Qed.

Program Definition fsa_singleton x : fsa := {|
  fsa_state := option bool;
  fsa_elem := f x;
  fsa_initial := None;
  fsa_final σ :=
    match σ return bool with
    | Some b => b
    | _ => false
    end;
  fsa_interp σ :=
    match σ return T with
    | Some b => pre_ka_of_bool b
    | None => f x
    end;
  fsa_trans y σ :=
    match σ return option bool with
    | Some _ => Some false
    | None => Some (bool_decide (x = y))
    end;
|}.

Next Obligation. by rewrite /=. Qed.

Next Obligation.
move=> x [[]|] /=.
- rewrite join_list_bottom ?right_id // => _ /elem_of_list_fmap [y [] -> _].
  by rewrite right_absorb.
- rewrite join_list_bottom ?right_id // => _ /elem_of_list_fmap [y [] -> _].
  by rewrite right_absorb.
- rewrite left_id.
  have <-: f x ⋅ 1 ≡ f x by exact: right_id.
  apply (anti_symm _).
  + apply/sqsubseteq_join_list/elem_of_list_fmap.
    exists x; split; last exact: elem_of_enum.
    by rewrite bool_decide_eq_true_2.
  + apply/join_list_sqsubseteq=> _ /elem_of_list_fmap [y [] -> _].
    case: bool_decide_reflect => [<- //|ne].
    rewrite right_absorb /=; exact: bottom_sqsubseteq.
Qed.

Definition fsa_one :=
  fsa_star (fsa_to_nfa fsa_bottom).

Lemma fsa_elem_one : fsa_elem fsa_one ≡ 1.
Proof. by rewrite /= elements_singleton /= star_bottom left_id. Qed.

Definition fsa_mul_list (As : list fsa) : fsa :=
  foldr fsa_mul' fsa_one As.

Lemma fsa_elem_mul_list As : fsa_elem (fsa_mul_list As) ≡ ∏ (map fsa_elem As).
Proof. by elim: As => /= [|A As ->]; rewrite // -fsa_elem_one. Qed.


Definition fsa_trans_s (A : fsa) (s : list Σ) (σ : fsa_state A) :=
  foldl (flip fsa_trans) σ s.

Lemma fsa_trans_s_cons (A : fsa) (x : Σ) (s : list Σ) (σ : fsa_state A) :
  fsa_interp (fsa_trans_s (x :: s) σ) ≡ fsa_interp (fsa_trans_s s (fsa_trans x σ)).
Proof.
  rewrite //=.
Qed.

Lemma fsa_trans_s_app (A : fsa) (x : Σ) (s : list Σ) (σ : fsa_state A) :
  fsa_interp (fsa_trans_s (s ++ [x]) σ) ≡ fsa_interp (fsa_trans x (fsa_trans_s s σ)).
Proof.
elim: s σ => [// | /= x' s' IH σ].
by rewrite IH.
Qed.


Definition string_match_at A (σ : fsa_state A) s :=
  fsa_final (fsa_trans_s s σ).

Definition string_match (A : fsa) (s : list Σ) :=
  string_match_at (fsa_initial A) s.

Definition ka_of_string s := ∏ (map f s).

Lemma ka_of_string_concat_l ys (y : Σ) :
  ka_of_string ys ⋅ f y ≡ ka_of_string (ys ++ [y]).
Proof.
rewrite /ka_of_string;
elim: ys => /= [|y' ys IHys]; first by rewrite ?right_id ?left_id.
by rewrite -assoc; rewrite IHys.
Qed.

Lemma ka_of_string_concat_r ys (y : Σ) :
  f y ⋅ ka_of_string ys ≡ ka_of_string (y :: ys).
Proof. rewrite //=. Qed.


(* TODO: this Arguments decl conflicts with the ∏/previous mul_list uses. *)
Arguments mul_list {_}.

Definition sum_terms_lt_k_at A (σ : fsa_state A) k :=
  ⨆ (map ∏
  (map
    (map f)
    (filter (string_match_at σ) (@enum_list_lt Σ _ _ k))
  )
).

Definition sum_terms_lt_k A k :=
  sum_terms_lt_k_at (fsa_initial A) k.


Definition sum_terms_eq_k_at A (σ : fsa_state A) k :=
  ⨆ (map ∏ (map (map f) (filter (string_match_at σ) (@enum_list_eq Σ _ _ k)))).

Definition sum_terms_eq_k A k := sum_terms_eq_k_at (fsa_initial A) k.

Definition string_suffix_at A (σ : fsa_state A) s :=
  fsa_interp (fsa_trans_s s σ).

Definition string_suffix A s :=
  string_suffix_at (fsa_initial A) s.

Definition string_suffix_term_at A (σ : fsa_state A) s :=
  (ka_of_string s) ⋅ fsa_interp (fsa_trans_s s σ).

Definition sum_suffix_terms_k_at A (σ : fsa_state A) k :=
  ⨆ (map (string_suffix_term_at σ) (@enum_list_eq Σ _ _ k)).

Lemma join_map_mul_dist {B : Type} (t1 t2 t3 : B -> T) (ls : list B):
  ⨆ (map (λ s, t1 s ⋅ (t2 s ⊔ t3 s)) ls)
  ≡ (⨆ (map (λ s, t1 s ⋅ t2 s) ls))
    ⊔ (⨆ (map (λ s, t1 s ⋅ t3 s) ls)).
Proof.
assert (G : ⨆ (map (λ s, (t1 s) ⋅ (t2 s ⊔ t3 s)) ls) ≡
            ⨆ (map (λ s, (t1 s ⋅ t2 s) ⊔ t1 s ⋅t3 s) ls)).
{
  apply: join_list_proper.
  apply: (@list_fmap_proper _ equivL) => //.
  move=> x y ->.
  apply pre_ka_right_dist.
  (* QUEST: type messages on this: *)
  (* apply ka_mul_join_right. *)
}
rewrite {}G.
apply join_list_join.
Qed.

Lemma string_derive_one_more_at A (σ : fsa_state A) k :
  ⨆ (map
     (λ s, ka_of_string s ⋅ fsa_interp (fsa_trans_s s σ))
     (enum_list_eq k)
    )
  ≡ ⨆ (map
       (λ s, ka_of_string s ⋅ (
        pre_ka_of_bool (fsa_final (fsa_trans_s s σ))
        ⊔ ⨆ (map
             (λ x,
              f x ⋅ fsa_interp (fsa_trans x (fsa_trans_s s σ)))
             (enum Σ))
        ))
    (enum_list_eq k)
  ).
Proof.
apply: join_list_proper.
(* QUEST: what is equivL? *)
apply: (@list_fmap_proper _ equivL) => //.
move=> x y ->.
by rewrite fsa_derivable.
Qed.

Lemma sum_terms_lt_S_k_at A (σ : fsa_state A) k :
sum_terms_lt_k_at σ (S k) ≡ sum_terms_lt_k_at σ k ⊔ sum_terms_eq_k_at σ k.
Proof.
rewrite /sum_terms_lt_k_at /sum_terms_eq_k_at {1}/enum_list_lt.
replace (S k) with (k + 1); last by lia.
(* QUEST: there are some annoying rewrites/unfolds here...is this ok? *)
by rewrite /string_match seq_app //= flat_map_app
           filter_app flat_map_enum_list_eq_id !map_map
           map_app join_list_app /enum_list_lt.
Qed.

Lemma join_elim_left (t1 t2 t3 : T) : t2 ≡ t3 -> t1 ⊔ t2 ≡ t1 ⊔ t3.
Proof.
by move=> <-.
Qed.

Lemma sum_terms_lt_k__to__S_k_at A (σ : fsa_state A) k :
  sum_terms_lt_k_at σ k ⊔ ⨆ (
    map (λ s : list Σ, ka_of_string s ⋅ pre_ka_of_bool (fsa_final (fsa_trans_s s σ))) (enum_list_eq k)
  ) ≡ sum_terms_lt_k_at σ (S k).
Proof.
rewrite sum_terms_lt_S_k_at. apply join_elim_left.
rewrite /sum_terms_eq_k_at /string_match_at.
elim: (enum_list_eq k) => [| en1 en' IHen]; first rewrite //=.
rewrite /=; case en1Final: (fsa_final (fsa_trans_s en1 σ));
rewrite filter_cons en1Final /ka_of_string.
- rewrite ?right_id /=; exact: join_elim_left.
- rewrite ?right_absorb ?left_id //=.
Qed.


Lemma fsa_elem_k_decomp_gen A (σ : fsa_state A) (k : nat):
  fsa_interp σ ≡ sum_terms_lt_k_at σ k ⊔ sum_suffix_terms_k_at σ k.
Proof.
elim: k => [| k IHk] /=;
first by rewrite /sum_terms_lt_k_at /sum_suffix_terms_k_at
             /string_suffix_term_at /ka_of_string /= ?left_id ?right_id.
rewrite {}IHk {1}/sum_suffix_terms_k_at /string_suffix_at.
rewrite string_derive_one_more_at join_map_mul_dist
        assoc sum_terms_lt_k__to__S_k_at.
apply join_elim_left.
rewrite /sum_suffix_terms_k_at /string_suffix_term_at.
apply (anti_symm _); apply join_list_sqsubseteq;
move=> _ /elem_of_list_fmap [xs [-> Hxs]].
- rewrite join_list_right_dist map_map.
  apply join_list_sqsubseteq.
  move=> _ /elem_of_list_fmap [x [-> Hxin]].
  rewrite assoc ka_of_string_concat_l -fsa_trans_s_app.
  move: Hxs => /elem_of_enum_list_eq;
  have {x Hxin xs} [x [xs [-> ->]]] := destruct_list_app_len x xs;
  rewrite enum_list_eq_Sn map_map => /elem_of_enum_list_eq Hxs.
  apply sqsubseteq_join_list; apply elem_of_list_fmap.
  exists (x, xs); split; [done | apply elem_of_concat].
  exists (map (pair x) (enum_list_eq k)).
  split; apply elem_of_list_fmap.
  + exists x; split; [done | exact: elem_of_enum].
  + exists xs; done.
- move: Hxs;
  rewrite /= => {xs} /elem_of_list_fmap [xpair [-> Hxpair]].
  move: Hxpair; rewrite /all_pairs => {xpair}
    /elem_of_concat [_ [
      /elem_of_list_fmap [x [-> Hxenum]]
      /elem_of_list_fmap [xs [-> Hxs]]
    ]].
  move: Hxs => /elem_of_enum_list_eq.
  have {x xs Hxenum} [x [xs [-> ->]]] := destruct_list_cons_len x xs.
  move=> /elem_of_enum_list_eq Hxs.
  eapply sqsubseteq_join_list';
  first by rewrite elem_of_list_fmap; exists xs; done.
  rewrite -ka_of_string_concat_l -assoc fsa_trans_s_app.
  rewrite join_list_right_dist map_map.
  apply sqsubseteq_join_list; apply elem_of_list_fmap.
  exists x; split; auto.
  exact: elem_of_enum.
Qed.


End Automata.
(* Set Printing Implicit. *)
Print fsa.
Print pre_ka.

Global Arguments fsa_one {Σ _ _ _ _}.
Global Arguments fsa_singleton {Σ _ _ _ _}.
Global Arguments fsa Σ {_ _} T.
Global Arguments fsa_mul' {Σ _ _ _ _}.

Section FSAKATerm.

Context (T : monoid) `{!FinGenMonoid T} `{!IsOne T}.

Fixpoint finite_state (e : ka_term T) : bool :=
  match e with
  | Unit _ => true
  | ka_term_join e1 e2 => finite_state e1 && finite_state e2
  | ka_term_bottom => true
  | ka_term_mul e1 e2 => finite_state e1 && finite_state e2
  | ka_term_star e => negb (has_one e) && finite_state e
  end.

Lemma finite_stateP e :
  finite_state e →
  ∃ A : fsa (generator T) (ka_term T) (λ x, Unit (generator_interp x)),
    e ≡ fsa_elem A.
Proof.
elim: e => /=.
- move=> s _.
  have [xs Exs] := generate s; exists (fsa_mul_list (map fsa_singleton xs)).
  rewrite fsa_elem_mul_list map_map Exs monoid_morphism_mul_list map_map.
  by apply: monoid_morphism_proper; apply: (@Proper_map' (eq_setoid (generator T)) _).
- move=> _. by exists (fsa_bottom _) => /=.
- move=> e1 IH1 e2 IH2 /andb_True [H1 H2].
  have [A1 E1] := IH1 H1.
  have [A2 E2] := IH2 H2.
  exists (fsa_join A1 A2). by rewrite /= -E1 -E2.
- move=> e1 IH1 e2 IH2 /andb_True [H1 H2].
  have [A1 E1] := IH1 H1.
  have [A2 E2] := IH2 H2.
  exists (fsa_mul A1 (fsa_to_nfa A2)).
  by rewrite /= -E1 -E2.
- move=> e1 IH1 /andb_True [/negb_True /Is_true_false H1 H2].
  have {IH1 H2} [A1 E1] := IH1 H2; exists (fsa_star' A1).
  rewrite fsa_elem_star' -?E1 //; case E: fsa_final => //.
  have ?: has_one e1 = true; last by congruence.
  apply/has_oneP; rewrite E1 -fsa_interp_initial.
  rewrite fsa_derivable E /=; exact: sqsubseteq_join_left.
Qed.

End FSAKATerm.

Section Derivatives.

Context (T : setoid) `{!EqDecision T, Finite T}.
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




(* Record fsa : Type := {
  fsa_state : setoid;
  fsa_state_leibniz : LeibnizEquiv fsa_state;
  fsa_state_eq_dec : EqDecision fsa_state;
  fsa_state_finite : Finite fsa_state;
}. *)

End Derivatives.

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
by rewrite app_length.
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

Lemma bounded_output_with_star k e :
  bounded_output_with k e →
  left_nonempty e →
  bounded_output_with (2 * k) (star e).
Proof.
move=> Hbo Hne sl sr /l_alt.
rewrite pre_ka_morphism_star.
case=> n; revert sl sr; elim: n => [|n IH] sl sr /=.
- move=> [/= /leibniz_equiv_iff esl /leibniz_equiv_iff esr].
  subst. simpl. lia.
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
exists (length s.2).
move=> sl sr /l_alt /= [/leibniz_equiv_iff -> /leibniz_equiv_iff ->].
nia.
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

