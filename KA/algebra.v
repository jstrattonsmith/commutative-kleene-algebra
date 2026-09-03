(* The algebraic hierarchy KA/ is built on: `setoid` -> `monoid` (via
   `MonoidMixin`) -> `semi_lattice` (via `SemiLatticeMixin`), each with a
   matching morphism class (`MonoidMorphism`, `SemiLatticeMorphism`), plus
   concrete instances for `bool`, `option`, `list`, and products. Also
   defines `MonoidGen`/`SizedMonoid` for generator structures. This is the
   base scaffolding every later file in KA/ and CKAUndec/ builds on. *)

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

From kacc Require Import KA.utils.

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

Section OptionSetoid.

Variable T : setoid.

Canonical Structure option_setoid :=
  @Setoid (option T) (≡) (option_equivalence _).

End OptionSetoid.

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

Definition mul_list {A} (f : A → T) (xs : list A) : T :=
  foldr (λ a acc, f a ⋅ acc) 1 xs.

Global Instance mul_list_proper {A} :
  Proper (pointwise_relation A (≡) ==> (=) ==> (≡)) mul_list.
Proof.
by move=> f g fg xs _ <-; elim: xs => //= x xs <-; rewrite -fg.
Qed.

Lemma mul_list_one {A} (f : A → T) xs :
  (∀ a, a ∈ xs → f a ≡ 1) →
  mul_list f xs ≡ 1.
Proof.
elim: xs => //= a xs IH xs_1.
rewrite (xs_1 a) ?elem_of_cons ?left_id; eauto.
rewrite IH // => a' a'_xs; apply: xs_1.
by rewrite elem_of_cons; eauto.
Qed.

Lemma mul_list_app {A} (f : A → T) ls ls' :
  mul_list f (ls ++ ls') ≡
  mul_list f ls ⋅ mul_list f ls'.
Proof.
elim: ls => [|l ls IHls];
  first by rewrite //= ?left_id.
by rewrite //= {}IHls assoc.
Qed.

Lemma mul_list_map {A B} (f : A → T)
    (g : B → A) xs :
  mul_list f (map g xs) = mul_list (f ∘ g) xs.
Proof. by elim: xs => //= x xs ->. Qed.

End MonoidTheory.

Notation "x ^ n" := (power x n) : ka_scope.
Arguments mul_list {_ _}.
Notation "'∏' x ∈ xs , e" := (mul_list (λ x, e) xs)
  (at level 36, x binder, xs at level 99,
   e at level 60, right associativity) : ka_scope.

Class MonoidMorphism (T S : monoid) (f : T → S) := {
  monoid_morphism_proper :: Proper ((≡) ==> (≡)) f;
  monoid_morphism_one : f 1 ≡ 1;
  monoid_morphism_mul : ∀ x y, f (x ⋅ y) ≡ f x ⋅ f y;
}.

Lemma monoid_morphism_mul_list `{MonoidMorphism T1 T2 f}
    {A} (g : A → T1) (xs : list A) :
  f (mul_list g xs) ≡ mul_list (f ∘ g) xs.
Proof.
elim: xs => //= [|x xs IH].
- by rewrite monoid_morphism_one.
- by rewrite monoid_morphism_mul IH.
Qed.

Lemma monoid_morphism_power `{MonoidMorphism T1 T2 f} (x : T1) n :
  f (x ^ n) ≡ (f x) ^ n.
Proof.
elim: n => [|n IH] /=.
- exact: monoid_morphism_one.
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

Class MonoidGen (G : Type) (T : monoid) := {
  generator_interp : G → T;
  generate : T → list G;
  generateP :
    ∀ x, x ≡ ∏ g ∈ generate x, generator_interp g;
}.

Global Hint Mode MonoidGen - ! : typeclasses.

Class SizedMonoid (G : Type) (T : monoid) `{!MonoidGen G T} := {
  sized_monoid :
    ∀ (gs : list G) (x : T),
      x ≡ (∏ g ∈ gs, generator_interp g) →
      length gs = length (generate x);
}.

Arguments SizedMonoid G T {_}.

Section MSize.

Context {G : Type} {T : monoid} `{!MonoidGen G T, !SizedMonoid G T}.

Definition msize (x : T) : nat :=
  length (generate ( x)).

Lemma msize_gen (gs : list G) :
  msize (∏ g ∈ gs, generator_interp g) = length gs.
Proof. symmetry. exact: sized_monoid. Qed.

Lemma msize_one : msize 1 = 0.
Proof. exact: (msize_gen []). Qed.

Lemma msize_mul (x y : T) : msize (x ⋅ y) = msize x + msize y.
Proof.
rewrite /msize.
have Hcat :
  x ⋅ y ≡ ∏ g ∈ generate x ++ generate y, generator_interp g.
{ rewrite mul_list_app -(generateP x) -(generateP y) //. }
have := @sized_monoid _ _ _ _ (generate x ++ generate y) _ Hcat.
rewrite length_app => <-. lia.
Qed.

Lemma msize_proper (x y : T) : x ≡ y → msize x = msize y.
Proof.
move=> Hxy. rewrite /msize.
have Hx := @sized_monoid _ _ _ _ (generate x) y
              (transitivity (symmetry Hxy) (generateP x)).
by rewrite Hx.
Qed.

Lemma msize_generator (g : G) : msize (generator_interp g) = 1%nat.
Proof.
rewrite /msize.
have Hgen :
  generator_interp g ≡ ∏ g' ∈ [g], generator_interp g'.
{ simpl. by rewrite right_id. }
have H := @sized_monoid _ _ _ _ [g] _ Hgen.
simpl in H. rewrite H //.
Qed.

End MSize.

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

Global Instance map_monoid_morphism
    {T S : setoid} (f : T → S) `{!Proper ((≡) ==> (≡)) f} :
  MonoidMorphism (map f).
Proof.
split => //.
- solve_proper.
- by move=> x y; rewrite map_app.
Qed.

Section ListFinGen.

Context {T : setoid} `{!LeibnizEquiv T}.

Global Program Instance list_fin_gen : MonoidGen T (list_monoid T) := {|
  generator_interp x := [x];
  generate xs := xs;
|}.
Next Obligation.
move=> xs; symmetry. by elim: xs => //= x xs' ->.
Qed.

Lemma list_gen_length (gs : list T) :
  (∏ g ∈ gs,
     generator_interp (T := list_monoid T) g) = gs.
Proof. by elim: gs => //= g gs' ->. Qed.

Global Instance list_sized_monoid : SizedMonoid T (list_monoid T).
Proof.
constructor => gs xs /leibniz_equiv_iff Hxs.
by rewrite list_gen_length in Hxs; subst xs.
Qed.

End ListFinGen.

Global Instance mul_list_monoid_morphism (T : monoid) :
  MonoidMorphism (@mul_list T T id).
Proof.
split => //.
- by move=> l1 l2; elim: l1 l2 / =>
    //= x1 x2 l1 l2 -> _ ->.
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

Context `{!MonoidGen G1 T1, !MonoidGen G2 T2}.

Global Program Instance prod_fin_gen : MonoidGen (G1 + G2) (T1 * T2)%type := {|
  generator_interp (x : G1 + G2) :=
    match x return T1 * T2 with
    | inl x => (generator_interp x, 1)
    | inr x => (1, generator_interp x)
    end;
  generate p := map inl (generate p.1) ++ map inr (generate p.2);
|}.
Next Obligation.
case=> x y /=.
rewrite mul_list_app; split; rewrite /=;
  rewrite -?/(fst _) -?/(snd _);
  rewrite ?(monoid_morphism_mul_list)
          !mul_list_map /=.
- rewrite -(generateP x).
  by rewrite mul_list_one ?right_id //
    => ? /elem_of_list_fmap [? [] -> _].
- rewrite -(generateP y).
  by rewrite mul_list_one ?left_id //
    => ? /elem_of_list_fmap [? [] -> _].
Qed.

Context {Hsz1 : SizedMonoid G1 T1} {Hsz2 : SizedMonoid G2 T2}.

Definition sum_lefts (gs : list (G1 + G2)) : list G1 :=
  omap (λ x, match x with inl g => Some g | inr _ => None end) gs.

Definition sum_rights (gs : list (G1 + G2)) : list G2 :=
  omap (λ x, match x with inl _ => None | inr g => Some g end) gs.

Lemma sum_lefts_rights_length (gs : list (G1 + G2)) :
  length gs = length (sum_lefts gs) + length (sum_rights gs).
Proof. elim: gs => [|[g|g] gs IH] //=; lia. Qed.

Lemma prod_gen_proj1 (gs : list (G1 + G2)) :
  fst (∏ g ∈ gs, generator_interp g) ≡
  ∏ g ∈ sum_lefts gs, generator_interp g.
Proof.
rewrite (monoid_morphism_mul_list (f := fst)).
elim: gs => [|[g|g] gs IH] //=.
- by rewrite IH.
- by rewrite IH left_id.
Qed.

Lemma prod_gen_proj2 (gs : list (G1 + G2)) :
  snd (∏ g ∈ gs, generator_interp g) ≡
  ∏ g ∈ sum_rights gs, generator_interp g.
Proof.
rewrite (monoid_morphism_mul_list (f := snd)).
elim: gs => [|[g|g] gs IH] //=.
- by rewrite IH left_id.
- by rewrite IH.
Qed.

Global Instance prod_sized_monoid : SizedMonoid (G1 + G2) (prod_monoid T1 T2).
Proof.
constructor => gs [x y] [/= Hx Hy].
have Hxe :
  x ≡ ∏ g ∈ sum_lefts gs, generator_interp g.
{ rewrite -prod_gen_proj1 Hx //. }
have Hye :
  y ≡ ∏ g ∈ sum_rights gs, generator_interp g.
{ rewrite -prod_gen_proj2 Hy //. }
rewrite sum_lefts_rights_length.
rewrite (@sized_monoid _ _ _ Hsz1 (sum_lefts gs) x Hxe).
rewrite (@sized_monoid _ _ _ Hsz2 (sum_rights gs) y Hye).
set gxy := generate (x, y).
have Hgxy := generateP (x, y).
have [/= Hgx Hgy] := Hgxy.
have Hlx := @sized_monoid _ _ _ Hsz1 (sum_lefts gxy) x
              (transitivity Hgx (prod_gen_proj1 gxy)).
have Hly := @sized_monoid _ _ _ Hsz2 (sum_rights gxy) y
              (transitivity Hgy (prod_gen_proj2 gxy)).
by rewrite -Hlx -Hly sum_lefts_rights_length.
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

Definition join_list {A} (f : A → T) (xs : list A) : T :=
  foldr (λ a acc, f a ⊔ acc) ⊥ xs.

Global Instance join_list_proper {A} :
  Proper (pointwise_relation A (≡) ==> (=) ==> (≡))
    (@join_list A).
Proof.
move=> f g Hfg xs _ <-.
by elim: xs => //= x xs <-; rewrite -Hfg.
Qed.

Lemma join_list_ext {A} (f g : A → T) xs :
  (∀ a, a ∈ xs → f a ≡ g a) →
  join_list f xs ≡ join_list g xs.
Proof.
elim: xs => [|x xs IH] //= H.
rewrite (H x (elem_of_list_here _ _)); f_equiv.
apply: IH => a Ha.
apply H. exact: elem_of_list_further.
Qed.

Lemma join_list_app {A} (f : A → T) xs ys :
  join_list f (xs ++ ys) ≡
  join_list f xs ⊔ join_list f ys.
Proof.
elim: xs => [|x xs IH] //=.
- by rewrite left_id.
- by rewrite IH assoc.
Qed.

Lemma join_list_sqsubseteq {A} (f : A → T)
    (xs : list A) y :
  join_list f xs ⊑ y ↔
  ∀ a, a ∈ xs → f a ⊑ y.
Proof.
elim: xs => [|a xs IH] /=; split.
- by move=> _ ?; rewrite elem_of_nil.
- move=> _; exact: bottom_sqsubseteq.
- rewrite join_sqsubseteq;
    case=> ay /IH asy a'.
  by rewrite elem_of_cons; case=> [->|]; eauto.
- rewrite join_sqsubseteq IH => asy; split.
  + by apply asy; rewrite elem_of_cons; eauto.
  + by move=> a' a'_xs; apply asy;
      rewrite elem_of_cons; eauto.
Qed.

Lemma sqsubseteq_join_list {A} (f : A → T)
    (xs : list A) a :
  a ∈ xs → f a ⊑ join_list f xs.
Proof.
move: a; apply/join_list_sqsubseteq. done.
Qed.

Lemma sqsubseteq_join_list' {A} (f : A → T)
    (xs : list A) a a' :
  a' ∈ xs → f a ⊑ f a' →
  f a ⊑ join_list f xs.
Proof.
move=> Helem ->; by apply sqsubseteq_join_list.
Qed.

Lemma list_subseteq_join_list {A} (f : A → T)
    (xs ys : list A) :
  xs ⊆ ys → join_list f xs ⊑ join_list f ys.
Proof.
move=> xs_ys; apply/join_list_sqsubseteq =>
  a /xs_ys a_ys.
exact: sqsubseteq_join_list.
Qed.

Lemma join_list_assoc {A} (f : A → T)
    (xss : list (list A)) :
  join_list (λ xs, join_list f xs) xss ≡
  join_list f (concat xss).
Proof.
elim: xss => [|xs xss IH] //=.
by rewrite join_list_app IH.
Qed.

Lemma join_list_bottom {A} (f : A → T) xs :
  (∀ a, a ∈ xs → f a ≡ ⊥) →
  join_list f xs ≡ ⊥.
Proof.
move=> const_a; apply: (anti_symm _).
- by rewrite join_list_sqsubseteq =>
    a a_xs; rewrite (const_a _ a_xs).
- exact: bottom_sqsubseteq.
Qed.

Global Instance join_mono : Proper ((⊑@{T}) ==> (⊑) ==> (⊑)) (⊔).
Proof.
move=> x1 x2 x12 y1 y2 y12; rewrite join_sqsubseteq; split.
- by etransitivity; last exact: sqsubseteq_join_left.
- by etransitivity; last exact: sqsubseteq_join_right.
Qed.

Global Instance join_flip_mono :
  Proper (flip (⊑@{T}) ==> flip (⊑) ==> flip (⊑)) (⊔).
Proof. by move=> x1 x2 x12 y1 y2 y12; f_equiv. Qed.

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

Arguments join_list {_ _}.
Notation "'⨆' x ∈ xs , e" := (join_list (λ x, e) xs)
  (at level 36, x binder, xs at level 99,
   e at level 60, right associativity) : ka_scope.

Lemma join_list_map {T : semi_lattice} {A B}
    (f : A → T) (g : B → A) xs :
  join_list f (map g xs) = join_list (f ∘ g) xs.
Proof. by elim: xs => //= x xs ->. Qed.

Lemma join_list_join {T : Type} {S : semi_lattice}
    (f1 : T → S) (f2 : T → S) (xs : list T) :
  (⨆ x ∈ xs, f1 x ⊔ f2 x) ≡
  (⨆ x ∈ xs, f1 x) ⊔ (⨆ x ∈ xs, f2 x).
Proof.
elim: xs => //= [|x xs IH];
  first by rewrite right_id.
rewrite IH [in X in _ ≡ X]assoc
  -[(f1 x ⊔ _) ⊔ f2 x]assoc.
by rewrite [join_list _ _ ⊔ f2 x]comm !assoc.
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

Global Instance semi_lattice_morphism_flip_mono : Proper (flip (⊑) ==> flip (⊑)) f.
Proof. move=> ???; exact: semi_lattice_morphism_sqsubseteq_proper. Qed.

Lemma semi_lattice_morphism_join_list {A}
    (g : A → T) (xs : list A) :
  f (join_list g xs) ≡ join_list (f ∘ g) xs.
Proof.
elim: xs => /= [|x xs IH];
  rewrite ?semi_lattice_morphism_bottom //.
by rewrite semi_lattice_morphism_join IH.
Qed.

End SemiLatticeMorphismTheory.

