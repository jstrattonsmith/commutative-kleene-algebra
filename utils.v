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

Section NSteps.

Lemma nsteps_0_inv {A} {R : relation A} {a b} : nsteps R 0 a b → a = b.
Proof. by move=> H; inversion H. Qed.

Lemma nsteps_inv_l {A} {R : relation A} {n a b} :
  nsteps R (S n) a b → ∃ c, R a c ∧ nsteps R n c b.
Proof. by move=> H; inversion H; eauto. Qed.

Lemma nsteps_det {A} {R : relation A} n :
  (∀ a b1 b2, R a b1 → R a b2 → b1 = b2) →
  (∀ a b1 b2, nsteps R n a b1 → nsteps R n a b2 → b1 = b2).
Proof. Admitted.

End NSteps.

Global Arguments nsteps_inv_r {_ _ _ _ _}.
Global Arguments nsteps_add_inv {_ _ _ _ _ _}.
Global Arguments rtc_nsteps_1 {_ _ _ _}.
Global Arguments rtc_nsteps_2 {_ _ _ _ _}.

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
