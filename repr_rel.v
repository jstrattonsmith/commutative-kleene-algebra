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

From kacc Require Import utils algebra pre_ka lang automata.

Section RepresentableRelations.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Implicit Types (e : ka_term (list T * list T)) (L : ka_term (list T)).
Implicit Types (s : list T).

Definition dpseudo_top : ka_term (list T * list T) :=
  ka_term_diag pseudo_top.

Definition mismatch : ka_term (list T * list T) :=
  let diffs := filter (λ '(x, y), bool_decide (x ≠ y)) (enum (T * T)) in
  ⨆ (map (λ '(x, y), Unit ([x], [y])) diffs).

(** Lemma 33 (normal form): If two lists diverge (share a common prefix
    then have different next characters), their pairing factors through diff. *)

Lemma dpseudo_top_absorb s : Unit (s, s) ⋅ dpseudo_top ⊑ dpseudo_top.
Proof.
have -> : Unit (s, s) ≡ ka_term_diag (Unit s) by [].
by rewrite -monoid_morphism_mul pseudo_top_absorb.
Qed.

Lemma dpseudo_top_absorb_list (σ : list (list T)) :
  ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ dpseudo_top ⊑ dpseudo_top.
Proof.
rewrite /= join_list_left_dist map_map join_list_sqsubseteq.
move=> _ /elem_of_list_fmap [xs [] -> ?].
have -> : Unit (xs, xs) ≡ ka_term_diag (Unit xs) by [].
by rewrite -monoid_morphism_mul pseudo_top_absorb.
Qed.

Lemma unit_le_mismatch (x x' : T) : x ≠ x' → Unit ([x], [x']) ⊑ mismatch.
Proof.
move=> Hne. rewrite /mismatch.
apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
exists (x, x'); split => //.
apply/elem_of_list_filter; split; last exact: elem_of_enum.
by apply/Is_true_true/bool_decide_eq_true.
Qed.

Lemma le_mismatch_conv s s' :
  Unit (s, s') ⊑ mismatch →
  ∃ x x', x ≠ x' ∧ s = [x] ∧ s' = [x'].
Proof. Admitted.

Lemma sqsubseteq_dpseudo_top s s' :
  Unit (s, s') ⊑ dpseudo_top ↔ s = s'.
Proof. Admitted.

Lemma mismatch_unit (x x' : T) :
  x ≠ x' → Unit ([x], [x']) ⊑ dpseudo_top ⋅ mismatch.
Proof.
move=> Hne.
rewrite -(left_id 1 (⋅) (Unit ([x], [x']))).
apply: pre_ka_mul_mono; last exact: unit_le_mismatch Hne.
have -> : (1 : ka_term _) ≡ ka_term_diag (1 : ka_term (list T)) by [].
rewrite -monoid_morphism_one.
exact: semi_lattice_morphism_sqsubseteq_proper (pre_ka_one_star _).
Qed.

(* TODO: Find better name *)
Lemma list_diverge s s' :
  ¬ (∃ t, s' = s ++ t) →
  ¬ (∃ t, s = s' ++ t) →
  Unit (s, s') ⊑ dpseudo_top ⋅ mismatch ⋅ pseudo_top.
Proof.
elim: s s' => [|x s IH] [|x' s'] Hns Hns'.
- exfalso. apply: Hns. by exists [].
- exfalso. apply: Hns. by exists (x' :: s').
- exfalso. apply: Hns'. by exists (x :: s).
- case: (decide (x = x')) Hns Hns' => [-> Hns Hns'|Hne Hns Hns'].
  + (* Same head: recurse *)
    have Hns1 : ¬ (∃ t, s' = s ++ t).
    { move=> [t Ht]; apply: Hns; exists t; rewrite /mul /= Ht //. }
    have Hns1' : ¬ (∃ t, s = s' ++ t).
    { move=> [t Ht]; apply: Hns'; exists t; rewrite /mul /= Ht //. }
    (* Unit(x::s, x::s') = Unit([x],[x]) ⋅ Unit(s, s') *)
    have Hsplit : Unit (x' :: s, x' :: s') ≡ Unit ([x'], [x']) ⋅ Unit (s, s').
    { have -> : (x' :: s, x' :: s') = ([x'], [x']) ⋅ (s, s') by done.
      by rewrite monoid_morphism_mul. }
    etransitivity.
    { rewrite Hsplit. reflexivity. }
    etransitivity.
    { apply: pre_ka_mul_mono; [reflexivity | exact: IH _ Hns1 Hns1']. }
    by rewrite !assoc dpseudo_top_absorb.
  + (* Different heads: divergence *)
    have Hsplit : Unit (x :: s, x' :: s') ≡ Unit ([x], [x']) ⋅ Unit (s, s').
    { have -> : (x :: s, x' :: s') = ([x], [x']) ⋅ (s, s') by done.
      by rewrite monoid_morphism_mul. }
    etransitivity.
    { rewrite Hsplit. reflexivity. }
    apply: pre_ka_mul_mono.
    * exact: mismatch_unit Hne.
    * exact: unit_le_pseudo_top.
Qed.



(** A pair (L, L ++ suffix) where left is a strict prefix of
    right cannot be in dpseudo_top ⋅ mismatch ⋅ pseudo_top.
    The mismatch requires differing characters at the same
    position, but a prefix relation has no such position. *)

(** A pair (L, L ++ suffix) where left is a strict prefix
    of right cannot be in dpseudo_top ⋅ mismatch ⋅ pseudo_top.

    Proof sketch: the language of this term contains only
    pairs (w++[x]++w1, w++[y]++w2) where x ≠ y. But
    for (L, L++suffix), the strings share a common prefix
    of length |L|, so any factoring gives x = y at the
    divergence point — contradiction. *)

Lemma prefix_not_in_mismatch s suffix :
  suffix ≠ [] →
  ¬ Unit (s, s ++ suffix) ⊑ dpseudo_top ⋅ mismatch ⋅ pseudo_top.
Proof.
(* The pair (s, s ++ suffix) has s as a prefix of
   s ++ suffix. Since list_diverge only produces pairs
   where NEITHER is a prefix of the other, and its
   image covers dpseudo_top ⋅ mismatch ⋅ pseudo_top,
   we get a contradiction. *)
Admitted.

Lemma in_dpseudo_top_inj2 sl sr (e : ka_term (list T)) :
  Unit (sl, sr) ⊑ dpseudo_top ⋅ ka_term_inj2 e →
  ∃ suffix, sr = sl ++ suffix ∧ Unit suffix ⊑ e.
Proof. Admitted.

(** Lifting a finite set of strings to a KA term. *)

Definition strings_r (σ : list (list T)) : ka_term (list T * list T) :=
  ⨆ (map (λ xs, Unit (1, xs)) σ).

Record repr_rel e L : Type := {
  repr_rel_dom : ka_term_proj1 e ⊑ L;
  repr_rel_cod : ka_term_proj2 e ⊑ L;
  next : list T → list (list T);
  next_spec : ∀ sl sr, sr ∈ next sl ↔ Unit (sl, sr) ⊑ e;
  residue : ka_term (list T * list T);
  expand_rel :
    ∀ xs : list T,
      Unit xs ⊑ L →
      Unit (1, xs) ⋅ e ⊑
        Unit (xs, xs) ⋅ strings_r (next xs)
        ⊔ dpseudo_top ⋅ mismatch ⋅ residue;
}.

(** Next function: image of a set of strings under a representable relation. *)

Section ReprRelIteration.

Variable e : ka_term (list T * list T).
Variable L : ka_term (list T).
Variable R : repr_rel e L.

Definition next_set (σ : list (list T)) : list (list T) :=
  flat_map (next R) σ.

Definition next_iter (n : nat) (σ : list (list T)) : list (list T) :=
  Nat.iter n next_set σ.

Fixpoint next_lt (n : nat) (σ : list (list T)) : list (list T) :=
  match n with
  | 0 => []
  | S n => next_lt n σ ++ next_iter n σ
  end.

Local Definition error : ka_term (list T * list T) :=
  dpseudo_top ⋅ mismatch ⋅ residue R ⋅ star e.

(** Helper: strings_r distributes over append. *)

Lemma strings_r_app (σ1 σ2 : list (list T)) :
  strings_r (σ1 ++ σ2) ≡ strings_r σ1 ⊔ strings_r σ2.
Proof.
by rewrite /strings_r map_app join_list_app.
Qed.

(** Helper: expand_rel summed over a list of strings. *)

Lemma expand_rel_sum (σ : list (list T)) :
  (∀ xs, xs ∈ σ → Unit xs ⊑ L) →
  strings_r σ ⋅ e ⊑
    ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r (next_set σ)
    ⊔ dpseudo_top ⋅ mismatch ⋅ residue R.
Proof.
move=> Hσ.
rewrite /strings_r join_list_left_dist map_map.
apply/join_list_sqsubseteq =>
  _ /elem_of_list_fmap [xs [-> xs_σ]] /=.
etransitivity; first exact: expand_rel R xs (Hσ xs xs_σ).
apply: join_mono; last reflexivity.
apply: pre_ka_mul_mono.
- apply: sqsubseteq_join_list; apply/elem_of_list_fmap; eauto.
- apply/join_list_sqsubseteq => _ /elem_of_list_fmap [ys [-> ys_next]].
  apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
  exists ys; split => //.
  rewrite /next_set; apply/elem_of_list_In/in_flat_map.
  exists xs; split; exact/elem_of_list_In.
Qed.

(** Lemma 21: Iteration of a representable relation.
    For e : Rel(L), there exists ρ such that for every n and finite Σ ⊆ L:
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Next^n(Σ)_r · e* + Σ* · Σ≠ · ρ *)

(** Helper: next_lt (S n) σ is σ ++ next_lt n (next_set σ). *)

Local Lemma next_iter_succ (n : nat) (σ : list (list T)) :
  next_iter (S n) σ = next_iter n (next_set σ).
Proof. exact: Nat.iter_succ_r. Qed.

Lemma next_lt_succ (n : nat) (σ : list (list T)) :
  next_lt (S n) σ = σ ++ next_lt n (next_set σ).
Proof.
elim: n σ => [|n IHn] σ.
- by simpl; rewrite app_nil_r.
- change (next_lt (S n) σ ++ next_iter (S n) σ =
         σ ++ (next_lt n (next_set σ) ++ next_iter n (next_set σ))).
  by rewrite IHn app_assoc /next_iter Nat.iter_succ_r.
Qed.

(** Helper: ⨆(map (λ xs, Unit(xs,xs)) σ) ⊑ pseudo_top *)

Lemma diag_units_le_pseudo_top (σ : list (list T)) :
  ⨆ (map (λ xs, Unit (xs, xs)) σ) ⊑ pseudo_top.
Proof.
apply/join_list_sqsubseteq => _ /elem_of_list_fmap [xs [-> _]].
exact: unit_le_pseudo_top.
Qed.

Lemma repr_rel_iter (n : nat) (σ : list (list T)) :
  (∀ xs, xs ∈ σ → Unit xs ⊑ L) →
  strings_r σ ⋅ star e ⊑
    dpseudo_top ⋅ strings_r (next_lt n σ)
    ⊔ dpseudo_top ⋅ strings_r (next_iter n σ) ⋅ star e
    ⊔ error.
Proof.
elim: n σ => [|n IH] σ Hσ.
- (* Base case: x ⊑ pseudo_top ⋅ x since 1 ⊑ pseudo_top *)
  etransitivity; last (apply: sqsubseteq_join; left;
    apply: sqsubseteq_join; right; reflexivity).
  rewrite -assoc.
  etransitivity; last (apply: pre_ka_mul_mono;
    [exact: pre_ka_one_star | reflexivity]).
  by rewrite left_id.
- (* Inductive step: follow the paper's chain of 8 hops *)
  set σ' := next_set σ.
  set err_base := dpseudo_top ⋅ mismatch ⋅ residue R.

  (* next_set preserves membership in L *)
  have Hσ' : ∀ xs, xs ∈ σ' → Unit xs ⊑ L.
  { move=> xs /elem_of_list_In /in_flat_map [ys [_ /elem_of_list_In Hxs]].
    move: Hxs => /(next_spec R ys xs) Hle.
    etransitivity; last exact: repr_rel_cod R.
    exact:
      semi_lattice_morphism_sqsubseteq_proper
        Hle. }

  (* Hop 1: unfold star *)
  have hop1 : strings_r σ ⋅ star e ≡ strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e.
  { by rewrite {1}pre_ka_star_unfold pre_ka_right_dist right_id assoc. }

  (* Hop 2: apply expand_rel_sum *)
  have hop2 :
    strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e ⊑
    strings_r σ
    ⊔ (⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⊔ err_base) ⋅ star e.
  { apply: join_mono; first reflexivity.
    apply: pre_ka_mul_mono; last reflexivity.
    exact: expand_rel_sum Hσ. }

  (* Hop 3: distribute · e* *)
  have hop3 :
    strings_r σ
    ⊔ (⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⊔ err_base) ⋅ star e
    ≡ strings_r σ ⊔
    ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⋅ star e ⊔ error.
  { by rewrite pre_ka_left_dist /error /err_base -!assoc. }

  (* Hop 4: apply IH to σ' *)
  have hop4 :
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⋅ star e ⊔ error
    ⊑ strings_r σ ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ)
        ⋅ (dpseudo_top ⋅ strings_r (next_lt n σ')
           ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
           ⊔ error)
    ⊔ error.
  { apply: join_mono; last reflexivity.
    apply: join_mono; first reflexivity.
    rewrite -assoc; apply: pre_ka_mul_mono; first reflexivity.
    exact: IH _ Hσ'. }

  (* Hop 5: distribute ⨆diag(σ) over the three summands *)
  have hop5 :
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ (dpseudo_top ⋅ strings_r (next_lt n σ') ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e ⊔ error)
    ⊔ error
    ≡
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ error
    ⊔ error.
  { by rewrite !pre_ka_right_dist -!assoc. }

  (* Hop 6: ⨆diag(σ) ⊑ pseudo_top, so ⨆diag(σ)·pt ⊑ pt and ⨆diag(σ)·error ⊑ error *)
  have hop6 :
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ error
    ⊔ error
    ⊑
    dpseudo_top ⋅ strings_r σ
    ⊔ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ error.
  { have Hd := diag_units_le_pseudo_top σ.

    (* Each of the 5 LHS summands lands in the RHS *)
    rewrite !join_sqsubseteq; repeat split.
    (* strings_r σ ⊑ pseudo_top ⋅ strings_r σ ⊔ ... *)
    - etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_left.
      rewrite -{1}[strings_r σ](left_id 1).
      apply: pre_ka_mul_mono => //; exact: pre_ka_one_star.
    (* ⨆diag · pt · next_lt ⊑ pt · next_lt ⊔ ... *)
    - etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_right.
      apply: pre_ka_mul_mono => //; exact: dpseudo_top_absorb_list.
    (* ⨆diag · pt · next_iter · e* ⊑ pt · next_iter · e* ⊔ ... *)
    - etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_right.
      apply: pre_ka_mul_mono; last reflexivity.
      apply: pre_ka_mul_mono => //; exact: dpseudo_top_absorb_list.
    (* ⨆diag · error ⊑ error *)
    - etransitivity; last apply: sqsubseteq_join_right.
      rewrite /error !assoc.
      apply: pre_ka_mul_mono; last reflexivity.
      apply: pre_ka_mul_mono; last reflexivity.
      apply: pre_ka_mul_mono; last reflexivity.
      exact: dpseudo_top_absorb_list.
    (* error ⊑ error *)
    - exact: sqsubseteq_join_right. }

  (* Hop 7: reassemble using next_lt_succ and next_iter_succ *)
  have hop7 :
    dpseudo_top ⋅ strings_r σ
    ⊔ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ error
    ≡
    dpseudo_top ⋅ strings_r (next_lt (S n) σ)
    ⊔ dpseudo_top ⋅ strings_r (next_iter (S n) σ) ⋅ star e
    ⊔ error.
  { by rewrite next_lt_succ strings_r_app pre_ka_right_dist next_iter_succ -assoc. }

  (* Compose all hops *)
  rewrite hop1.
  etransitivity; first exact: hop2.
  rewrite hop3.
  etransitivity; first exact: hop4.
  rewrite hop5.
  etransitivity; first exact: hop6.
  by rewrite hop7.
Qed.

(** Theorem 22: If Next^n_e(Σ) = ∅, then
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Σ≠ · ρ *)

Lemma repr_rel_iter_empty
  (n : nat) (σ : list (list T)) :
  (∀ xs, xs ∈ σ → Unit xs ⊑ L) →
  next_iter n σ = [] →
  strings_r σ ⋅ star e ⊑
    ka_term_diag pseudo_top ⋅ strings_r (next_lt n σ) ⊔ error.
Proof.
move=> Hσ Hempty.
etransitivity; first exact: repr_rel_iter n σ Hσ.
by rewrite Hempty /strings_r /= right_absorb left_absorb right_id.
Qed.

End ReprRelIteration.

End RepresentableRelations.

Arguments dpseudo_top {_ _ _}.
Arguments mismatch {_ _ _}.
