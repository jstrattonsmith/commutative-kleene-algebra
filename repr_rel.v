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

Definition diff : ka_term (list T * list T) :=
  let diffs := filter (λ '(x, y), bool_decide (x ≠ y)) (enum (T * T)) in
  ⨆ (map (λ '(x, y), Unit ([x], [y])) diffs).

Record repr_rel e L : Type := {
  repr_rel_dom : ka_term_proj1 e ⊑ L;
  repr_rel_cod : ka_term_proj2 e ⊑ L;
  next : list T → list (list T);
  next_spec : ∀ sl sr, sr ∈ next sl ↔ Unit (sl, sr) ⊑ e;
  residue : ka_term (list T * list T);
  expand_rel :
    ∀ xs : list T,
      Unit (1, xs) ⋅ e ⊑
        Unit (xs, xs) ⋅ ⨆ (map (λ ys, Unit (1, ys)) (next xs))
        ⊔ ka_term_diag pseudo_top ⋅ diff ⋅ residue;
}.

(** Lifting a finite set of strings to a KA term. *)

Definition strings_r (σ : list (list T)) : ka_term (list T * list T) :=
  ⨆ (map (λ xs, Unit (1, xs)) σ).

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

Definition error : ka_term (list T * list T) :=
  ka_term_diag pseudo_top ⋅ diff ⋅ residue R ⋅ star e.

(** Helper: strings_r distributes over append. *)

Lemma strings_r_app (σ1 σ2 : list (list T)) :
  strings_r (σ1 ++ σ2) ≡ strings_r σ1 ⊔ strings_r σ2.
Proof.
by rewrite /strings_r map_app join_list_app.
Qed.

(** Helper: expand_rel summed over a list of strings. *)

Lemma expand_rel_sum (σ : list (list T)) :
  strings_r σ ⋅ e ⊑
    ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r (next_set σ)
    ⊔ ka_term_diag pseudo_top ⋅ diff ⋅ residue R.
Proof.
rewrite /strings_r join_list_left_dist map_map.
apply/join_list_sqsubseteq => _ /elem_of_list_fmap [xs [-> xs_σ]] /=.
etransitivity; first exact: expand_rel R xs.
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

Lemma next_iter_succ (n : nat) (σ : list (list T)) :
  next_iter (S n) σ = next_iter n (next_set σ).
Proof. exact: Nat.iter_succ_r. Qed.

Lemma next_lt_succ (n : nat) (σ : list (list T)) :
  next_lt (S n) σ = σ ++ next_lt n (next_set σ).
Proof.
elim: n σ => [|n IHn] σ.
- by simpl; rewrite app_nil_r.
- change (next_lt (S n) σ ++ next_iter (S n) σ =
         σ ++ (next_lt n (next_set σ) ++ next_iter n (next_set σ))).
  rewrite IHn -next_iter_succ.
  by rewrite app_assoc.
Qed.

(** Helper: ⨆(map (λ xs, Unit(xs,xs)) σ) ⊑ pseudo_top *)

Lemma unit_le_pseudo_top (x : list T * list T) : Unit x ⊑ pseudo_top.
Proof.
etransitivity; last exact: pseudo_top_absorb x.
rewrite -{1}[Unit x](right_id 1); apply: pre_ka_mul_mono => //.
exact: pre_ka_one_star.
Qed.

Lemma diag_units_le_pseudo_top (σ : list (list T)) :
  ⨆ (map (λ xs, Unit (xs, xs) : ka_term (list T * list T)) σ) ⊑ pseudo_top.
Proof.
apply/join_list_sqsubseteq => _ /elem_of_list_fmap [xs [-> _]].
exact: unit_le_pseudo_top.
Qed.

Lemma repr_rel_iter (n : nat) (σ : list (list T)) :
  strings_r σ ⋅ star e ⊑
    pseudo_top ⋅ strings_r (next_lt n σ)
    ⊔ pseudo_top ⋅ strings_r (next_iter n σ) ⋅ star e
    ⊔ error.
Proof.
elim: n σ => [|n IH] σ.
- (* Base case: x ⊑ pseudo_top ⋅ x since 1 ⊑ pseudo_top *)
  etransitivity; last (apply: sqsubseteq_join; left;
    apply: sqsubseteq_join; right; reflexivity).
  rewrite -assoc.
  etransitivity; last (apply: pre_ka_mul_mono;
    [exact: pre_ka_one_star | reflexivity]).
  by rewrite left_id.
- (* Inductive step: follow the paper's chain of 8 hops *)
  set σ' := next_set σ.
  set err_base := ka_term_diag pseudo_top ⋅ diff ⋅ residue R.

  (* Hop 1: unfold star *)
  have hop1 : strings_r σ ⋅ star e ≡
    strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e.
  { by rewrite {1}pre_ka_star_unfold pre_ka_right_dist right_id assoc. }

  (* Hop 2: apply expand_rel_sum *)
  have hop2 : strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e ⊑
    strings_r σ ⊔ (⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⊔ err_base) ⋅ star e.
  { apply: join_mono; first reflexivity.
    apply: pre_ka_mul_mono; last reflexivity.
    exact: expand_rel_sum. }

  (* Hop 3: distribute · e* and simplify err_base · e* = error *)
  have hop3 : strings_r σ ⊔ (⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⊔ err_base) ⋅ star e ≡
    strings_r σ ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⋅ star e ⊔ error.
  { rewrite pre_ka_left_dist /error /err_base -!assoc. by rewrite [_ ⊔ _ ⋅ _]assoc. }

  (* Hop 4: apply IH to σ' *)
  have hop4 : strings_r σ ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ strings_r σ' ⋅ star e ⊔ error ⊑
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ (pseudo_top ⋅ strings_r (next_lt n σ') ⊔ pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e ⊔ error)
    ⊔ error.
  { admit. }

  (* Hop 5: distribute ⨆diag(σ) over the three summands *)
  have hop5 :
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ (pseudo_top ⋅ strings_r (next_lt n σ') ⊔ pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e ⊔ error)
    ⊔ error
    ≡
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ pseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ error
    ⊔ error.
  { admit. }

  (* Hop 6: ⨆diag(σ) ⊑ pseudo_top, so ⨆diag(σ)·pt ⊑ pt and ⨆diag(σ)·error ⊑ error *)
  have hop6 :
    strings_r σ
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ pseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ ⨆ (map (λ xs, Unit (xs, xs)) σ) ⋅ error
    ⊔ error
    ⊑
    pseudo_top ⋅ strings_r σ
    ⊔ pseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ error.
  { admit. }

  (* Hop 7: reassemble using next_lt_succ and next_iter_succ *)
  have hop7 :
    pseudo_top ⋅ strings_r σ
    ⊔ pseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ pseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ error
    ≡
    pseudo_top ⋅ strings_r (next_lt (S n) σ)
    ⊔ pseudo_top ⋅ strings_r (next_iter (S n) σ) ⋅ star e
    ⊔ error.
  { admit. }

  (* Compose all hops *)
  rewrite hop1.
  etransitivity; first exact: hop2.
  rewrite hop3.
  etransitivity; first exact: hop4.
  rewrite hop5.
  etransitivity; first exact: hop6.
  by rewrite hop7.
Admitted.

(** Theorem 22: If Next^n_e(Σ) = ∅, then
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Σ≠ · ρ *)

Lemma repr_rel_iter_empty (n : nat) (σ : list (list T)) :
  next_iter n σ = [] →
  strings_r σ ⋅ star e ⊑
    pseudo_top ⋅ strings_r (next_lt n σ) ⊔ error.
Proof.
move=> Hempty.
etransitivity; first exact: repr_rel_iter n σ.
rewrite Hempty /strings_r /=.
(* The middle term has ⨆ [] = ⊥, so pseudo_top ⋅ ⊥ ⋅ star e ≡ ⊥ *)
rewrite (@right_absorb _ _ (⊥ : ka_term _) _ _) (@left_absorb _ _ (⊥ : ka_term _) _ _).
by rewrite right_id.
Qed.

End ReprRelIteration.


End RepresentableRelations.
