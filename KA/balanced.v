(* Balanced universality over the monoid `list A * nat`: the pre-KA engine
   behind CKAUndec/UnivEncoding.v. The second component counts a single
   letter that commutes with everything (the `b` of Xu, Zhou, Walker and
   Kincaid's universality encoding, arXiv:2607.09635, Section 4).

   The left-hand side is `bal_star`, the star of the "balanced" letters
   `([t], 1)`, whose language is `{(w, |w|)}`. Pre-KA has no star
   induction, so we cannot reason about `bal_star ⊑ x` through languages
   alone. Instead, `bal_univ_complete` unfolds `bal_star` a fixed number
   `D` of times: if every balanced word shorter than `D` is in `l x`, and
   every balanced word of length `D` has a prefix accepted by a term
   `Pre` with `Pre ⋅ bal_star ⊑ x`, then `bal_star ⊑ x`. The padding
   `bal_star` at the end of the upper bound absorbs the residue
   (`bal_absorb`).

   Using all generators (`([t], 0)` and `([], 1)`) on the left, i.e.
   `pseudo_top`, would not work: in a model of finite and infinite words
   where only stars of exactly the generators produce infinite words,
   `pseudo_top ⊑ e` forces every infinite word to have a prefix in a
   regular set computed from `e`, which makes the inequality decidable
   for the instances a reduction with language-based soundness would
   produce. The `k = |w|` slice used here is not regular, which is where
   that argument breaks down. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.

(** The additive monoid of natural numbers. Beware that `1` in `ka_scope`
    denotes the unit of this monoid, i.e. `0`; write `1%nat` for one. *)

Section NatAddMonoid.

Local Instance nat_add_one : One nat := 0%nat.
Local Instance nat_add_mul : Mul nat := Nat.add.

Lemma nat_add_monoid_mixin : @MonoidMixin nat equivL nat_add_mul nat_add_one.
Proof.
constructor.
- move=> ???; rewrite /equiv /equivL /mul /nat_add_mul; lia.
- by move=> ?.
- move=> ?; rewrite /equiv /equivL /mul /nat_add_mul /one /nat_add_one; lia.
- by move=> ?? -> ?? ->.
Qed.

Canonical Structure nat_add_monoid :=
  @Monoid' nat equivL nat_add_mul nat_add_one _ nat_add_monoid_mixin.

Lemma nat_add_mulE (x y : nat_add_monoid) : x ⋅ y = (x + y)%nat.
Proof. by []. Qed.

Lemma nat_add_oneE : (1 : nat_add_monoid) = 0%nat.
Proof. by []. Qed.

End NatAddMonoid.

Section Balanced.

Context {A : setoid} `{!LeibnizEquiv A, !EqDecision A, !Finite A}.

Notation M := (prod_monoid (list_monoid A) nat_add_monoid).

Implicit Types (w u : list A) (t : A).

Lemma M_equiv_eq (x y : M) : x ≡ y → x = y.
Proof.
case: x y => [w1 k1] [w2 k2] [/= /leibniz_equiv_iff -> ek].
by rewrite ek.
Qed.

Lemma M_eq_equiv (x y : M) : x = y → x ≡ y.
Proof. by move=> ->. Qed.

Lemma M_mulE w1 k1 w2 k2 :
  ((w1, k1) ⋅ (w2, k2) : M) = (w1 ++ w2, (k1 + k2)%nat).
Proof. by []. Qed.

Lemma M_oneE : (1 : M) = ([], 0%nat).
Proof. by []. Qed.

(** A balanced word: `w` paired with its own length. *)

Definition bal w : ka_term M := Unit (w, length w).

Definition bal_gen : ka_term M := ⨆ t ∈ enum A, bal [t].

Definition bal_star : ka_term M := star bal_gen.

Lemma bal_app w u : bal (w ++ u) ≡ bal w ⋅ bal u.
Proof.
rewrite /bal -monoid_morphism_mul; apply: ka_unit_proper.
by rewrite length_app.
Qed.

Lemma bal_nil : bal [] ≡ 1.
Proof. by []. Qed.

Lemma bal_letter_gen t : bal [t] ⊑ bal_gen.
Proof. apply: (sqsubseteq_join_list (λ t, bal [t])); exact: elem_of_enum. Qed.

Lemma bal_absorb w : bal w ⋅ bal_star ⊑ bal_star.
Proof.
elim: w => [|t w IH]; first by rewrite bal_nil left_id.
rewrite -[t :: w]/([t] ++ w) bal_app -assoc IH /bal_star.
rewrite bal_letter_gen; exact: pre_ka_mul_star.
Qed.

Lemma bal_le_star w : bal w ⊑ bal_star.
Proof.
rewrite -(bal_absorb w); rewrite -{1}[bal w](right_id 1).
apply: pre_ka_mul_mono => //; exact: pre_ka_one_star.
Qed.

Lemma l_bal w y : l (bal w) y ↔ y = (w, length w).
Proof. by split => [/M_equiv_eq|->]. Qed.

Lemma l_bal_gen y : l bal_gen y → ∃ t, y = ([t], 1%nat).
Proof.
rewrite /bal_gen semi_lattice_morphism_join_list elem_of_lang_join_list.
by case=> t [] _ /l_bal ->; exists t.
Qed.

Lemma l_bal_star y : l bal_star y ↔ y.2 = length y.1.
Proof.
split.
- case=> n; elim: n y => [|n IH] [w k].
    by move=> /M_equiv_eq [-> ->].
  case=> - [w1 k1] [] - [w2 k2] [] /M_equiv_eq [-> ->] [] H1 H2.
  case/l_bal_gen: H1 => t [-> ->].
  by move: (IH _ H2) => /= ->.
- case: y => w k Hk; simpl in Hk; subst k.
  apply/l_alt; exact: bal_le_star.
Qed.

(** The engine: unfold `bal_star` `D` times. *)

Lemma bal_cover_from (x : ka_term M) D u :
  (∀ w, length w < D → bal (u ++ w) ⊑ x) →
  (∀ w, length w = D → bal (u ++ w) ⋅ bal_star ⊑ x) →
  bal u ⋅ bal_star ⊑ x.
Proof.
elim: D u => [|D IH] u short long.
  by move: (long [] eq_refl); rewrite app_nil_r.
rewrite /bal_star pre_ka_star_unfold -/bal_star pre_ka_right_dist right_id.
apply/join_sqsubseteq; split.
  by move: (short [] ltac:(simpl; lia)); rewrite app_nil_r.
rewrite /bal_gen join_list_left_dist join_list_right_dist.
apply/join_list_sqsubseteq => t _.
rewrite assoc -bal_app; apply: IH => w Hw.
- rewrite -app_assoc; apply: short => /=; lia.
- rewrite -app_assoc; apply: long => /=; lia.
Qed.

Theorem bal_univ_complete (x Pre : ka_term M) D :
  Pre ⋅ bal_star ⊑ x →
  (∀ w, length w < D → l x (w, length w)) →
  (∀ w, length w = D → ∃ w1 w2, w = w1 ++ w2 ∧ l Pre (w1, length w1)) →
  bal_star ⊑ x.
Proof.
move=> Hpre short long.
rewrite -[bal_star](left_id 1) -bal_nil.
apply: (bal_cover_from (D := D)) => w Hw /=.
- by apply/l_alt; apply: short.
- case: (long w Hw) => w1 [] w2 [] -> /l_alt Hw1.
  rewrite bal_app -assoc bal_absorb -Hpre.
  exact: pre_ka_mul_mono.
Qed.

Theorem bal_univ_sound (x : ka_term M) w :
  bal_star ⊑ x → l x (w, length w).
Proof. by move=> Hx; apply/l_alt; rewrite -Hx; exact: bal_le_star. Qed.

(** Membership in a padded component `Pre ⋅ bal_star`. *)

Lemma l_padded (Pre : ka_term M) w k :
  l (Pre ⋅ bal_star) (w, k) ↔
  ∃ w1 k1 w2, w = w1 ++ w2 ∧ k = k1 + length w2 ∧ l Pre (w1, k1).
Proof.
split.
- case=> - [w1 k1] [] - [w2 k2] [] /M_equiv_eq [-> ->] [] H1 /l_bal_star /=.
  move=> ->; by exists w1, k1, w2.
- case=> w1 [] k1 [] w2 [] -> [] -> H1.
  exists (w1, k1), (w2, length w2); split => //.
  split => //; exact/l_bal_star.
Qed.

(** Languages of products and stars over `list A * nat`. *)

Lemma l_pair_mul_inv (X Y : ka_term M) w k :
  l (X ⋅ Y) (w, k) →
  ∃ w1 k1 w2 k2, w = w1 ++ w2 ∧ k = (k1 + k2)%nat ∧
    l X (w1, k1) ∧ l Y (w2, k2).
Proof.
case=> - [w1 k1] [] - [w2 k2] [] /M_equiv_eq [-> ->] [] H1 H2.
by exists w1, k1, w2, k2.
Qed.

Lemma l_pair_mul_intro (X Y : ka_term M) w1 k1 w2 k2 :
  l X (w1, k1) → l Y (w2, k2) → l (X ⋅ Y) (w1 ++ w2, (k1 + k2)%nat).
Proof. by move=> H1 H2; exists (w1, k1), (w2, k2). Qed.

Lemma l_star_nil (X : ka_term M) : l (star X) ([], 0%nat).
Proof. by exists 0%nat. Qed.

Lemma l_star_cons (X : ka_term M) w1 k1 w2 k2 :
  l X (w1, k1) → l (star X) (w2, k2) →
  l (star X) (w1 ++ w2, (k1 + k2)%nat).
Proof.
by move=> H1 [n H2]; exists (S n); exists (w1, k1), (w2, k2).
Qed.

Lemma l_star_elim (X : ka_term M) (Pr : list A → nat → Prop) :
  Pr [] 0%nat →
  (∀ w1 k1 w2 k2, l X (w1, k1) → Pr w2 k2 → Pr (w1 ++ w2) (k1 + k2)%nat) →
  ∀ w k, l (star X) (w, k) → Pr w k.
Proof.
move=> H0 HS w k [n]; elim: n w k => [|n IH] w k /=.
  by move=> /M_equiv_eq [-> ->].
case=> - [w1 k1] [] - [w2 k2] [] /M_equiv_eq [-> ->] [] H1 H2.
exact: HS H1 (IH _ _ H2).
Qed.

End Balanced.
