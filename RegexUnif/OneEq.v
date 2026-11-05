(* One equation instead of a system. Given two distinct letters `a` and
   `b`, the words `mark n = aⁿ b` form a prefix code: none is a prefix
   of another. The system `[(e₀, f₀); …; (eₖ, fₖ)]` becomes the single
   equation `⨆ᵢ aⁱ b ⋅ eᵢ ≡ ⨆ᵢ aⁱ b ⋅ fᵢ` (`one_eq`). A pre-KA solution
   of the system solves it by congruence (`unif_one_eq`), and in
   languages, cutting `aⁱ b` off the front recovers the `i`-th equation
   (`one_eq_lsolves`). No fresh letters are needed. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite.
From Stdlib Require Import Arith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.algebra KA.pre_ka KA.lang.
From kacc Require Import RegexUnif.Syntax RegexUnif.Invariant.

Section OneEq.

Context {A : setoid} `{!LeibnizEquiv A, !EqDecision A, !Finite A}.

Notation W := (list_monoid A).
Notation UT := (@uterm A).
Notation UE := (@ueq A).

Variables a b : A.
Hypothesis Hab : a ≠ b.

Definition mark (n : nat) : list A := repeat a n ++ [b].

Lemma mark_inj n m y z : mark n ++ y = mark m ++ z → n = m ∧ y = z.
Proof.
rewrite /mark -!app_assoc.
elim: n m => [|n IH] [|m] /=.
- by case.
- by case=> Hba _; case: Hab.
- by case=> Hab' _; case: Hab.
- by case=> /IH [-> ->].
Qed.

Fixpoint one_side (f : UE → UT) (n : nat) (eqs : list UE) : UT :=
  match eqs with
  | [] => ⊥
  | q :: eqs => tw (mark n) ⋅ f q ⊔ one_side f (S n) eqs
  end.

Definition one_eq (eqs : list UE) : UE :=
  (one_side fst 0 eqs, one_side snd 0 eqs).

Lemma one_side_cons f n q eqs :
  one_side f n (q :: eqs) = tw (mark n) ⋅ f q ⊔ one_side f (S n) eqs.
Proof. by []. Qed.

(** * Completeness *)

Lemma subst_join σ (e1 e2 : UT) : subst σ (e1 ⊔ e2) = subst σ e1 ⊔ subst σ e2.
Proof. by []. Qed.

Lemma subst_mul σ (e1 e2 : UT) : subst σ (e1 ⋅ e2) = subst σ e1 ⋅ subst σ e2.
Proof. by []. Qed.

Lemma subst_one_side σ n eqs :
  (∀ q, q ∈ eqs → subst σ q.1 ≡ subst σ q.2) →
  subst σ (one_side fst n eqs) ≡ subst σ (one_side snd n eqs).
Proof.
elim: eqs n => [|q eqs IH] n H; first reflexivity.
rewrite !one_side_cons !subst_join !subst_mul.
rewrite (H q (elem_of_list_here _ _)) (IH (S n)) //.
by move=> q' Hq'; apply: H; apply: elem_of_list_further.
Qed.

Lemma unif_one_eq eqs : unif preka_eqv eqs → unif preka_eqv [one_eq eqs].
Proof.
case=> σ Hσ; exists σ => p /elem_of_list_singleton ->.
exact: subst_one_side.
Qed.

(** * Soundness *)

Lemma in_one_side ρ f n eqs x :
  lsubst ρ (one_side f n eqs) x ↔
  ∃ k q y, eqs !! k = Some q ∧ x = mark (n + k) ++ y ∧ lsubst ρ (f q) y.
Proof.
elim: eqs n x => [|q eqs IH] n x.
  by rewrite lsubst_bot in_bot; split => [[]|[k [q [y []]]]].
rewrite one_side_cons lsubst_join in_join lsubst_mul in_mul IH; split.
- case=> [[x1 [x2 [-> [/in_tw -> Hq]]]]|[k [q' [y [Hk [-> Hy]]]]]].
  + by exists 0, q, x2; rewrite Nat.add_0_r.
  + by exists (S k), q', y; rewrite Nat.add_succ_r.
- case=> [[|k] [q' [y [/= Hk [-> Hy]]]]].
  + case: Hk Hy => <- Hy; left; exists (mark n), y; rewrite Nat.add_0_r.
    by do !split => //; apply/in_tw.
  + by right; exists k, q', y; rewrite Nat.add_succ_r.
Qed.

Lemma in_one_side_at ρ f eqs k q y :
  eqs !! k = Some q →
  lsubst ρ (one_side f 0 eqs) (mark k ++ y) ↔ lsubst ρ (f q) y.
Proof.
move=> Hk; rewrite in_one_side; split => [[k' [q' [y' [Hk' [Hm Hy]]]]]|Hy].
- case/mark_inj: Hm => /= Hkk Hyy; subst k' y'.
  by move: Hk'; rewrite Hk => - [->].
- by exists k, q, y.
Qed.

Lemma one_eq_lsolves ρ eqs : lsolves ρ [one_eq eqs] → lsolves ρ eqs.
Proof.
move=> Hsol q /elem_of_list_lookup [k Hk] y.
have := Hsol _ (elem_of_list_here _ _) (mark k ++ y).
by rewrite /= !(in_one_side_at _ _ _ Hk).
Qed.

End OneEq.
