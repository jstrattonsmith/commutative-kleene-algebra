Require Import ssreflect.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From Undecidability.Synthetic Require Import DecidabilityFacts.
From Undecidability.Synthetic Require Import MoreReducibilityFacts.
From stdpp Require Import base countable decidable.
From kacc Require Import KA.utils KA.algebra KA.pre_ka.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Enumerability of [ka_eq]

    We show that if the equivalence relation [≡] of the carrier monoid
    [T] is enumerable, then so is the induced equivalence [ka_eq] on
    [ka_term T].  "Enumerable" is the notion from the
    coq-library-undecidability development
    ([Undecidability.Synthetic.Definitions.enumerable]).

    The carrier is assumed [Countable] (this yields decidable Leibniz
    equality on [ka_term T], which is needed to close the relation under
    transitivity, and an enumeration of [ka_term T]).

    The proof reifies [ka_eq] derivations as an inductive datatype [D],
    equips it with a [Countable] instance (hence an enumeration), and
    checks each derivation with a partial function [check] whose image is
    exactly the graph of [ka_eq]. *)

(** Any countable type is enumerable in the sense of the library. *)
Lemma countable_enumerableT (X : Type) `{Countable X} : enumerable__T X.
Proof.
exists decode_nat => x; exists (encode_nat x); exact: decode_encode_nat.
Qed.

(** Tags for the twelve "constant" equational axiom schemes. *)
Inductive ax_tag :=
  | AMul | LMulId | RMulId | AJoin | CJoin | LJoinId
  | IJoin | LAbs | RAbs | DstR | DstL | SUnf.

Global Instance ax_tag_eq_dec : EqDecision ax_tag.
Proof. solve_decision. Defined.

Open Scope nat_scope.
Definition ax_to_nat (t : ax_tag) : nat :=
  match t with
  | AMul => 0 | LMulId => 1 | RMulId => 2 | AJoin => 3 | CJoin => 4
  | LJoinId => 5 | IJoin => 6 | LAbs => 7 | RAbs => 8 | DstR => 9
  | DstL => 10 | SUnf => 11
  end.
Definition nat_to_ax (n : nat) : ax_tag :=
  match n with
  | 0 => AMul | 1 => LMulId | 2 => RMulId | 3 => AJoin | 4 => CJoin
  | 5 => LJoinId | 6 => IJoin | 7 => LAbs | 8 => RAbs | 9 => DstR
  | 10 => DstL | _ => SUnf
  end.
Close Scope nat_scope.

Global Instance ax_tag_countable : Countable ax_tag.
Proof. refine (inj_countable' ax_to_nat nat_to_ax _); by case. Defined.

Section KaEqEnumerable.

Context (T : monoid) `{Countable T}.

Implicit Types (e a b c : ka_term T) (x y : T).

(** Reified [ka_eq] derivations.  [D_unit k] records that the [k]-th
    element enumerated by the carrier's [≡]-enumerator justifies a
    [ka_unit_proper] step; [D_ax t a b c] records an instance of one of
    the constant axiom schemes. *)
Inductive D :=
  | D_refl (a : ka_term T)
  | D_sym (d : D)
  | D_trans (d1 d2 : D)
  | D_muldistr (x y : T)
  | D_unit (k : nat)
  | D_mulc (d1 d2 : D)
  | D_joinc (d1 d2 : D)
  | D_starc (d : D)
  | D_ax (t : ax_tag) (a b c : ka_term T).

Global Instance D_eq_dec : EqDecision D.
Proof. solve_decision. Defined.

(** Encoding of [D] into generic trees, as for [ka_term]. *)
Notation Dleaf := (T + (ka_term T + (nat + ax_tag)))%type.

Global Instance D_countable : Countable D.
Proof.
set (enc :=
  fix go (d : D) : gen_tree Dleaf :=
    match d with
    | D_refl a => GenNode 0 [GenLeaf (inr (inl a))]
    | D_sym d => GenNode 1 [go d]
    | D_trans d1 d2 => GenNode 2 [go d1; go d2]
    | D_muldistr x y => GenNode 3 [GenLeaf (inl x); GenLeaf (inl y)]
    | D_unit k => GenNode 4 [GenLeaf (inr (inr (inl k)))]
    | D_mulc d1 d2 => GenNode 5 [go d1; go d2]
    | D_joinc d1 d2 => GenNode 6 [go d1; go d2]
    | D_starc d => GenNode 7 [go d]
    | D_ax t a b c =>
        GenNode 8 [GenLeaf (inr (inr (inr t))); GenLeaf (inr (inl a));
                   GenLeaf (inr (inl b)); GenLeaf (inr (inl c))]
    end).
set (dec :=
  fix go (u : gen_tree Dleaf) : D :=
    match u with
    | GenNode 0 [GenLeaf (inr (inl a))] => D_refl a
    | GenNode 1 [u] => D_sym (go u)
    | GenNode 2 [u1; u2] => D_trans (go u1) (go u2)
    | GenNode 3 [GenLeaf (inl x); GenLeaf (inl y)] => D_muldistr x y
    | GenNode 4 [GenLeaf (inr (inr (inl k)))] => D_unit k
    | GenNode 5 [u1; u2] => D_mulc (go u1) (go u2)
    | GenNode 6 [u1; u2] => D_joinc (go u1) (go u2)
    | GenNode 7 [u] => D_starc (go u)
    | GenNode 8 [GenLeaf (inr (inr (inr t))); GenLeaf (inr (inl a));
                 GenLeaf (inr (inl b)); GenLeaf (inr (inl c))] => D_ax t a b c
    | _ => D_unit 0
    end).
refine (inj_countable' enc dec _).
(* QUEST: what is * doing here? *)
by elim=> //= *; congruence.
Qed.

(** The pair proved by an instance of a constant axiom scheme. *)
Definition axpair (t : ax_tag) (a b c : ka_term T)
    : ka_term T * ka_term T :=
  match t with
  | AMul => (a ⋅ (b ⋅ c), (a ⋅ b) ⋅ c)
  | LMulId => (1 ⋅ a, a)
  | RMulId => (a ⋅ 1, a)
  | AJoin => (a ⊔ (b ⊔ c), (a ⊔ b) ⊔ c)
  | CJoin => (a ⊔ b, b ⊔ a)
  | LJoinId => (⊥ ⊔ a, a)
  | IJoin => (a ⊔ a, a)
  | LAbs => (⊥ ⋅ a, ⊥)
  | RAbs => (a ⋅ ⊥, ⊥)
  | DstR => (a ⋅ (b ⊔ c), a ⋅ b ⊔ a ⋅ c)
  | DstL => ((a ⊔ b) ⋅ c, a ⋅ c ⊔ b ⋅ c)
  | SUnf => (star a, 1 ⊔ a ⋅ star a)
  end.

Lemma axpair_sound t a b c : (axpair t a b c).1 ≡ (axpair t a b c).2.
Proof.
case: t => /=.
- exact: ka_mul_assoc.
- exact: ka_mul_left_id.
- exact: ka_mul_right_id.
- exact: ka_join_assoc.
- exact: ka_join_comm.
- exact: ka_join_left_id.
- exact: ka_join_idemp.
- exact: ka_mul_left_absorb.
- exact: ka_mul_right_absorb.
- exact: ka_mul_join_right.
- exact: ka_mul_join_left.
- exact: ka_star_unfold.
Qed.

Section WithEnum.

Variable g : nat → option (T * T).

(** Compute the conclusion [(a, b)] of a derivation, or [None] if the
    derivation is ill-formed (a transitivity whose two halves do not meet,
    or a [D_unit] pointing past the enumerator). *)
Fixpoint check (d : D) : option (ka_term T * ka_term T) :=
  match d with
  | D_refl a => Some (a, a)
  | D_sym d =>
      match check d with Some (a, b) => Some (b, a) | None => None end
  | D_trans d1 d2 =>
      match check d1, check d2 with
      | Some (a, b), Some (b', c) =>
          if decide (b = b') is left _ then Some (a, c) else None
      | _, _ => None
      end
  | D_muldistr x y => Some (Unit (x ⋅ y), Unit x ⋅ Unit y)
  | D_unit k =>
      match g k with Some (x, y) => Some (Unit x, Unit y) | None => None end
  | D_mulc d1 d2 =>
      match check d1, check d2 with
      | Some (a, b), Some (c, e) => Some (a ⋅ c, b ⋅ e)
      | _, _ => None
      end
  | D_joinc d1 d2 =>
      match check d1, check d2 with
      | Some (a, b), Some (c, e) => Some (a ⊔ c, b ⊔ e)
      | _, _ => None
      end
  | D_starc d =>
      match check d with Some (a, b) => Some (star a, star b) | None => None end
  | D_ax t a b c => Some (axpair t a b c)
  end.

(** Soundness: every conclusion computed by [check] is a genuine
    [ka_eq]. *)
Lemma check_sound :
  (∀ n x y, g n = Some (x, y) → x ≡ y) →
  ∀ d a b, check d = Some (a, b) → a ≡ b.
Proof.
move=> Hg; elim.
- by move=> a0 a b [= <- <-].
- move=> d IH a b /=.
  case E: (check d) => [[a0 b0]|] //= [= <- <-].
  by symmetry; exact: (IH _ _ E).
- move=> d1 IH1 d2 IH2 a b /=.
  case E1: (check d1) => [[a1 b1]|] //=.
  case E2: (check d2) => [[a2 b2]|] //=.
  case: (decide (b1 = a2)) => [e|_] //= [= <- <-].
  transitivity b1; first exact: (IH1 _ _ E1).
  by rewrite e; exact: (IH2 _ _ E2).
- by move=> x y a b [= <- <-]; exact: ka_mul_distr.
- move=> k a b /=.
  case E: (g k) => [[x y]|] //= [= <- <-].
  by apply: ka_unit_proper; exact: (Hg _ _ _ E).
- move=> d1 IH1 d2 IH2 a b /=.
  case E1: (check d1) => [[a1 b1]|] //=.
  case E2: (check d2) => [[a2 b2]|] //= [= <- <-].
  by apply: ka_mul_proper; [exact: (IH1 _ _ E1) | exact: (IH2 _ _ E2)].
- move=> d1 IH1 d2 IH2 a b /=.
  case E1: (check d1) => [[a1 b1]|] //=.
  case E2: (check d2) => [[a2 b2]|] //= [= <- <-].
  by apply: ka_join_proper; [exact: (IH1 _ _ E1) | exact: (IH2 _ _ E2)].
- move=> d IH a b /=.
  case E: (check d) => [[a0 b0]|] //= [= <- <-].
  by apply: ka_star_proper; exact: (IH _ _ E).
- move=> t a0 b0 c0 a b /= [= E].
  by move: (axpair_sound t a0 b0 c0); rewrite E.
Qed.

(** Completeness: every [ka_eq] pair is computed by [check] on some
    derivation. *)
Lemma check_complete :
  (∀ x y, x ≡ y → ∃ n, g n = Some (x, y)) →
  ∀ e1 e2, ka_eq e1 e2 → ∃ d, check d = Some (e1, e2).
Proof.
move=> Hg e1 e2; elim.
- by move=> x; exists (D_refl x).
- by move=> x y _ [d Hd]; exists (D_sym d); rewrite /= Hd.
- move=> x y z _ [d1 H1] _ [d2 H2]; exists (D_trans d1 d2).
  rewrite /= H1 H2 /=.
  case: (decide (y = y)) => [_|neq] /=; last by case: (neq eq_refl).
  done.
- by move=> x y; exists (D_muldistr x y).
- move=> x y Hxy; have [n Hn] := Hg x y Hxy.
  by exists (D_unit n); rewrite /= Hn.
- move=> x y _ [d1 H1] z w _ [d2 H2].
  by exists (D_mulc d1 d2); rewrite /= H1 H2.
- move=> x y _ [d1 H1] z w _ [d2 H2].
  by exists (D_joinc d1 d2); rewrite /= H1 H2.
- by move=> x y _ [d Hd]; exists (D_starc d); rewrite /= Hd.
- by move=> x y z; exists (D_ax AMul x y z).
- by move=> x; exists (D_ax LMulId x x x).
- by move=> x; exists (D_ax RMulId x x x).
- by move=> x y z; exists (D_ax AJoin x y z).
- by move=> x y; exists (D_ax CJoin x y x).
- by move=> x; exists (D_ax LJoinId x x x).
- by move=> x; exists (D_ax IJoin x x x).
- by move=> x; exists (D_ax LAbs x x x).
- by move=> x; exists (D_ax RAbs x x x).
- by move=> u v w; exists (D_ax DstR u v w).
- by move=> u v w; exists (D_ax DstL u v w).
- by move=> t; exists (D_ax SUnf t t t).
Qed.

End WithEnum.

Theorem ka_eq_enumerable :
  enumerable (fun p : T * T => p.1 ≡ p.2) →
  enumerable (fun p : ka_term T * ka_term T => p.1 ≡ p.2).
Proof.
move=> [g Hg].
have Hgs : ∀ n x y, g n = Some (x, y) → x ≡ y.
  by move=> n x y Hn; apply/(Hg (x, y)); exists n.
have Hgc : ∀ x y, x ≡ y → ∃ n, g n = Some (x, y).
  by move=> x y /(Hg (x, y)).
have [enD HenD] := @countable_enumerableT D _ _.
exists (fun n => match enD n with Some d => check g d | None => None end).
move=> [e1 e2] /=; split.
- move=> H12.
  have [d Hd] := check_complete Hgc H12.
  by have [n Hn] := HenD d; exists n; rewrite Hn.
- move=> [n]; case E: (enD n) => [d|] // Hd.
  exact: (check_sound Hgs Hd).
Qed.

(** The canonical order [⊑] on [ka_term T], characterised by
    [x ⊑ y ↔ x ⊔ y ≡ y], is enumerable whenever the carrier's [≡] is: it
    reduces to [ka_eq] along [(x, y) ↦ (x ⊔ y, y)], and enumerability is
    preserved under reductions with an enumerable source and discrete
    target. *)
Theorem ka_sqsubseteq_enumerable :
  enumerable (fun p : T * T => p.1 ≡ p.2) →
  enumerable (fun p : ka_term T * ka_term T => p.1 ⊑ p.2).
Proof.
move=> Henum.
apply: (@enumerable_red (ka_term T * ka_term T) (ka_term T * ka_term T)
          (fun p => p.1 ⊑ p.2) (fun q => q.1 ≡ q.2)).
- exists (fun p => (p.1 ⊔ p.2, p.2)).
  by move=> [a b] /=; exact: sqsubseteq_iff.
- exact: (@countable_enumerableT (ka_term T * ka_term T) _ _).
- apply: discrete_prod; apply/discrete_iff; constructor; exact: ka_term_eq_dec.
- exact: ka_eq_enumerable Henum.
Qed.

End KaEqEnumerable.

(** * Enumerability of a fixed-rhs "slice" of [⊑]

    Generic packaging of [ka_sqsubseteq_enumerable] for the common shape
    every KA-term-inequality undecidability argument in this project
    needs: a carrier monoid [T] with decidable, countable, Leibniz-equal
    [≡] gives [⊑] on [ka_term T] enumerable (via [KA_ineq_over]), and
    hence any fixed-rhs SLICE of it (a family [lhs : nat -> ka_term T]
    against one fixed [rhs]) enumerable too, via [enumerable_red].
    Originally proved twice, once each for the machine-specific carrier
    [TmMonoid] (CKAUndec/KEnumerable.v) and the binary-alphabet carrier
    [Tm_bin] (CKAUndec/BinaryAlphabetMComplete.v) -- factored out here
    since neither proof used anything but this file's own machinery. *)

Section SliceEnumerable.

Context (T : monoid).
Context `{HeqT : !RelDecision (@Logic.eq (monoid_car T))}.
Context `{!Countable (monoid_car T)} (HLeibniz : LeibnizEquiv (monoid_car T)).

Instance T_equiv_dec (x y : monoid_car T) : Decision (x ≡ y).
Proof.
destruct (HeqT x y) as [-> | Hne].
- left. reflexivity.
- right. intros Heq. apply Hne. exact (leibniz_equiv x y Heq).
Defined.

Lemma T_equiv_enumerable : enumerable (fun p : monoid_car T * monoid_car T => p.1 ≡ p.2).
Proof.
apply: dec_count_enum.
2: exact: (@countable_enumerableT (monoid_car T * monoid_car T) _ _).
exists (fun p => bool_decide (p.1 ≡ p.2)).
intros p. unfold reflects. symmetry. apply bool_decide_eq_true.
Qed.

Definition KA_ineq_over : ka_term (monoid_car T) * ka_term (monoid_car T) -> Prop :=
  fun p => p.1 ⊑ p.2.

Theorem KA_ineq_over_enumerable : enumerable KA_ineq_over.
Proof. exact: ka_sqsubseteq_enumerable T_equiv_enumerable. Qed.

Theorem slice_enumerable
    (lhs : nat -> ka_term (monoid_car T)) (rhs : ka_term (monoid_car T)) :
  enumerable (fun z => lhs z ⊑ rhs).
Proof.
apply: (@enumerable_red nat (ka_term (monoid_car T) * ka_term (monoid_car T))
  (fun z => lhs z ⊑ rhs) KA_ineq_over).
- exists (fun z => (lhs z, rhs)). intros z. reflexivity.
- exists (fun n => Some n). intros n. exists n. reflexivity.
- apply: discrete_prod; apply/discrete_iff; constructor; exact: ka_term_eq_dec.
- exact: KA_ineq_over_enumerable.
Qed.

End SliceEnumerable.
