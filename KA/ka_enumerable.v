(* Enumerability of derivability in KA: the analogue of
   KA/preka_enumerable.v for the free Kleene algebra of KA/ka.v. If the
   pre-KA equivalence on terms over a countable pre-KA `P` is enumerable,
   so is `free_ka_eq`: its derivations are reified as `DK` and checked by
   `checkK`, exactly as KA/preka_enumerable.v does for the pre-KA axioms,
   with two extra rules for star induction. `fka_le_slice_enumerable_r`
   packages the result for the KA ordering `FKA e1 ⊑ FKA e2` on terms over
   a discrete countable monoid, with a fixed left-hand side. *)

Require Import ssreflect.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From Undecidability.Synthetic Require Import DecidabilityFacts.
From Undecidability.Synthetic Require Import MoreReducibilityFacts.
From stdpp Require Import base countable decidable.
From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.preka_enumerable.
From kacc Require Import KA.ka.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FreeKAEqEnumerable.

Context (P : pre_ka) `{Countable (pre_ka_car P)}.

Implicit Types (e a b : ka_term P) (x y : P).

Inductive DK :=
  | K_refl (a : ka_term P)
  | K_sym (d : DK)
  | K_trans (d1 d2 : DK)
  | K_pre (k : nat)
  | K_join (d1 d2 : DK)
  | K_mul (d1 d2 : DK)
  | K_star (d : DK)
  | K_ubot
  | K_ujoin (x y : P)
  | K_ustar (x : P)
  | K_indl (d : DK)
  | K_indr (d : DK).

Global Instance DK_eq_dec : EqDecision DK.
Proof. solve_decision. Defined.

Notation DKleaf := (ka_term P + (nat + P))%type.

Global Instance DK_countable : Countable DK.
Proof.
set (enc :=
  fix go (d : DK) : gen_tree DKleaf :=
    match d with
    | K_refl a => GenNode 0 [GenLeaf (inl a)]
    | K_sym d => GenNode 1 [go d]
    | K_trans d1 d2 => GenNode 2 [go d1; go d2]
    | K_pre k => GenNode 3 [GenLeaf (inr (inl k))]
    | K_join d1 d2 => GenNode 4 [go d1; go d2]
    | K_mul d1 d2 => GenNode 5 [go d1; go d2]
    | K_star d => GenNode 6 [go d]
    | K_ubot => GenNode 7 []
    | K_ujoin x y => GenNode 8 [GenLeaf (inr (inr x)); GenLeaf (inr (inr y))]
    | K_ustar x => GenNode 9 [GenLeaf (inr (inr x))]
    | K_indl d => GenNode 10 [go d]
    | K_indr d => GenNode 11 [go d]
    end).
set (dec :=
  fix go (u : gen_tree DKleaf) : DK :=
    match u with
    | GenNode 0 [GenLeaf (inl a)] => K_refl a
    | GenNode 1 [u] => K_sym (go u)
    | GenNode 2 [u1; u2] => K_trans (go u1) (go u2)
    | GenNode 3 [GenLeaf (inr (inl k))] => K_pre k
    | GenNode 4 [u1; u2] => K_join (go u1) (go u2)
    | GenNode 5 [u1; u2] => K_mul (go u1) (go u2)
    | GenNode 6 [u] => K_star (go u)
    | GenNode 7 [] => K_ubot
    | GenNode 8 [GenLeaf (inr (inr x)); GenLeaf (inr (inr y))] => K_ujoin x y
    | GenNode 9 [GenLeaf (inr (inr x))] => K_ustar x
    | GenNode 10 [u] => K_indl (go u)
    | GenNode 11 [u] => K_indr (go u)
    | _ => K_ubot
    end).
refine (inj_countable' enc dec _).
by elim=> //= *; congruence.
Qed.

Section WithEnum.

Variable g : nat → option (ka_term P * ka_term P).

Definition ind_l_concl (p : ka_term P * ka_term P) :
    option (ka_term P * ka_term P) :=
  match p with
  | (ka_term_join (ka_term_join e2 (ka_term_mul e1 e3)) e3', e3'') =>
      if decide (e3 = e3' ∧ e3' = e3'') is left _ then
        Some (star e1 ⋅ e2 ⊔ e3, e3)
      else None
  | _ => None
  end.

Definition ind_r_concl (p : ka_term P * ka_term P) :
    option (ka_term P * ka_term P) :=
  match p with
  | (ka_term_join (ka_term_join e2 (ka_term_mul e3 e1)) e3', e3'') =>
      if decide (e3 = e3' ∧ e3' = e3'') is left _ then
        Some (e2 ⋅ star e1 ⊔ e3, e3)
      else None
  | _ => None
  end.

Lemma ind_l_concl_inv p a b :
  ind_l_concl p = Some (a, b) →
  ∃ e1 e2 e3, p = ((e2 ⊔ e1 ⋅ e3) ⊔ e3, e3) ∧
    a = star e1 ⋅ e2 ⊔ e3 ∧ b = e3.
Proof.
rewrite /ind_l_concl => Hc; repeat case_match; simplify_eq.
by destruct_and!; subst; eauto 10.
Qed.

Lemma ind_r_concl_inv p a b :
  ind_r_concl p = Some (a, b) →
  ∃ e1 e2 e3, p = ((e2 ⊔ e3 ⋅ e1) ⊔ e3, e3) ∧
    a = e2 ⋅ star e1 ⊔ e3 ∧ b = e3.
Proof.
rewrite /ind_r_concl => Hc; repeat case_match; simplify_eq.
by destruct_and!; subst; eauto 10.
Qed.

Fixpoint checkK (d : DK) : option (ka_term P * ka_term P) :=
  match d with
  | K_refl a => Some (a, a)
  | K_sym d =>
      match checkK d with Some (a, b) => Some (b, a) | None => None end
  | K_trans d1 d2 =>
      match checkK d1, checkK d2 with
      | Some (a, b), Some (b', c) =>
          if decide (b = b') is left _ then Some (a, c) else None
      | _, _ => None
      end
  | K_pre k => g k
  | K_join d1 d2 =>
      match checkK d1, checkK d2 with
      | Some (a, b), Some (c, e) => Some (a ⊔ c, b ⊔ e)
      | _, _ => None
      end
  | K_mul d1 d2 =>
      match checkK d1, checkK d2 with
      | Some (a, b), Some (c, e) => Some (a ⋅ c, b ⋅ e)
      | _, _ => None
      end
  | K_star d =>
      match checkK d with
      | Some (a, b) => Some (star a, star b)
      | None => None
      end
  | K_ubot => Some (Unit ⊥, ⊥)
  | K_ujoin x y => Some (Unit (x ⊔ y), Unit x ⊔ Unit y)
  | K_ustar x => Some (Unit (star x), star (Unit x))
  | K_indl d =>
      match checkK d with Some p => ind_l_concl p | None => None end
  | K_indr d =>
      match checkK d with Some p => ind_r_concl p | None => None end
  end.

Lemma checkK_sound :
  (∀ n a b, g n = Some (a, b) → a ≡ b) →
  ∀ d a b, checkK d = Some (a, b) → free_ka_eq a b.
Proof.
move=> Hg; elim.
- by move=> a0 a b [= <- <-]; exact: fk_refl.
- move=> d IH a b /=.
  case E: (checkK d) => [[a0 b0]|] //= [= <- <-].
  exact: fk_sym (IH _ _ E).
- move=> d1 IH1 d2 IH2 a b /=.
  case E1: (checkK d1) => [[a1 b1]|] //=.
  case E2: (checkK d2) => [[a2 b2]|] //=.
  case: (decide (b1 = a2)) => [e|_] //= [= <- <-].
  apply: fk_trans (IH1 _ _ E1) _; rewrite e; exact: IH2.
- by move=> k a b /= /Hg; exact: fk_pre.
- move=> d1 IH1 d2 IH2 a b /=.
  case E1: (checkK d1) => [[a1 b1]|] //=.
  case E2: (checkK d2) => [[a2 b2]|] //= [= <- <-].
  exact: fk_join_proper (IH1 _ _ E1) (IH2 _ _ E2).
- move=> d1 IH1 d2 IH2 a b /=.
  case E1: (checkK d1) => [[a1 b1]|] //=.
  case E2: (checkK d2) => [[a2 b2]|] //= [= <- <-].
  exact: fk_mul_proper (IH1 _ _ E1) (IH2 _ _ E2).
- move=> d IH a b /=.
  case E: (checkK d) => [[a0 b0]|] //= [= <- <-].
  exact: fk_star_proper (IH _ _ E).
- by move=> a b [= <- <-]; exact: fk_unit_bottom.
- by move=> x y a b [= <- <-]; exact: fk_unit_join.
- by move=> x a b [= <- <-]; exact: fk_unit_star.
- move=> d IH a b /=.
  case E: (checkK d) => [p|] //= /ind_l_concl_inv [e1 [e2 [e3 [Ep [-> ->]]]]].
  subst p; exact: fk_star_ind_l (IH _ _ E).
- move=> d IH a b /=.
  case E: (checkK d) => [p|] //= /ind_r_concl_inv [e1 [e2 [e3 [Ep [-> ->]]]]].
  subst p; exact: fk_star_ind_r (IH _ _ E).
Qed.

Lemma checkK_complete :
  (∀ a b, a ≡ b → ∃ n, g n = Some (a, b)) →
  ∀ e1 e2, free_ka_eq e1 e2 → ∃ d, checkK d = Some (e1, e2).
Proof.
move=> Hg e1 e2; elim.
- by move=> a; exists (K_refl a).
- by move=> a b _ [d Hd]; exists (K_sym d); rewrite /= Hd.
- move=> a b c _ [d1 H1] _ [d2 H2]; exists (K_trans d1 d2).
  by rewrite /= H1 H2 decide_True.
- by move=> a b /Hg [n Hn]; exists (K_pre n).
- move=> a a' b b' _ [d1 H1] _ [d2 H2].
  by exists (K_join d1 d2); rewrite /= H1 H2.
- move=> a a' b b' _ [d1 H1] _ [d2 H2].
  by exists (K_mul d1 d2); rewrite /= H1 H2.
- by move=> a b _ [d Hd]; exists (K_star d); rewrite /= Hd.
- by exists K_ubot.
- by move=> x y; exists (K_ujoin x y).
- by move=> x; exists (K_ustar x).
- move=> a b c _ [d Hd]; exists (K_indl d).
  by rewrite /= Hd /= decide_True.
- move=> a b c _ [d Hd]; exists (K_indr d).
  by rewrite /= Hd /= decide_True.
Qed.

End WithEnum.

Theorem free_ka_eq_enumerable :
  enumerable (fun p : ka_term P * ka_term P => p.1 ≡ p.2) →
  enumerable (fun p : ka_term P * ka_term P => free_ka_eq p.1 p.2).
Proof.
move=> [g Hg].
apply: (checker_enumerable (check := checkK g)).
- move=> d [a b] /=; apply: checkK_sound => n a' b' Hn.
  by apply/(Hg (a', b')); exists n.
- move=> [a b] /= Hab; apply: checkK_complete Hab.
  by move=> a' b' /(Hg (a', b')).
Qed.

End FreeKAEqEnumerable.

(** * The KA ordering on terms over a discrete countable monoid *)

Section KaLeqEnumerable.

Context (T : monoid).
Context `{HeqT : !RelDecision (@Logic.eq (monoid_car T))}.
Context `{!Countable (monoid_car T)} (HLeibniz : LeibnizEquiv (monoid_car T)).

Lemma fka_eq_enumerable :
  enumerable (fun p : ka_term (ka_term T) * ka_term (ka_term T) =>
                free_ka_eq p.1 p.2).
Proof.
apply: (@free_ka_eq_enumerable (ka_term_pre_ka T)).
apply: (@ka_eq_enumerable (ka_term_monoid T)).
apply: ka_eq_enumerable.
exact: T_equiv_enumerable HLeibniz.
Qed.

Lemma fka_le_iff (e1 e2 : ka_term T) :
  FKA e1 ⊑ FKA e2 ↔ free_ka_eq (Unit (e1 ⊔ e2)) (Unit e2).
Proof. exact: default_sqsubseteq_eq. Qed.

Theorem fka_le_slice_enumerable_r
    (lhs : ka_term T) (rhs : nat → ka_term T) :
  enumerable (fun z => FKA lhs ⊑ FKA (rhs z)).
Proof.
apply: (enumerable_reduce (f := fun z => (Unit (lhs ⊔ rhs z), Unit (rhs z)))
          (Q := fun p : ka_term (ka_term T) * _ => free_ka_eq p.1 p.2)).
- move=> z; exact: fka_le_iff.
- exact: fka_eq_enumerable.
Qed.

End KaLeqEnumerable.
