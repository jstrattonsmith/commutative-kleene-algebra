(* Follow-up to Theorem17_KATerm.v, prompted by the observation that
   Undecidability/enumerable.v (already in _CoqProject) proves exactly
   the "provability from a finite axiomatisation is r.e." bridge needed
   to show K enumerable: ka_sqsubseteq_enumerable shows that ⊑ on
   ka_term T is enumerable whenever the carrier monoid T's own ≡ is.
   mm.v's carrier (for a fixed program P := progOf c) is
   list (mm_sym Q) * list (mm_sym Q) with Q := fin (S (S (length P))) --
   a product of free monoids over a finite, decidable-equality alphabet,
   so its ≡ is decidable, hence enumerable for free. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
Require Import ssreflect.
From stdpp Require Import base countable fin finite.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts
  DecidabilityFacts MoreReducibilityFacts.
From kacc Require Import algebra pre_ka enumerable.
Require kacc.mm.
From kacc Require Import EffectiveInseparability_MM2.
From kacc Require Import Theorem17_KATerm.

Section KEnumerable.

Variable c : nat.

Notation Prog := (progOf c).
Let QF : Type := fin (S (S (length Prog))).

Instance QF_eqdec : EqDecision QF.
Proof. apply _. Defined.

Instance QF_finite : Finite QF.
Proof. apply _. Defined.

(* Supply the carrier monoid as an explicit `monoid` record (not a bare
   product type) -- `ka_term_sqsubseteq`/the algebra instances are
   registered for `T : monoid` and Coq's typeclass search does not
   reliably reverse-engineer a `monoid` record from a bare carrier type
   the way Canonical Structure inference does during normal term
   elaboration. Giving the record explicitly sidesteps that. Its carrier
   (via the `monoid_car` coercion) is definitionally the same bare
   product `list (mm_sym QF) * list (mm_sym QF)` mm.v's own red_lb/
   red_ub are stated over, so terms convert without issue. *)
Definition TmMonoid : monoid :=
  prod_monoid (list_monoid (option_setoid (@mm.mm_sym_setoid QF)))
              (list_monoid (option_setoid (@mm.mm_sym_setoid QF))).

Notation Tm := (monoid_car TmMonoid).

Instance Tm_eqdec : EqDecision Tm.
Proof. apply _. Defined.

Instance mm_sym_QF_countable : Countable (mm.mm_sym QF).
Proof. apply finite_countable. Defined.

Instance Tm_countable : Countable Tm.
Proof. apply _. Defined.

Instance Tm_leibniz : LeibnizEquiv Tm.
Proof. apply _. Defined.

Instance Tm_equiv_dec (x y : Tm) : Decision (x ≡ y).
Proof.
destruct (decide (x = y)) as [-> | Hne].
- left. reflexivity.
- right. intros H % leibniz_equiv_iff. exact (Hne H).
Defined.

Lemma Tm_equiv_enumerable : enumerable (fun p : Tm * Tm => p.1 ≡ p.2).
Proof.
apply: dec_count_enum.
- exists (fun p => bool_decide (p.1 ≡ p.2)).
  intros p. unfold reflects. symmetry. apply bool_decide_eq_true.
- exact: (@countable_enumerableT (Tm * Tm) _ _).
Qed.

(* --- The actual general KA-term inequality relation over this
   carrier -- not K itself, which is only ever a SLICE of it (the
   right-hand side fixed to red_ub Prog). This is what the source
   paper's own Theorem 18/19 are stated over. K_to_KA_ineq below is
   the reduction witnessing that slice relationship; it is used twice,
   in opposite directions: here, to import enumerability FROM KA_ineq
   INTO K, and in Theorem19_Full.v, to transport m-completeness the
   other way, OUT of K and into KA_ineq (composed with
   red_m_transitive). *)

Definition KA_ineq : ka_term Tm * ka_term Tm -> Prop := fun p => p.1 ⊑ p.2.

Theorem KA_ineq_enumerable : enumerable KA_ineq.
Proof. exact: ka_sqsubseteq_enumerable Tm_equiv_enumerable. Qed.

Definition K_to_KA_ineq (z : nat) : ka_term Tm * ka_term Tm :=
  (mm.red_lb Prog ((1, (ps 1 * enc 2 (z_vec z), 0))%nat), mm.red_ub Prog).

Lemma K_to_KA_ineq_spec (z : nat) : K c z <-> KA_ineq (K_to_KA_ineq z).
Proof. reflexivity. Qed.

Theorem K_enumerable : enumerable (K c).
Proof.
apply: (@enumerable_red nat (ka_term Tm * ka_term Tm) (K c) KA_ineq).
- exists K_to_KA_ineq. exact: K_to_KA_ineq_spec.
- exists (fun n => Some n). intros n. exists n. reflexivity.
- apply: discrete_prod; apply/discrete_iff; constructor; exact: ka_term_eq_dec.
- exact: KA_ineq_enumerable.
Qed.

End KEnumerable.
