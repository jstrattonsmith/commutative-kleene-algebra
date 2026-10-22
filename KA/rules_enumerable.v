(* Project glue over RuleEnum/: its enumerability lemmas restated with
   stdpp's [Countable]/[EqDecision] as hypotheses and the Coq Library of
   Undecidability Proofs' [enumerable]/[enumerable__T] as conclusions,
   the shape used by KA/preka_enumerable.v (for `ka_eq`),
   KA/ka_enumerable.v (for `free_ka_eq`) and CKAUndec/KEnumerable.v.
   The proofs themselves live in RuleEnum/RuleEnum.v, which depends only
   on the Rocq Stdlib. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From stdpp Require Import base list countable decidable.
From kacc Require RuleEnum.RuleEnum RuleEnum.RuleEnumStdpp RuleEnum.RuleEnumUndec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Any countable type is enumerable in the sense of the library. *)
Lemma countable_enumerableT (X : Type) `{Countable X} : enumerable__T X.
Proof.
apply/RuleEnumUndec.enumerableT_iff.
exact: RuleEnumStdpp.countable_enumerableT.
Qed.

(** A relation is enumerable if some checker over a countable type of
    derivations computes exactly its graph. *)
Lemma checker_enumerable {X D : Type} `{Countable D}
    (R : X → Prop) (check : D → option X) :
  (∀ d x, check d = Some x → R x) →
  (∀ x, R x → ∃ d, check d = Some x) →
  enumerable R.
Proof.
move=> Hs Hc; apply/RuleEnumUndec.enumerable_iff.
exact: (RuleEnum.checker_enumerable check R
          (RuleEnumStdpp.countable_enumerableT D) Hs Hc).
Qed.

(** The least predicate closed under a countable family of computable
    rules is enumerable. *)
Theorem rules_enumerable {X L : Type} `{Countable L}
    (rule : L → list X → option X) (R : X → Prop) :
  (∀ l xs x, rule l xs = Some x → Forall R xs → R x) →
  (∀ S : X → Prop, (∀ l xs x, rule l xs = Some x → Forall S xs → S x) →
     ∀ x, R x → S x) →
  enumerable R.
Proof.
move=> Hs Hc; apply/RuleEnumUndec.enumerable_iff.
exact: (RuleEnum.rules_enumerable rule R
          (RuleEnumStdpp.countable_enumerableT L) Hs Hc).
Qed.

(** Enumerability transfers back along reductions from a countable
    source to a target with decidable equality, the shape of every
    reduction in this project. *)
Lemma enumerable_reduce {X Y : Type} `{Countable X} `{EqDecision Y}
    (P : X → Prop) (Q : Y → Prop) (f : X → Y) :
  (∀ x, P x ↔ Q (f x)) → enumerable Q → enumerable P.
Proof.
move=> Hf /RuleEnumUndec.enumerable_iff HQ; apply/RuleEnumUndec.enumerable_iff.
exact: (RuleEnum.enumerable_reduce P Q f
          (RuleEnumStdpp.countable_enumerableT X)
          RuleEnumStdpp.eq_dec_of_EqDecision Hf HQ).
Qed.
