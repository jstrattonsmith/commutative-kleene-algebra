(* stdpp adapter: a [Countable] type is enumerable, and an [EqDecision]
   is a decider for equality. The core lemmas of RuleEnum.v can then be
   used with stdpp-style hypotheses. *)

From stdpp Require Import base countable.
Require Import RuleEnum.RuleEnum.

Lemma countable_enumeratorT (X : Type) `{Countable X} :
  enumeratorT (@decode_nat X _ _).
Proof. intros x; exists (encode_nat x); apply decode_encode_nat. Qed.

Corollary countable_enumerableT (X : Type) `{Countable X} : enumerableT X.
Proof. exists decode_nat; apply countable_enumeratorT. Qed.

Definition eq_dec_of_EqDecision {Y : Type} `{EqDecision Y} :
  forall y1 y2 : Y, {y1 = y2} + {y1 <> y2} :=
  fun y1 y2 => decide (y1 = y2).
