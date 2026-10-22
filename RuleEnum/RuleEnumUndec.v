(* Adapter for the Coq Library of Undecidability Proofs. RuleEnum.v's
   enumerability notions are definitionally the library's, so results
   transfer in both directions by conversion. *)

From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
Require RuleEnum.RuleEnum.

Lemma enumerator_iff {X} (f : nat -> option X) (P : X -> Prop) :
  RuleEnum.enumerator f P <-> Definitions.enumerator f P.
Proof. reflexivity. Qed.

Lemma enumerable_iff {X} (P : X -> Prop) :
  RuleEnum.enumerable P <-> Definitions.enumerable P.
Proof. reflexivity. Qed.

Lemma enumeratorT_iff {X} (f : nat -> option X) :
  RuleEnum.enumeratorT f <-> enumerator__T f X.
Proof. reflexivity. Qed.

Lemma enumerableT_iff (X : Type) :
  RuleEnum.enumerableT X <-> enumerable__T X.
Proof. reflexivity. Qed.
