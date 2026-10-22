(* Worked examples for RuleSystem.v: a single relation ([le]), then a
   pair of mutual predicates ([even]/[odd]). In both, the proofs reduce
   to [rules_closed] and [induction] followed by [by_rule]. *)

From Stdlib Require Import List Arith.
Import ListNotations.
Require Import RuleEnum.RuleEnum RuleEnum.RuleSystem.

(** ** A single relation: [le] on pairs *)

Inductive le_label := L_le_n (n : nat) | L_le_S (n m : nat).

Definition le_premises (l : le_label) : list (nat * nat) :=
  match l with L_le_n _ => [] | L_le_S n m => [(n, m)] end.

Definition le_conclusion (l : le_label) : nat * nat :=
  match l with L_le_n n => (n, n) | L_le_S n m => (n, S m) end.

Lemma le_label_enumerableT : enumerableT le_label.
Proof.
  exists (fun k => option_map
            (fun s => match s with inl n => L_le_n n | inr (n, m) => L_le_S n m end)
            (sum_enum (fun n => Some n) (prod_enum (fun n => Some n) (fun n => Some n)) k)).
  apply map_enumeratorT.
  - exact (sum_enumeratorT nat_enumeratorT
             (prod_enumeratorT nat_enumeratorT nat_enumeratorT)).
  - intros [n|n m]; [now exists (inl n) | now exists (inr (n, m))].
Qed.

Definition nat_pair_eq_dec : forall x y : nat * nat, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Theorem le_enumerable : enumerable (fun p : nat * nat => fst p <= snd p).
Proof.
  apply (rule_system_enumerable_noax nat_pair_eq_dec le_premises le_conclusion).
  - exact le_label_enumerableT.
  - rules_closed.
  - intros S HS [n m]; cbn; induction 1; by_rule.
Qed.

(** ** Mutual predicates: [even] and [odd] *)

Inductive even : nat -> Prop :=
  | ev0 : even 0
  | evS n : odd n -> even (S n)
with odd : nat -> Prop :=
  | odS n : even n -> odd (S n).

Scheme even_min := Minimality for even Sort Prop
with   odd_min  := Minimality for odd  Sort Prop.
Combined Scheme even_odd_min from even_min, odd_min.

(** Judgments are [inl n] ("[n] is even") and [inr n] ("[n] is odd"). *)
Inductive eo_label := L_ev0 | L_evS (n : nat) | L_odS (n : nat).

Definition eo_premises (l : eo_label) : list (nat + nat) :=
  match l with L_ev0 => [] | L_evS n => [inr n] | L_odS n => [inl n] end.

Definition eo_conclusion (l : eo_label) : nat + nat :=
  match l with L_ev0 => inl 0 | L_evS n => inl (S n) | L_odS n => inr (S n) end.

Lemma eo_label_enumerableT : enumerableT eo_label.
Proof.
  exists (fun k => option_map
            (fun s => match s with
                      | inl (inl tt) => L_ev0
                      | inl (inr n) => L_evS n
                      | inr n => L_odS n
                      end)
            (sum_enum (sum_enum (fun _ => Some tt) (fun n => Some n))
                      (fun n => Some n) k)).
  apply map_enumeratorT.
  - refine (sum_enumeratorT (sum_enumeratorT _ nat_enumeratorT) nat_enumeratorT).
    intros []; now exists 0.
  - intros [|n|n]; [now exists (inl (inl tt)) | now exists (inl (inr n))
                   | now exists (inr n)].
Qed.

Theorem even_odd_enumerable : enumerable even /\ enumerable odd.
Proof.
  apply (rule_system_enumerable_mutual Nat.eq_dec Nat.eq_dec
           eo_premises eo_conclusion (fun _ => False)).
  - exact eo_label_enumerableT.
  - apply enumerable_empty.
  - rules_closed.
  - intros S1 S2 HS; apply even_odd_min; intros; by_rule.
Qed.
