(* A first application of [rules_enumerable]: the reflexive-transitive
   closure of an enumerable relation on an enumerable type with
   decidable equality is enumerable. This covers reachability for
   string rewriting, machine step relations, etc.

   It also shows the general recipe for an inductive predicate. Each
   constructor becomes a label carrying the constructor's non-recursive
   arguments (here the point [x] of [rt_refl], or the index [n] of a
   step in the relation's enumerator). Each side condition is checked
   decidably by the rule (here, that the middle points of [rt_trans]
   agree). *)

From Stdlib Require Import List Relations.
Import ListNotations.
Require Import RuleEnum.RuleEnum.

Section ReflTrans.

Context {X : Type} (eqX : forall x y : X, {x = y} + {x <> y}).

(** Labels: [inl (inl x)] is reflexivity at [x], [inl (inr n)] is the
    [n]-th enumerated step, and [inr tt] is transitivity. *)
Definition rt_rule (eR : nat -> option (X * X)) (l : X + nat + unit)
    (ps : list (X * X)) : option (X * X) :=
  match l, ps with
  | inl (inl x), [] => Some (x, x)
  | inl (inr n), [] => eR n
  | inr tt, [(x, y); (y', z)] => if eqX y y' then Some (x, z) else None
  | _, _ => None
  end.

Theorem clos_refl_trans_enumerable (R : X -> X -> Prop) :
  enumerableT X ->
  enumerable (fun p : X * X => R (fst p) (snd p)) ->
  enumerable (fun p : X * X => clos_refl_trans X R (fst p) (snd p)).
Proof.
  intros [eX HeX] [eR HeR].
  apply (rules_enumerable (rt_rule eR)).
  - exists (sum_enum (sum_enum eX (fun n => Some n)) (fun _ => Some tt)).
    apply sum_enumeratorT; [apply sum_enumeratorT; [exact HeX | exact nat_enumeratorT]|].
    intros []; now exists 0.
  - intros [[x|n]|[]] ps [a b] H HF; cbn.
    + destruct ps; [|discriminate]; injection H as <- <-; apply rt_refl.
    + destruct ps; [|discriminate].
      apply rt_step, (proj2 (HeR (a, b))); now exists n.
    + destruct ps as [|[x y] [|[y' z] [|]]]; try discriminate; cbn in H.
      destruct (eqX y y') as [<-|]; [|discriminate].
      injection H as <- <-.
      apply rt_trans with y.
      * exact (Forall_inv HF).
      * exact (Forall_inv (Forall_inv_tail HF)).
  - intros S HS [x y]; cbn; induction 1 as [x y H|x|x y z _ IH1 _ IH2].
    + destruct (proj1 (HeR (x, y)) H) as [n Hn].
      exact (HS (inl (inr n)) [] (x, y) Hn (Forall_nil _)).
    + exact (HS (inl (inl x)) [] (x, x) eq_refl (Forall_nil _)).
    + apply (HS (inr tt) [(x, y); (y, z)]); [cbn|now repeat constructor].
      now destruct (eqX y y).
Qed.

End ReflTrans.
