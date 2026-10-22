(* A schematic front end to [rules_enumerable], with tactics.

   Instead of a partial function from premises to conclusions, a rule
   system is given by:

   - a label type [L], with one label per rule instance, carrying every
     metavariable of that instance (including any that the premises
     would also determine);
   - [premises : L -> list X] and [conclusion : L -> X];
   - optionally, an enumerable set [Ax] of axioms, for base facts known
     only through an enumerator (an enumerable but undecidable side
     relation, a theory given as an enumerable set, ...).

   With this interface both proof obligations have the shape of the
   predicate's own constructors, and there is no rule function to invert.

   - [closed_under R]: every axiom is in [R], and for every label, if
     its premises are in [R] then so is its conclusion.
   - Minimality: [R] is contained in every [S] that is [closed_under].
     This is proved by [induction] on [R] followed by [by_rule] in each
     case.

   The price is decidable equality on [X], which the derived rule
   function uses to compare actual premises against [premises l].

   Tactics:
   - [rules_closed] reduces [closed_under R] to one goal per label,
     stated with the premises as hypotheses. It tries [econstructor;
     eauto] on each and leaves whatever that cannot solve.
   - [by_rule] proves a goal [S c] from a closedness hypothesis in
     context, trying each constructor of the label type in turn. Its
     arguments are found by unifying [conclusion l] with [c] and the
     premises by [eassumption]. For a label that is not determined this
     way (e.g. data that must be computed, as in HSCEnumerable.v), use
     [by_rule_with (MyLabel args)].
   - [by_axiom] closes a goal [S x] from a hypothesis [Ax x].

   [by_rule] tries constructors 1 to 16 by index. Labels should be a
   dedicated inductive type whose constructors carry the data directly,
   not a nested sum. *)

From Stdlib Require Import List.
Import ListNotations.
Require Import RuleEnum.RuleEnum.

Section RuleSystem.

Context {X L : Type} (eqX : forall x y : X, {x = y} + {x <> y}).
Context (premises : L -> list X) (conclusion : L -> X) (Ax : X -> Prop).

Definition closed_under (S : X -> Prop) : Prop :=
  (forall x, Ax x -> S x) /\
  (forall l, Forall S (premises l) -> S (conclusion l)).

Lemma closed_under_ext (S S' : X -> Prop) :
  (forall x, S x <-> S' x) -> closed_under S -> closed_under S'.
Proof.
  intros HS [HAx Hr]; split.
  - intros x Hx; apply HS, HAx, Hx.
  - intros l HF; apply HS, Hr.
    eapply Forall_impl; [|exact HF]; intros x; apply HS.
Qed.

(** The rule function behind the interface: label [inl n] is the [n]-th
    enumerated axiom; label [inr l] fires on exactly [premises l]. *)
Definition schema_rule (eAx : nat -> option X) (l : nat + L) (xs : list X) :
    option X :=
  match l, xs with
  | inl n, [] => eAx n
  | inl _, _ :: _ => None
  | inr l, xs =>
      if list_eq_dec eqX xs (premises l) then Some (conclusion l) else None
  end.

Theorem rule_system_enumerable (R : X -> Prop) :
  enumerableT L ->
  enumerable Ax ->
  closed_under R ->
  (forall S, closed_under S -> forall x, R x -> S x) ->
  enumerable R.
Proof.
  intros [eL HeL] [eAx HeAx] [HAx Hr] Hleast.
  apply (rules_enumerable (schema_rule eAx)).
  - exists (sum_enum (fun n => Some n) eL).
    exact (sum_enumeratorT nat_enumeratorT HeL).
  - intros [n|l] xs x H HF; cbn in H.
    + destruct xs; [|discriminate].
      apply HAx, HeAx; now exists n.
    + destruct (list_eq_dec eqX xs (premises l)) as [->|]; [|discriminate].
      injection H as <-; exact (Hr l HF).
  - intros S HS; apply Hleast; split.
    + intros x [n Hn]%HeAx; exact (HS (inl n) [] x Hn (Forall_nil _)).
    + intros l HF; apply (HS (inr l) (premises l)); [|exact HF]; cbn.
      now destruct (list_eq_dec eqX (premises l) (premises l)).
Qed.

Lemma enumerable_empty : enumerable (fun _ : X => False).
Proof. exists (fun _ => None); intros x; split; [intros []|intros [_ H]; discriminate]. Qed.

End RuleSystem.

(** Without axioms. *)
Corollary rule_system_enumerable_noax {X L : Type}
    (eqX : forall x y : X, {x = y} + {x <> y})
    (premises : L -> list X) (conclusion : L -> X) (R : X -> Prop) :
  enumerableT L ->
  closed_under premises conclusion (fun _ => False) R ->
  (forall S, closed_under premises conclusion (fun _ => False) S ->
     forall x, R x -> S x) ->
  enumerable R.
Proof.
  intros HL; apply (rule_system_enumerable eqX premises conclusion); auto.
  apply enumerable_empty.
Qed.

(** * Mutual predicates

    Two mutual predicates [R1 : A -> Prop] and [R2 : B -> Prop] are one
    predicate [sum_pred R1 R2] on tagged judgments [A + B]. The
    minimality obligation is stated for a pair of predicates, which is
    exactly the conclusion of a [Combined Scheme] of the two
    [Minimality] schemes. *)

Definition sum_pred {A B} (P : A -> Prop) (Q : B -> Prop) (x : A + B) : Prop :=
  match x with inl a => P a | inr b => Q b end.

Definition sum_eq_dec {A B}
    (eqA : forall x y : A, {x = y} + {x <> y})
    (eqB : forall x y : B, {x = y} + {x <> y}) :
  forall x y : A + B, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Theorem rule_system_enumerable_mutual {A B L : Type}
    (eqA : forall x y : A, {x = y} + {x <> y})
    (eqB : forall x y : B, {x = y} + {x <> y})
    (premises : L -> list (A + B)) (conclusion : L -> A + B)
    (Ax : A + B -> Prop) (R1 : A -> Prop) (R2 : B -> Prop) :
  enumerableT L ->
  enumerable Ax ->
  closed_under premises conclusion Ax (sum_pred R1 R2) ->
  (forall S1 S2, closed_under premises conclusion Ax (sum_pred S1 S2) ->
     (forall a, R1 a -> S1 a) /\ (forall b, R2 b -> S2 b)) ->
  enumerable R1 /\ enumerable R2.
Proof.
  intros HL HAx Hcl Hleast.
  assert (H : enumerable (sum_pred R1 R2)).
  { apply (rule_system_enumerable (sum_eq_dec eqA eqB) premises conclusion Ax);
      auto.
    intros S HS.
    assert (HS' : closed_under premises conclusion Ax
                    (sum_pred (fun a => S (inl a)) (fun b => S (inr b)))).
    { apply (closed_under_ext premises conclusion Ax S); [|exact HS].
      intros []; reflexivity. }
    destruct (Hleast _ _ HS') as [H1 H2].
    intros [a|b]; cbn; [apply H1 | apply H2]. }
  exact (conj (enumerable_inl _ H) (enumerable_inr _ H)).
Qed.

(** * Tactics *)

Ltac destruct_Forall :=
  repeat match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [? H]
  end.

Ltac rules_closed :=
  split;
  [ intros ?x ?Hx
  | intros ?l; destruct l; cbn; intros ?HF; destruct_Forall; cbn in * ];
  try solve [contradiction | econstructor; eauto].

Ltac premises_from_context :=
  cbn; repeat (apply Forall_cons; [eassumption|]); apply Forall_nil.

(** Apply the closedness hypothesis at the label built by [mk]. *)
Ltac rule_by mk :=
  match goal with
  | Hcl : closed_under _ _ _ _ |- _ =>
      destruct Hcl as [?HAx ?Hr]; rule_by mk
  | Hr : forall l, Forall _ _ -> _ |- _ =>
      eapply (Hr ltac:(mk)); premises_from_context
  end.

Ltac by_rule_with l := rule_by ltac:(exact l).

Ltac by_rule :=
  first [ rule_by ltac:(econstructor 1)  | rule_by ltac:(econstructor 2)
        | rule_by ltac:(econstructor 3)  | rule_by ltac:(econstructor 4)
        | rule_by ltac:(econstructor 5)  | rule_by ltac:(econstructor 6)
        | rule_by ltac:(econstructor 7)  | rule_by ltac:(econstructor 8)
        | rule_by ltac:(econstructor 9)  | rule_by ltac:(econstructor 10)
        | rule_by ltac:(econstructor 11) | rule_by ltac:(econstructor 12)
        | rule_by ltac:(econstructor 13) | rule_by ltac:(econstructor 14)
        | rule_by ltac:(econstructor 15) | rule_by ltac:(econstructor 16) ].

Ltac by_axiom :=
  match goal with
  | Hcl : closed_under _ _ _ _ |- _ => destruct Hcl as [?HAx ?Hr]; by_axiom
  | HAx : forall x, _ x -> _ x |- _ => apply HAx; eauto
  end.
