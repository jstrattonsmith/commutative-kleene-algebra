(* Generic enumerability lemmas, independent of KA: countable types are
   enumerable (`countable_enumerableT`), a checker over a countable type
   of certificates has an enumerable image (`checker_enumerable`),
   enumerability transfers back along reductions (`enumerable_reduce`),
   and the least predicate closed under a countable family of computable
   rules is enumerable (`rules_enumerable`). KA/preka_enumerable.v and
   KA/ka_enumerable.v instantiate the last one for `ka_eq` and
   `free_ka_eq`. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.
From Undecidability.Synthetic Require Import DecidabilityFacts.
From Undecidability.Synthetic Require Import MoreReducibilityFacts.
From stdpp Require Import base list countable decidable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Any countable type is enumerable in the sense of the library. *)
Lemma countable_enumerableT (X : Type) `{Countable X} : enumerable__T X.
Proof.
exists decode_nat => x; exists (encode_nat x); exact: decode_encode_nat.
Qed.

(** A relation is enumerable if some checker over a countable type of
    derivations computes exactly its graph: enumerate the derivations and
    keep what they prove. *)
Lemma checker_enumerable {X D : Type} `{Countable D}
    (R : X → Prop) (check : D → option X) :
  (∀ d x, check d = Some x → R x) →
  (∀ x, R x → ∃ d, check d = Some x) →
  enumerable R.
Proof.
move=> Hs Hc.
have [enD HenD] := @countable_enumerableT D _ _.
exists (fun n => match enD n with Some d => check d | None => None end).
move=> x; split.
- move=> /Hc [d Hd].
  by have [n Hn] := HenD d; exists n; rewrite Hn.
- move=> [n]; case E: (enD n) => [d|] // Hd.
  exact: Hs Hd.
Qed.

(** * Rule systems

    A predicate [R] on [X] that is the least set closed under a countable
    family of rules is enumerable, as long as each rule computes its
    conclusion (if any) from the list of its premises. A derivation is a
    postfix program over rule labels: [(l, n)] pops [n] conclusions off
    the stack and pushes the conclusion of [l] applied to them. Programs
    are lists, so they are countable as soon as the labels are. *)

Section RuleEnumerable.

Context {X L : Type} `{Countable L} (rule : L → list X → option X).

Fixpoint rule_run (p : list (L * nat)) (st : list X) : option (list X) :=
  match p with
  | [] => Some st
  | (l, n) :: p =>
      rule_run p st ≫= λ st', x ← rule l (take n st'); Some (x :: drop n st')
  end.

Lemma rule_run_app p q st : rule_run (p ++ q) st = rule_run q st ≫= rule_run p.
Proof.
elim: p => [|[l n] p IH] /=; first by case: (rule_run q st).
by rewrite IH; case: (rule_run q st).
Qed.

Lemma rule_run_sound (R : X → Prop) :
  (∀ l xs x, rule l xs = Some x → Forall R xs → R x) →
  ∀ p st st', rule_run p st = Some st' → Forall R st → Forall R st'.
Proof.
move=> Hs; elim=> [|[l n] p IH] st st' /=; first by move=> [<-].
case E: (rule_run p st) => [st0|] //=.
case Ex: (rule l (take n st0)) => [x|] //= [<-] HR.
have HR0 := IH _ _ E HR.
constructor; last by apply: Forall_drop.
by apply: (Hs l (take n st0)) => //; apply: Forall_take.
Qed.

Theorem rules_enumerable (R : X → Prop) :
  (∀ l xs x, rule l xs = Some x → Forall R xs → R x) →
  (∀ S : X → Prop, (∀ l xs x, rule l xs = Some x → Forall S xs → S x) →
     ∀ x, R x → S x) →
  enumerable R.
Proof.
move=> Hs Hc.
apply: (checker_enumerable
  (check := fun p => if rule_run p [] is Some [x] then Some x else None)).
- move=> p x; case E: (rule_run p []) => [[|y [|]]|] // [<-].
  have := rule_run_sound Hs E (Forall_nil R).
  by move=> HR; inversion HR.
- suff HS : ∀ x, R x → ∃ p, ∀ st, rule_run p st = Some (x :: st).
    by move=> x /HS [p Hp]; exists p; rewrite Hp.
  apply: (Hc (fun x => ∃ p, ∀ st, rule_run p st = Some (x :: st)))
    => l xs x Hx HSxs.
  have [q Hq] : ∃ q, ∀ st, rule_run q st = Some (xs ++ st).
    elim: xs {Hx} HSxs => [|y ys IH] HS; first by exists [].
    have [[p Hp] HSys] := Forall_cons_1 _ _ _ HS.
    have [q Hq] := IH HSys.
    by exists (p ++ q) => st; rewrite rule_run_app Hq /= Hp.
  exists ((l, length xs) :: q) => st /=.
  by rewrite Hq /= take_app_length Hx /= drop_app_length.
Qed.

End RuleEnumerable.

(** [enumerable_red] specialized to a countable source and a target with
    decidable equality, the shape of every reduction in this project. *)
Lemma enumerable_reduce {X Y : Type} `{Countable X} `{EqDecision Y}
    (P : X → Prop) (Q : Y → Prop) (f : X → Y) :
  (∀ x, P x ↔ Q (f x)) → enumerable Q → enumerable P.
Proof.
move=> Hf.
apply: (@enumerable_red X Y P Q).
- by exists f.
- exact: countable_enumerableT.
- apply/discrete_iff; constructor => x y.
  by case: (decide (x = y)); [left | right].
Qed.
