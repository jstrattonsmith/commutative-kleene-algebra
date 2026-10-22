(* An application of RuleEnum.v to the Coq Library of Undecidability
   Proofs: derivability in a Hilbert-style calculus ([hsc] from
   Undecidability.HilbertCalculi.HSC) is enumerable, uniformly in the
   list of axioms.

   This is the dual of the library's HSC_PRV_undec. It shows the two
   ways labels handle data the premises cannot supply:

   - [hsc_var] quantifies over a substitution [ζ : nat -> formula], which
     is not enumerable. Only its values on the variables of the axiom
     matter, so the label carries that finite prefix
     ([list_subst_spec]).
   - [hsc_arr] has two premises that must agree on the antecedent and
     the axioms, which the rule checks with decidable equality.

   [formula_enumerableT] is itself an instance of [rules_enumerable],
   with [R := fun _ => True]: every inductive type whose non-recursive
   arguments are enumerable is enumerable.

   Needs only HilbertCalculi/HSC.v, which itself depends only on the
   Rocq Stdlib. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From Undecidability.HilbertCalculi Require Import HSC.
Require Import RuleEnum.RuleEnum.

(** * Formulas *)

Definition formula_eq_dec : forall s t : formula, {s = t} + {s <> t}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** [inl n] builds [var n]; [inr tt] builds [arr s t] from [s] and [t]. *)
Definition formula_rule (l : nat + unit) (ps : list formula) : option formula :=
  match l, ps with
  | inl n, [] => Some (var n)
  | inr tt, [s; t] => Some (arr s t)
  | _, _ => None
  end.

Lemma formula_enumerableT : enumerableT formula.
Proof.
  destruct (rules_enumerable formula_rule (fun _ => True)) as [f Hf].
  - exists (sum_enum (fun n => Some n) (fun _ => Some tt)).
    apply sum_enumeratorT; [exact nat_enumeratorT | intros []; now exists 0].
  - auto.
  - intros S HS t _; induction t as [n|s IHs t IHt].
    + exact (HS (inl n) [] _ eq_refl (Forall_nil _)).
    + exact (HS (inr tt) [s; t] _ eq_refl
               (Forall_cons _ IHs (Forall_cons _ IHt (Forall_nil _)))).
  - exists f; intros t; exact (proj1 (Hf t) I).
Qed.

(** * Finite substitutions

    [substitute ζ t] depends only on [ζ] below [fv_bound t], so it is
    determined by the finite list [map ζ (seq 0 (fv_bound t))]. *)

Fixpoint fv_bound (t : formula) : nat :=
  match t with
  | var n => S n
  | arr s t => Nat.max (fv_bound s) (fv_bound t)
  end.

Lemma substitute_ext (ζ1 ζ2 : nat -> formula) t :
  (forall n, n < fv_bound t -> ζ1 n = ζ2 n) ->
  substitute ζ1 t = substitute ζ2 t.
Proof.
  induction t as [n|s IHs t IHt]; cbn; intros H.
  - apply H; lia.
  - rewrite IHs, IHt; [reflexivity| |]; intros n Hn; apply H; lia.
Qed.

Definition list_subst (ζs : list formula) (n : nat) : formula :=
  nth n ζs (var n).

Lemma list_subst_spec (ζ : nat -> formula) t :
  substitute (list_subst (map ζ (seq 0 (fv_bound t)))) t = substitute ζ t.
Proof.
  apply substitute_ext; intros n Hn; unfold list_subst.
  rewrite (nth_indep _ (var n) (ζ 0)) by now rewrite length_map, length_seq.
  now rewrite map_nth, seq_nth.
Qed.

(** * Derivability *)

(** Labels: [inl (Gamma, i, ζs)] instantiates the [i]-th axiom of
    [Gamma] by the finite substitution [ζs]; [inr tt] is modus ponens. *)
Definition hsc_rule (l : list formula * nat * list formula + unit)
    (ps : list (list formula * formula)) : option (list formula * formula) :=
  match l, ps with
  | inl (Gamma, i, ζs), [] =>
      match nth_error Gamma i with
      | Some t => Some (Gamma, substitute (list_subst ζs) t)
      | None => None
      end
  | inr tt, [(Gamma1, arr s t); (Gamma2, s')] =>
      if list_eq_dec formula_eq_dec Gamma1 Gamma2 then
        if formula_eq_dec s s' then Some (Gamma1, t) else None
      else None
  | _, _ => None
  end.

Theorem hsc_enumerable :
  enumerable (fun p : list formula * formula => hsc (fst p) (snd p)).
Proof.
  destruct formula_enumerableT as [eF HeF].
  apply (rules_enumerable hsc_rule).
  - exists (sum_enum
              (prod_enum (prod_enum (list_enum eF) (fun n => Some n))
                         (list_enum eF))
              (fun _ => Some tt)).
    apply sum_enumeratorT; [|intros []; now exists 0].
    apply prod_enumeratorT; [apply prod_enumeratorT|];
      auto using list_enumeratorT, nat_enumeratorT.
  - intros [[[Gamma i] ζs]|[]] ps [G t] H HF.
    + destruct ps; [|discriminate]; cbn in H.
      destruct (nth_error Gamma i) as [t0|] eqn:E; [|discriminate].
      injection H as <- <-; cbn.
      apply hsc_var, (nth_error_In _ i E).
    + destruct ps as [|[G1 [n|s t']] [|[G2 s'] [|]]]; cbn in H;
        try discriminate.
      destruct (list_eq_dec formula_eq_dec G1 G2) as [<-|]; [|discriminate].
      destruct (formula_eq_dec s s') as [<-|]; [|discriminate].
      injection H as <- <-; cbn.
      eapply hsc_arr; [exact (Forall_inv HF) | exact (Forall_inv (Forall_inv_tail HF))].
  - intros S HS [G t]; cbn; induction 1 as [ζ t Hin|s t _ IH1 _ IH2].
    + destruct (In_nth_error _ _ Hin) as [i Hi].
      rewrite <- (list_subst_spec ζ t).
      apply (HS (inl (G, i, map ζ (seq 0 (fv_bound t)))) []);
        [cbn; now rewrite Hi | constructor].
    + apply (HS (inr tt) [(G, arr s t); (G, s)]); [cbn | now repeat constructor].
      destruct (list_eq_dec formula_eq_dec G G); [|contradiction].
      now destruct (formula_eq_dec s s).
Qed.

(** For a fixed list of axioms, the library's [HSC_PRV] problem. *)
Corollary HSC_PRV_enumerable (Gamma : list formula) :
  enumerable (HSC_PRV Gamma).
Proof.
  apply (enumerable_reduce (HSC_PRV Gamma)
           (fun p : list formula * formula => hsc (fst p) (snd p))
           (fun s => (Gamma, s))).
  - exact formula_enumerableT.
  - intros [G1 s1] [G2 s2].
    destruct (list_eq_dec formula_eq_dec G1 G2) as [<-|];
      [destruct (formula_eq_dec s1 s2) as [<-|]|]; [left| right| right];
      congruence.
  - reflexivity.
  - exact hsc_enumerable.
Qed.
