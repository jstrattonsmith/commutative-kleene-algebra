(* KA unification: given equations between terms over letters and
   variables, is there a substitution of terms for the variables that
   makes every equation hold? A term with variables is a `ka_term` over
   words of `A + nat` (`inl` a letter, `inr i` the variable `X_i`), and a
   substitution is a list of terms over `A` (`X_i` ↦ the `i`-th entry, ⊥
   past the end), so that witnesses are countable.

   The problem `unif E` is stated for any relation `E` on terms. We use
   two: pre-KA equality `≡` (`preka_eqv`) and KA provability
   `FKA e1 ≡ FKA e2` (`fka_eqv`, KA/ka.v). A solution modulo any theory
   sound for languages is a language-level one (`unif_lsolves`), and
   both theories are enumerable, hence so is `unif E`
   (`unif_enumerable`). *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list countable.
From Undecidability.Synthetic Require Import Definitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.algebra KA.pre_ka KA.lang KA.ka.
From kacc Require Import KA.rules_enumerable KA.preka_enumerable.
From kacc Require Import KA.ka_enumerable.

Section Syntax.

Context {A : setoid}.

Notation W := (list_monoid A).

(** Terms with variables, equations and substitution. *)

Definition uterm := ka_term (list (A + nat)).
Definition ueq := (uterm * uterm)%type.

Definition usym (σ : list (ka_term W)) (c : A + nat) : ka_term W :=
  match c with inl a => Unit [a] | inr i => nth i σ ⊥ end.

Definition subst (σ : list (ka_term W)) : uterm → ka_term W :=
  ka_term_elim (S := ka_term_pre_ka W) (λ w, ∏ c ∈ w, usym σ c).

Definition unif (E : ka_term W → ka_term W → Prop) (eqs : list ueq) :=
  ∃ σ, ∀ p, p ∈ eqs → E (subst σ p.1) (subst σ p.2).

Lemma unif_mono (E E' : ka_term W → ka_term W → Prop) eqs :
  (∀ e1 e2, E e1 e2 → E' e1 e2) → unif E eqs → unif E' eqs.
Proof. by move=> HE [σ Hσ]; exists σ => p /Hσ /HE. Qed.

(** The same substitution, in languages. *)

Definition lsym (ρ : nat → lang W) (c : A + nat) : lang W :=
  match c with inl a => lang_sing [a] | inr i => ρ i end.

Definition lsubst (ρ : nat → lang W) : uterm → lang W :=
  ka_term_elim (S := lang_pre_ka W) (λ w, ∏ c ∈ w, lsym ρ c).

Definition lsolves (ρ : nat → lang W) (eqs : list ueq) :=
  ∀ p, p ∈ eqs → lsubst ρ p.1 ≡ lsubst ρ p.2.

Fixpoint uvars (e : uterm) : list nat :=
  match e with
  | Unit w => omap (λ c, match c with inl _ => None | inr i => Some i end) w
  | ka_term_bottom => []
  | ka_term_join e1 e2 | ka_term_mul e1 e2 => uvars e1 ++ uvars e2
  | ka_term_star e => uvars e
  end.

Lemma mul_list_cons {T : monoid} {X} (f : X → T) x xs :
  mul_list f (x :: xs) = f x ⋅ mul_list f xs.
Proof. by []. Qed.

Lemma lsubst_ext ρ ρ' e :
  (∀ i, i ∈ uvars e → ρ i ≡ ρ' i) → lsubst ρ e ≡ lsubst ρ' e.
Proof.
rewrite /lsubst; elim: e => /=.
- elim=> [|[a|i] w IH] H //; rewrite !mul_list_cons.
  + by rewrite IH.
  + rewrite [lsym ρ _]/= [lsym ρ' _]/= (H i); first exact: elem_of_list_here.
    by rewrite IH // => j Hj; apply: H; apply: elem_of_list_further.
- by [].
- move=> e1 IH1 e2 IH2 H.
  by rewrite IH1 ?IH2 // => i Hi; apply: H; apply/elem_of_app; auto.
- move=> e1 IH1 e2 IH2 H.
  by rewrite IH1 ?IH2 // => i Hi; apply: H; apply/elem_of_app; auto.
- by move=> e IH H; rewrite IH.
Qed.

Lemma l_subst σ e : l (subst σ e) ≡ lsubst (λ i, l (nth i σ ⊥)) e.
Proof.
rewrite /subst /lsubst; elim: e => /=.
- move=> w; rewrite [l _](monoid_morphism_mul_list (f := @l W)).
  by apply: mul_list_proper => // - [a|i].
- exact: pre_ka_morphism_bottom.
- by move=> e1 IH1 e2 IH2; rewrite pre_ka_morphism_join IH1 IH2.
- by move=> e1 IH1 e2 IH2; rewrite pre_ka_morphism_mul IH1 IH2.
- by move=> e IH; rewrite pre_ka_morphism_star IH.
Qed.

(** The theories we unify modulo. *)

Definition preka_eqv (e1 e2 : ka_term W) : Prop := e1 ≡ e2.
Definition fka_eqv (e1 e2 : ka_term W) : Prop := FKA e1 ≡ FKA e2.

Lemma unif_lsolves E eqs :
  (∀ e1 e2, E e1 e2 → l e1 ≡ l e2) → unif E eqs → ∃ ρ, lsolves ρ eqs.
Proof.
move=> HE [σ Hσ]; exists (λ i, l (nth i σ ⊥)) => p /Hσ /HE.
by rewrite !l_subst.
Qed.

End Syntax.

(** * Enumerability *)

Section Enumerable.

Context {A : setoid} `{!LeibnizEquiv A, !EqDecision A, !Countable A}.

Notation W := (list_monoid A).

Lemma Forall2_of_exists {X Y} (R : X → Y → Prop) xs :
  (∀ x, x ∈ xs → ∃ y, R x y) → ∃ ys, Forall2 R xs ys.
Proof.
elim: xs => [|x xs IH] H; first by exists [].
have [y Hy] := H x (elem_of_list_here _ _).
have [ys Hys] := IH (λ x' Hx', H x' (elem_of_list_further _ _ _ Hx')).
by exists (y :: ys); constructor.
Qed.

Lemma Forall2_exists_l {X Y} (R : X → Y → Prop) xs ys x :
  Forall2 R xs ys → x ∈ xs → ∃ y, R x y.
Proof.
elim=> [/elem_of_nil []|x' y xs' ys' Hxy _ IH /elem_of_cons [->|/IH //]].
by exists y.
Qed.

(* A certificate is the equations, the substitution, and for each
   equation an index at which an enumerator of `E` produces it. *)
Lemma unif_enumerable (E : ka_term W → ka_term W → Prop) :
  enumerable (λ p : ka_term W * ka_term W, E p.1 p.2) →
  enumerable (unif E).
Proof.
move=> [g Hg].
apply: (checker_enumerable (D := list ueq * list (ka_term W) * list nat)
  (check := λ d,
     if bool_decide (Forall2 (λ p n, g n = Some (subst d.1.2 p.1,
                                                 subst d.1.2 p.2))
                       d.1.1 d.2)
     then Some d.1.1 else None)).
- move=> [[eqs σ] ns] x /=; case_bool_decide as Hok => // - [<-].
  exists σ => p Hp.
  have [n Hn] := Forall2_exists_l Hok Hp.
  by apply/(Hg (_, _)); exists n.
- move=> eqs [σ Hσ].
  have [ns Hns] : ∃ ns,
    Forall2 (λ p n, g n = Some (subst σ p.1, subst σ p.2)) eqs ns.
  { apply: Forall2_of_exists => p /Hσ /(Hg (_, _)) [n Hn]; by exists n. }
  by exists (eqs, σ, ns) => /=; rewrite bool_decide_eq_true_2.
Qed.

Lemma W_leibniz : LeibnizEquiv (monoid_car W).
Proof. apply _. Qed.

Lemma preka_eqv_enumerable :
  enumerable (λ p : ka_term W * ka_term W, preka_eqv p.1 p.2).
Proof. exact: ka_eq_enumerable (T_equiv_enumerable W_leibniz). Qed.

Lemma fka_eqv_enumerable :
  enumerable (λ p : ka_term W * ka_term W, fka_eqv p.1 p.2).
Proof.
apply: (enumerable_reduce (f := λ p : ka_term W * ka_term W,
                                  (Unit p.1, Unit p.2))
          (Q := λ p : ka_term (ka_term W) * _, free_ka_eq p.1 p.2)).
- by [].
- exact: fka_eq_enumerable W_leibniz.
Qed.

End Enumerable.
