Require Import Coq.Classes.Morphisms.
Require Import Coq.Unicode.Utf8.
Require Import ssreflect.
Require Import Coq.Setoids.Setoid.
Require Import Undecidability.MinskyMachines.MM2.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.

From Coq Require Import List. Import ListNotations.
From Coq Require Import Bool.

(* Require Import List Relations.Relation_Operators. *)

Check mm2_step.
Print mm2_step.

(* Print mm2_instr_at.
#[local] Set Implicit Arguments.
Check clos_refl_trans.
Check (clos_refl_trans _ (mm2_step _)). *)

(* ------- ------- *)
(* ------- Commuting Relations ------- *)
(* ------- ------- *)

Definition commuting_relation X (R : Relation_Definitions.relation X) :=
  Reflexive R /\ Symmetric R.

Definition commute X R (H : commuting_relation X R) (x y : X) := R x y.

Definition commutable X R := commuting_relation X R.

Definition discrete X R (H : commuting_relation X R) (x y : X) :=
  R x y <-> x = y. (* QUEST: what kind of equality is meant here? *)

Definition commutative X R (H : commuting_relation X R) :=
  ∀ (x y : X), commute X R H x y.

(* ------- ------- *)
(* ------- string over set ------- *)
(* ------- ------- *)
(* Inductive str (T : Type) : Type :=
  | empty
  | str_cons (c : T) (r : str T) : str T. *)

(* ------- ------- *)
(* ------- Pre-Kleene Algebra Specs ------- *)
(* ------- ------- *)

Inductive ka_term (T : Type) : Type :=
  | K_Zero
  | K_One
  | L (t : T)
  | R (t : T)
  (* | K_Var (t : T) *)
  | K_Plus (t1 t2 : ka_term T)
  | K_Dot (t1 t2 : ka_term T)
  | K_Star (t : ka_term T)
.

Arguments K_Zero {T}.
Arguments K_One {T}.
(* Arguments K_Var {T}. *)
Arguments L {T}.
Arguments R {T}.
Arguments K_Plus {T}.
Arguments K_Dot {T}.
Arguments K_Star {T}.

Declare Scope ka_scope.
Delimit Scope ka_scope with T.
Bind Scope ka_scope with ka_term.

Fixpoint ka_power {T} (x : ka_term T) (n : nat) :=
  match n with
  | 0 => K_One
  | S n => K_Dot x (ka_power x n)
  end.
Notation "x ^ n" := (ka_power x n) : ka_scope.

Notation "x + y" := (K_Plus x y) (at level 50, left associativity) : ka_scope.
Notation "x ⋅ y" := (K_Dot x y) (at level 40, left associativity) : ka_scope.
Notation "x ✶"   := (K_Star x) (at level 35) : ka_scope.
Notation "1"     := (K_One) : ka_scope.
Notation "0"     := (K_Zero) : ka_scope.

Definition lr_term {T} (x : T) := K_Dot (L x) (R x).

(* TODO: come back to scoping here *)
Notation "'lr' x" := (lr_term x) (at level 30, no associativity): ka_scope.

Reserved Notation "e1 ≐ e2" (at level 80, no associativity).

Inductive ka_eq {T : Type} : ka_term T -> ka_term T -> Prop :=
  | Ka_refl : Reflexive (@ka_eq T)
  | Ka_sym : Symmetric (@ka_eq T)
  | Ka_trans : Transitive (@ka_eq T)

  | Ka_Plus : Proper ((@ka_eq T) ==> (@ka_eq T) ==> (@ka_eq T)) K_Plus
  | Ka_Dot : Proper ((@ka_eq T) ==> (@ka_eq T) ==> (@ka_eq T)) K_Dot
  | Ka_Star : Proper ((@ka_eq T) ==> (@ka_eq T)) K_Star

  (* including the following to allow for commuting terms *)
  | LR_Com x y : (L x)⋅(R y) ≐ (R y)⋅(L x)

  | Dot_Id1 t : t ⋅ 1 ≐ t
  | Dot_Id2 t : 1 ⋅ t ≐ t
  | Dot_Z1  t : t ⋅ 0 ≐ 0
  | Dot_Z2  t : 0 ⋅ t ≐ 0
  | Dot_Assoc x y z : x ⋅ (y ⋅ z) ≐ (x ⋅ y) ⋅ z

  | Plus_Id t : 0 + t ≐ t
  | Plus_Com (x y : ka_term T) : x + y ≐ y + x
  | Plus_Assoc x y z : x + (y + z) ≐ (x + y) + z
  | Plus_Idemp x : x + x ≐ x

  | Dist_L x y z : x ⋅ (y + z) ≐ x⋅y + x⋅z
  | Dist_R x y z : (x + y) ⋅ z ≐ x⋅z + y⋅z

  | Star t : t✶ ≐ 1 + (t ⋅ (t✶))
  where "e1 ≐ e2" := (ka_eq e1 e2) : ka_scope.

Global Existing Instance Ka_refl.
Global Existing Instance Ka_sym.
Global Existing Instance Ka_trans.
Global Existing Instance Ka_Plus.
Global Existing Instance Ka_Dot.
Global Existing Instance Ka_Star.

Add Parametric Relation T : (ka_term T) ka_eq as ka_eq.

Definition ka_leq {T} (x y : ka_term T) : Prop := ((y + x) ≐ y)%T. (* this is a typo in the paper? *)
Notation "x ≤ y" := (ka_leq x y) : ka_scope.

(* Global Instance  *)

(* ------- ------- *)
(* ------- Interpreting MM instructions as terms ------- *)
(* ------- ------- *)

Section Theory.
Local Open Scope ka_scope.

Inductive Σ_M : Type :=
  | Q_M (n : nat)
  | a
  | b
  | c_0
  | c_1.

Lemma leq_reflex : forall T (t : ka_term T), t ≤ t.
Proof.
  intros. unfold ka_leq. apply Plus_Idemp.
Qed.

Hint Resolve leq_reflex : core.
Variable T : Type.
Implicit Types (e : ka_term T) (x y z : T).

Global Instance leq_proper :
  Proper (ka_eq ==> ka_eq ==> iff) (@ka_leq T).
Proof.
  rewrite /ka_leq => e1 e2 e12 e3 e4 e34.
  split.
  - intros. rewrite <- e34. rewrite <- e12. assumption.
  - intros. rewrite e12. rewrite e34. assumption.
Qed.

Lemma star_expand : forall (t : ka_term T), t✶ ≐ 1 + t⋅t✶.
Proof. intros. apply Star. Qed.

Lemma star_leq : forall (t : ka_term T), 1 + t⋅t✶ ≤ t✶.
Proof.
  intros.
  rewrite <- star_expand.
  apply leq_reflex.
Qed.

Lemma leq_antisym : forall (x y : ka_term T), x ≤ y -> y ≤ x -> x ≐ y.
Proof.
  intros.
  unfold ka_leq in H, H0.
  rewrite <- H. rewrite Plus_Com. symmetry. assumption.
Qed.

(* Lemma not_L_eq_0 : ∀ a : T, not (L a ≐ 0).
Proof.
  unfold not. intros.
  inversion
Admitted.

Lemma dot_eq_zero : ∀ e1 e2,  e1 ⋅ e2 ≐ 0 -> (e1 ≐ 0) \/ (e2 ≐ 0).
Proof.
  intros.
  induction e1.
  - left; reflexivity.
  - rewrite Dot_Id2 in H. right; assumption.
  - right. destruct e2.
    + reflexivity.
    + rewrite Dot_Id1 in H. apply not_L_eq_0 in H. contradiction.
    + inversion H; subst.
  destruct (L t) eqn:eqlt; try (inversion eqlt); subst.
    + inversion eqlt.
    +
  inversion H.

Lemma plus_elim : ∀ (ex1 ex2 : ka_term T) (side : T -> ka_term T) a, (side = L) \/ (side = R) -> side a ⋅ ex1 ≐ side a ⋅ ex2 -> ex1 ≐ ex2.
Proof.
  intros.
  destruct H as [H1 | H2]; subst.
  - remember (L a0) as l.
    induction ex1.
    + rewrite Dot_Z1 in H0. subst.
    inversion H0; subst; try reflexivity.
    +
   induction ex1.
    + inversion H0; subst; try reflexivity.
      *
   remember (L a0) as l.
    induction ex1.
    + subst. induction ex2; try reflexivity.
      * rewrite Dot_Z1 in H0. rewrite Dot_Id1 in H0. inversion H0; subst.
  induction H. inversion H0; subst; try reflexivity.
    +
  -
  induction ex1.
  - rewrite Dot_Z1 in H. inversion H.
    +
  inversion H.
  - reflexivity.
  -
  induction ex1.
  - inversion H; try reflexivity. *)

Definition string_to_ka_term side ls :=
  List.fold_left (* TODO: use fold_right*)
    (* (ka_term T) T *)
    (λ (t : ka_term T) (new : T), t⋅(side new))
    ls 1.

Print List.fold_left.
Print List.fold_right.

Definition step exp s s' := (string_to_ka_term L s) ⋅ (string_to_ka_term R s') ≤ exp.

Definition interp (n : nat) (P : list mm2_instr) :=
  match nth n P mm2_inc_a with
  | mm2_inc_a => R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M (S n))
  | mm2_inc_b => (lr a)✶ ⋅ R b ⋅ (lr b)✶  ⋅ R (Q_M (S n))
  | mm2_dec_a n' => (lr b)✶ ⋅ (R (Q_M n'))
                    + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  | mm2_dec_b n' => (lr a)✶ ⋅ (R (Q_M n'))
                    + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  end.

Definition pair_append (s1 s2 : list T * list T) :=
  match s1, s2 with
  | (s1l, s1r), (s2l, s2r) => (s1l ++ s2l, s1r ++ s2r)
  end.

Check ka_power.

(* Fixpoint lang_interp_power (term : ka_term T) (n : nat) {struct term} : (list T * list T) -> Prop :=
  match n with
  | 0%nat => λ s, s = ([], [])
  | S n' => λ s, ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp term s1 /\ lang_interp_power term n' s2
  end *)

Print ka_power.

Definition pair_length (s : list T * list T) :=
  match s with (l1, l2) => Nat.add (List.length l1) (List.length l2) end.

Definition ka_pred_empty (s : list T * list T) := s = ([], []).

Definition ka_pred_mul P Q s :=
  ∃ s1 s2, s = pair_append s1 s2 ∧ P s1 ∧ Q s2.

Definition ka_pred_power P n :=
  Nat.iter n (ka_pred_mul P) ka_pred_empty.

Definition ka_pred_star P s := ∃ n, ka_pred_power P n s.

Fixpoint lang_interp term s :=
  match term with
  | 0 => False
  | 1 => s = ([], [])
  | L e => s = ([e], [])
  | R e => s = ([], [e])
  | e1 + e2 => lang_interp e1 s \/ lang_interp e2 s
  | e1 ⋅ e2 => ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp e1 s1 /\ lang_interp e2 s2
  (* | e✶ => λ s, ∃ (n : nat), lang_interp_power e n s *)
  | e✶ => ka_pred_star (lang_interp e) s
  (* λ s, True *)
  (* λ s, ∃ n, ka_power_pred e n s *)
  (* λ s, ∃ n, lang_interp (ka_power e n) s *)
  (* s = ([], []) \/ ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp e s1 /\ lang_interp e(* ✶ *) s2 *)
  end.

(* Fixpoint ka_power_pred e n s {measure (pair_length s)}:=
  match n with
  | 0%nat => s = ([], [])
  | S n => ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp e s1 /\ ka_power_pred e n s2
  end

with lang_interp term s {measure (pair_length s)} :=
  match term with
  | 0 => False
  | 1 => s = ([], [])
  | L e => s = ([e], [])
  | R e => s = ([], [e])
  | e1 + e2 => lang_interp e1 s \/ lang_interp e2 s
  | e1 ⋅ e2 => ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp e1 s1 /\ lang_interp e2 s2
  (* | e✶ => λ s, ∃ (n : nat), lang_interp_power e n s *)
  | e✶ => ∃ n, ka_power_pred e n s
  (* λ s, True *)
  (* λ s, ∃ n, ka_power_pred e n s *)
  (* λ s, ∃ n, lang_interp (ka_power e n) s *)
  (* s = ([], []) \/ ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp e s1 /\ lang_interp e(* ✶ *) s2 *)
  end. *)

Check lang_interp.

(* Lemma l_i_plus : ∀ (x x' : ka_term T) s,
  lang_interp (x + x') s <->
    lang_interp x s \/ lang_interp x' s.
Proof.
  intros; unfold lang_interp; reflexivity.
Qed. *)

(* Lemma l_i_dot : ∀ (x x' : ka_term T) s,
  lang_interp (x ⋅ x') s <->
    ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp x s1 /\ lang_interp x' s2.
Proof.
  intros; unfold lang_interp; reflexivity.
Qed. *)

(* Lemma l_i_star : ∀ (x : ka_term T) s,
  lang_interp (x✶) s <-> s = ([], []) \/ ∃ s1 s2, s = pair_append s1 s2 /\ lang_interp x s1 /\ lang_interp x s2.
Proof.
  intros; unfold lang_interp; reflexivity.
Qed. *)

Lemma pair_append_id_r : ∀ s, pair_append s ([], []) = s.
Proof.
  intros. unfold pair_append.
  destruct s.
  repeat (rewrite List.app_nil_r).
  reflexivity.
Qed.

Lemma pair_append_id_l : ∀ s, pair_append ([], []) s = s.
Proof.
  intros. unfold pair_append.
  destruct s.
  repeat (rewrite List.app_nil_l).
  reflexivity.
Qed.

Lemma pair_append_assoc : ∀ s1 s2 s3, pair_append s1 (pair_append s2 s3) = pair_append (pair_append s1 s2) s3.
Proof.
  intros.
  destruct s1, s2, s3.
  simpl. repeat (rewrite List.app_assoc); reflexivity.
Qed.

Lemma l_i_dot_1_r : ∀ (x : ka_term T) s, lang_interp (x ⋅ 1) s <-> lang_interp x s.
Proof.
  split; intros.
  - simpl in H. destruct H as [s1 [s2 [H1 [H2 H3]]]].
    subst. rewrite pair_append_id_r. assumption.
  - simpl.
    exists s, ([], []); repeat split.
    + symmetry. apply pair_append_id_r.
    + assumption.
Qed.

Lemma l_i_dot_1_l : ∀ (x : ka_term T) s, lang_interp (1 ⋅ x) s <-> lang_interp x s.
Proof.
  split; intros.
  - simpl in H. destruct H as [s1 [s2 [H1 [H2 H3]]]].
    subst. rewrite pair_append_id_l. assumption.
  - simpl.
    exists ([], []), s; repeat split.
    + symmetry. apply pair_append_id_l.
    + assumption.
Qed.

(* Theorem term_lang_equiv : ∀ s t, string_to_ka_term L s ≤ t <-> lang_interp t (s, []).
Proof.
  split; intros.
  induction t.
  - compute in H.
  simpl. *)

Theorem l_i_equality : ∀ t1 t2, t1 ≐ t2 -> ∀ s, lang_interp t1 s <-> lang_interp t2 s.
Proof.
  intros.
  generalize dependent s.
  induction H.
  - reflexivity.
  - intros. symmetry. apply IHka_eq.
  - intros. rewrite IHka_eq1. apply IHka_eq2.
  - simpl; split; intros; destruct H1 as [H1 | H1].
    + rewrite IHka_eq1 in H1; left; assumption.
    + rewrite IHka_eq2 in H1; right; assumption.
    + rewrite <- IHka_eq1 in H1; left; assumption.
    + rewrite <- IHka_eq2 in H1; right; assumption.
  - simpl; split; intros;
    destruct H1 as [s1 [s2 [G1 [G2 G3]]]]; exists s1, s2;
    repeat split; try assumption.
    + rewrite IHka_eq1 in G2; assumption.
    + rewrite IHka_eq2 in G3; assumption.
    + rewrite <- IHka_eq1 in G2; assumption.
    + rewrite <- IHka_eq2 in G3; assumption.
  - simpl; split; intros;
    destruct H0 as [Hem | [s1 [s2 [H1 [H2 H3]]]]];
    try (left; assumption).
    + right; exists s1, s2; repeat split; try assumption.
      * rewrite IHka_eq in H2; assumption.
      * rewrite IHka_eq in H3; assumption.
    + right; exists s1, s2; repeat split; try assumption.
      * rewrite <- IHka_eq in H2; assumption.
      * rewrite <- IHka_eq in H3; assumption.
  - intros. unfold lang_interp in *.
    split; intros; destruct H as [s1 [s2 [H1 [H2 H3]]]];
    exists s2, s1; repeat split; try assumption; subst; reflexivity.
  - intros; rewrite l_i_dot_1_r; reflexivity.
  - intros; rewrite l_i_dot_1_l; reflexivity.
  - split; intros; simpl in *;
    [destruct H as [_ [_ [_ [_ H]]]]; assumption | contradiction].
  - split; intros; simpl in *;
    [destruct H as [_ [_ [_ [H _]]]]; assumption | contradiction].
  - split; intros; simpl in *.
    + destruct H as [s1 [s2 [Hs1s2 [HLI1 [s3 [s4 [Hs3s4 [HLI3 HLI4]]]]]]]].
      exists (pair_append s1 s3), s4; repeat split.
      * rewrite <- pair_append_assoc. rewrite <- Hs3s4; assumption.
      * exists s1, s3; repeat split; assumption.
      * assumption.
    + destruct H as [s1 [s2 [Hs1s2 [[s3 [s4 [Hs3s4 [HLI3 HLI4]]]] HLI2]]]].
      exists s3, (pair_append s4 s2); repeat split.
      * rewrite pair_append_assoc; rewrite <- Hs3s4; assumption.
      * assumption.
      * exists s4, s2; repeat split; assumption.
  - simpl; split; intros; [destruct H; [contradiction | assumption] | right; assumption].
  - simpl; intros; rewrite or_comm; reflexivity.
  - simpl; intros; rewrite or_assoc; reflexivity.
  - simpl; split; intros.
    + destruct H; assumption.
    + left; assumption.
  - simpl; split; intros.
    + destruct H as [s1 [s2 [HS1s2 [HLI1 [HLI2 | HLI3]]]]].
      * left;  exists s1, s2; repeat split; assumption.
      * right; exists s1, s2; repeat split; assumption.
    + destruct H as [[s1 [s2 [Hs1s2 [HLI1 HLI2]]]] | [s1 [s2 [Hs1s2 [HLI1 HLI2]]]]].
      * exists s1, s2; repeat split; try assumption; left; assumption.
      * exists s1, s2; repeat split; try assumption; right; assumption.
  - simpl; split; intros.
    + destruct H as [s1 [s2 [Hs1s2 [[HS1|HS1] HS2]]]].
      * left;  exists s1, s2; repeat split; assumption.
      * right; exists s1, s2; repeat split; assumption.
    + destruct H as [[s1 [s2 [Hs1s2 [HLI1 HLI2]]]] | [s1 [s2 [Hs1s2 [HLI1 HLI2]]]]].
      * exists s1, s2; repeat split; try assumption; left; assumption.
      * exists s1, s2; repeat split; try assumption; right; assumption.
  - simpl. split; intros.
    + destruct H.
      * left; assumption.
      * right; destruct H as [s1 [s2 [Hs1s2 [HLI1 HLI2]]]].
        exists s1, (pair_append s2 ([], [])); repeat split.
        -- rewrite pair_append_id_r; assumption.
        -- assumption.
        -- right.
        exists s1, s2; repeat split; try assumption.
        right. exists s2, ([], []); repeat split.
        -- symmetry; apply pair_append_id_r.
        -- assumption.
        --
   simpl; split; intros.
    + destruct H as [HS | [s1 [s2 [Hs1s2 [HLI1 HLI2]]]]].
      * left; assumption.
      * right. exists s1, s2. repeat split; try assumption.
       right; exists s1, s2; repeat split; try assumption.



  split; intros; simpl in *.
    + destruct H as [s1 [s2 [Hs1s2 [HLI1 [s3 [s4 [Hs3s4 [HLI3 HLI4]]]]]]]].
      exists s1, s2; repeat split.
      destruct H as [s1 [s2 [Hs1s2 [HLI1 [s3 [s4 [Hs3s4 [HLI3 HLI4]]]]]]]].


Fixpoint R_M' (P : list mm2_instr) (n : nat) := match P with
  | [] => 0
  | hd :: tl => (interp 1 P) ⋅ (L (Q_M n)) + R_M' tl (S n)
  end.

Definition R_M (P : list mm2_instr) := R_M' P 1.

Fixpoint C_M' (P : list mm2_instr) (n : nat) := match P with
  | [] => 0
  | _::tl => L (Q_M n) + C_M' tl (S n)
  end.

Definition C_M (P : list mm2_instr) := (L a)✶ ⋅ (L b)✶ ⋅ (C_M' P 1).

End Theory.
Local Open Scope ka_scope.

Check string_to_ka_term.
Theorem R_M__well_formed : ∀ P (s s' : list Σ_M), step Σ_M s s' (R_M P) -> (string_to_ka_term Σ_M L s ≤ C_M P).
Proof.
  intros. unfold step in H. unfold string_to_ka_term in *. unfold C_M. unfold ka_leq. compute.

Definition lang_interp {T} (term : ka_term T) :=
  match term with
  | L x => ([x], [])
  | R x => ([], [x])
  | K_Plus x y => ([], [])
  | _ => ([], [])
  end.
Check lang_interp.

Print mm2_instr.
Search mm2_atom.
Print mm2_step.
(* Definition mm2_instr__to__katerm instr := match
  instr with
  | mm2_inc_a => (R a) ⋅ (lr a)✶ ⋅ (lr b)✶
  | _ => R a
  end
. *)

Fixpoint to_term (f : T -> ka_term T) (s : list T) :=
  match s with
  | n :: rest => (f n)⋅(to_term f rest)
  | [] => 1
  end.

(* how to make T implicit here? it is added explicitly after End Theory. *)
Definition step_relation (s s' : list T) (e : ka_term T) :=
  (to_term L s) ⋅ (to_term R s') ≤ e.

Definition C_M n := (lr a)✶⋅(lr b)✶⋅(lr (Q_M n)).

(* Inductive T_M :=
  | cm n (H : C_M n) : T_M
  | c0 c_0 : T_M
  | c1 c_1 : T_M
. *)

Definition R_M n1 n2 :=
  (*Inc(1, q)*)   R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M n1) ⋅ L (Q_M n1) +
  (*Inc(2, q)*)   (lr a)✶ ⋅ R b ⋅ (lr b)✶ ⋅ R (Q_M n1) ⋅ L (Q_M n1)+
  (*If(1,q1,q2)*) (lr b)✶ ⋅ R (Q_M n1) + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M n2) +
  (*If(2,q1,q2)*) (lr a)✶ ⋅ R (Q_M n1) + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ R (Q_M n2) +
  (*Halt(0)*)     R c_0 +
  (*Halt(1)*)     R c_1
  .

Print R_M.

Fixpoint power_list {T} (x:T) n :=
  match n with
  | 0%nat => []
  | S n => x :: (power_list x n)
  end.

Definition c_m_form_list n m i := power_list a n ++ (power_list b m) ++ [Q_M i].

(* Definition R_M := *)

(* Lemma step_form : ∀ s s' *)

End Theory.
Local Open Scope ka_scope.
Print step_relation.

Locate "lr".
Lemma step_form : ∀ s s' n1 n2,
  step_relation Σ_M s s' (R_M n1 n2)
    -> ∃ n m i, s = c_m_form_list n m i /\ (to_term Σ_M lr_term s) ≤ C_M i.
Proof.
  intros.
  unfold step_relation in H.
  unfold R_M in H.
  unfold C_M.
  unfold c_m_form_list.
  (* exists n1; exists n2; exists n2. *)
Admitted.

Example ex_to_term : step_relation Σ_M [a; b; c_1] [a; b; c_1]
  ((lr a)⋅(lr b)⋅(lr c_1)).
Proof.



Section Canonicalization.

Fixpoint freeQ_L (e : ka_term T) :=
  match e with
  | L _ => false
  | x + y => (freeQ_L x) && (freeQ_L y)
  | x ⋅ y => (freeQ_L x) && (freeQ_L y)
  | _ => true
  end.

Fixpoint freeQ_Plus (e : ka_term T) :=
  match e with
  | _ + _ => false
  | x ⋅ y => (freeQ_Plus x) && freeQ_Plus y
  | _ => true
  end.

Fixpoint collect_L_R (e : ka_term T) (accL accR : list (ka_term T)) :=
  match e with
  | x ⋅ y =>
    (match collect_L_R x accL accR with
    | (accL, accR) =>
      collect_L_R y accL accR
    end)
  | L x => ((L x)::accL, accR)
  | R x => (accL, (R x)::accR)
  | 0 => (0::accL, [])
  | _ => (accL, accR)
  end.

Fixpoint compose acc term :=
  match acc with
  | [] => term
  | K_Zero::rest => K_Zero
  | x::rest => (compose rest (@K_Dot T x term))
  end.

Definition compose_L_R accL_accR :=
  match accL_accR with
  (* | ([], _) => 0
  | (_, []) => 0 *)
  | (accL, accR) => (compose accL 1) ⋅ (compose accR 1)
  end.

Fixpoint remove_1 e :=
  match e with
  | 1 ⋅ e => remove_1 e
  | e ⋅ 1 => remove_1 e
  | x ⋅ y => (remove_1 x) ⋅ remove_1 y
  | x + y => (remove_1 x) + remove_1 y
  | s => s
  end.

(* is this worth it?? *)
Fixpoint left_assoc e :=
  match e with
  | x ⋅ (y ⋅ z) => (left_assoc x) ⋅ (left_assoc y) ⋅ (left_assoc z)
  (* | x + (y + z) => (left_assoc x) + (left_assoc y) + (left_assoc z) *)
  | t => t
  end.

(* Theorem left_assoc_equiv e : left_assoc e ≐ e.
Proof.
  induction e; try (reflexivity).
  - assert (H : left_assoc (e1 + e2) ≐ (left_assoc e1) + left_assoc e2).
    { simpl. inversion IHe2; subst. compute. }
  rewrite <- IHe1. generalize dependent IHe2.
    induction e2; try reflexivity.
    intros. rewrite <- IHe2.
    simpl.
    compute. *)

(* Definition canonicalize e := left_assoc (remove_1 (compose_L_R (collect_L_R e [] []))).

Theorem canonicalize_equiv e : canonicalize e ≐ e.
Proof.
  induction e; try (compute; reflexivity).
  - unfold canonicalize.
    assert
    unfold collect_L_R.
  assert (H : canonicalize (e1 + e2) ≐ (canonicalize e1) + (canonicalize e2)).
    { rewrite IHe1. rewrite IHe2. compute. }
  unfold canonicalize.
    unfold collect_L_R. *)

End Canonicalization.

Local Open Scope ka_scope.

Example check_canonicalize : canonicalize Σ_M (R a ⋅ L a ⋅ R b ⋅ L b) ≐ L a ⋅ L b ⋅ R a ⋅ R b.
Proof.
  (* simpl. why does simpl not do anything here? compute does more *)
  compute. reflexivity.
Qed.

Theorem canonicalize_equiv :

(* Fixpoint to_L__R (e : ka_term T) :=
  match e with
  | x + y =>
  end.
  match e with
  | (R y) ⋅ (L x) => (L x) ⋅ (R y)
  | (u⋅R y) ⋅ L x => (to_L__R u)⋅L x⋅ R y
  | (u⋅R y) ⋅ ((L x) ⋅ w) => (to_L__R u)⋅L x⋅ R y⋅(to_L__R w)
  | (R y) ⋅ ((L x) ⋅ w) => (L x) ⋅ R y ⋅(to_L__R (w))
  | x + y => (to_L__R x) + (to_L__R y)
  | x ⋅ y => (to_L__R x) ⋅ (to_L__R y)
  | s => s
  end. *)

(* Example to_L__R_ex1 : ∀ x y, to_L__R ((lr x)⋅(lr y)) ≐ (L x)⋅(L y)⋅(R x)⋅(R y).
Proof.
  intros.
  (* unfold lr_term. *)
  reflexivity.
Qed.

Example to_L__R_ex2 : ∀ x y z, to_L__R ((lr x)⋅(lr y)⋅(lr z)) ≐ L x⋅L y⋅L z⋅R x⋅R y⋅R z.
Proof.
  intros.
  simpl. *)



Lemma plus_interleave : ∀ (x y z w : ka_term T), x + y + z + w ≐ x + z + y + w.
Proof.
  intros.
  rewrite <- Plus_Assoc.
  rewrite <- Plus_Assoc.
  assert (G : y + (z + w) ≐ (z + w) + y). { apply Plus_Com. }
  rewrite G.
  assert (H : y + w ≐ w + y). { apply Plus_Com. }
  rewrite <- Plus_Assoc.
  rewrite <- H.
  rewrite Plus_Assoc.
  rewrite Plus_Assoc.
  reflexivity.
Qed.

Lemma extra_one_ignore : forall (x : ka_term T), 1 + 1 + x ≐ 1 + x.
Proof.
  intros.
  rewrite Plus_Idemp.
  reflexivity.
Qed.

Print step_relation.
Locate "lr".




Lemma x_xstar__xtar_x : forall (t : ka_term T), t⋅t✶ ≐ t✶⋅t.
Proof.
  intros.
  induction t.
  - rewrite Dot_Z2. rewrite Dot_Z1. reflexivity.
  - rewrite Dot_Id2. rewrite Dot_Id1. reflexivity.
  - admit.
  - admit.
  - rewrite Dist_R. rewrite Dist_L.
Admitted. (* should follow from t⋅t✶ ≐ t✶ ≐ t✶⋅t *)


Lemma x_x_star : forall (t : ka_term T), t✶ ≐ t✶⋅t.
Proof.
  intros.
  assert (H : t✶ ≤ t✶⋅t).
  {admit. }
  assert (G : t✶⋅t ≤ t✶).
  {admit. }
  apply (leq_antisym _ _ H G).
Admitted.
  (* unfold ka_leq.
  rewrite Plus_Com.
  rewrite star_expand.
  rewrite Dist_R.
  rewrite Dot_Id2.
  rewrite Plus_Assoc.
  rewrite Plus_Assoc.
  rewrite Dist_L.
  rewrite Dot_Id1.
  rewrite Dot_Assoc.
  rewrite <- star_expand.
  assert (H : t ≐ t⋅1).
  { symmetry. apply Dot_Id1. }
  rewrite <- Dot_Assoc.
  rewrite H.
  rewrite <- Dot_Assoc.
  rewrite <- Dist_L.
  rewrite <- H.
  rewrite Dot_Id2.
  rewrite <- star_expand.
  Check star_leq.

  replace (t✶) with (1 + t⋅t✶).
  apply Star. *)


Inductive step_relation :=
  |

(* Inductive disjoint_union {T} : Type :=
  | l (t : T)
  | r (t : T).

(* Coercion K_Var : Σ_M >-> ka_term. QUEST: how to make this work? *)

Inductive commute_on_disjoint_union {T} : disjoint_union -> disjoint_union -> Prop :=
  | commute_refl : Reflexive (@commute_on_disjoint_union T)
  | commute_sym : Symmetric (@commute_on_disjoint_union T)
  | lr_com (s s' : T) : commute_on_disjoint_union (l s) (r s').

Print ka_term.

Check term_to_disjoint_term ([[a]]⋅[[b]]⋅[[Q_M 1]]). *)
(* Example ex_1 :
  term_to_disjoint_term ([[a]]⋅[[b]]⋅[[Q_M 1]])
  ≐ [[l a]]⋅[[r a]]⋅[[l b]]⋅[[r b]]⋅[[l (Q_M 1)]]⋅[[r (Q_M 1)]].
  Proof. simpl. Unset Printing Notations. *)


(* Print mm2_instr.
(* Unset Printing Notations. *)
Print mm2_atom.
Locate "//".

Print mm2_stop. *)

Definition interpret_mm2_instr (pc1 pc2 : nat) (i : mm2_instr) :=
  match i with
  | mm2_inc_a => (lr a)⋅((lr a)✶)⋅((lr b)✶)⋅(R (Q_M pc1))
  | mm2_inc_b => ((lr a)✶)⋅(R b)⋅((lr b)✶)⋅(R (Q_M pc1))
  | mm2_dec_a n => ((lr b)✶)⋅(R (Q_M pc1)) + (L a)⋅((lr a)✶)⋅((lr b)✶)⋅(R (Q_M pc2))
  | mm2_dec_b n => ((lr a)✶)⋅(R (Q_M pc1)) + ((lr a)✶)⋅(L b)⋅((lr b)✶)⋅(R (Q_M pc2))
  end.

Check interpret_mm2_instr.

Print mm2_atom.

(* Definition interpret_mm2 (i : mm2_atom) :=
  match i with
    | _ => 1
  end.
Check interpret_mm2. *)

(* ------- testing out some lemmas on the ka_eq and ka_term types ------- *)

Local Open Scope ka_scope.

Global Instance KatCC_Eq_equiv : ∀ T, Equivalence (@ka_eq T).
Proof.
  split; constructor; try assumption.
  apply Ka_sym, Ka_trans with y; auto.
Qed.

Lemma ka_power_decomp : forall T (kat : ka_term T) n m,
  ka_power kat (n + m) ≐ K_Dot (ka_power kat n) (ka_power kat m).
Proof.
  intros.
  induction n.
  - simpl. rewrite Dot_Id2. reflexivity.
  - simpl. rewrite IHn. rewrite Dot_Assoc. reflexivity.
Qed.

Lemma test : forall T (t : ka_term T), t + 0 ≐ t.
Proof.
intros. rewrite Plus_Com. by constructor. Qed.

Lemma plus_assoc_swap1 : ∀ T (x y z : ka_term T),
  x + (y + z) ≐ x + (z + y).
Proof.
  intros. assert (H: y+z ≐ z + y).
  - apply Plus_Com.
  - rewrite H. reflexivity.
Qed.

Lemma plus_assoc_swap2 : ∀ T (x y z : ka_term T),
  x + (y + z) ≐ (x + z) + y.
Proof.
  intros. assert (H: y+z≐z+y).
  - apply Plus_Com.
  - rewrite H. apply Plus_Assoc.
Qed.

(* QUEST: why does this struggle with typing? *)
Lemma test_1 : forall (T:Type) (x y z : ka_term T), x ≤ y -> (x + z ≐ (x + y) + z).
Proof.
  intros. unfold ka_leq in H. rewrite Plus_Com in H. rewrite H. reflexivity.
Qed.

Lemma leq_antisym : forall (T : Type) (x y : ka_term T), x ≤ y -> y ≤ x -> x ≐ y.
Proof.
  intros.
  unfold ka_leq in H, H0.
  rewrite <- H. rewrite Plus_Com. assumption.
Qed.

Global Instance leq_trans : ∀ T, Transitive (@ka_eq T).
Proof.
  unfold Transitive. intros.
  apply Ka_trans with y; assumption.
Qed.

(* QUEST: in Arthur's setup, he has TEStar1, TEStarL, TEStarR.
In the present setup, I'm not sure how to translate or derive these... *)
Lemma one_star : ∀ (T : Type) (x : ka_term T), (1 ≤ x✶).
Proof.
intros. compute. rewrite (Ka_Star x). Abort. (* HELP! -- can't be helped *)


(* ------- Testing Example 1 ------- *)
(* QUEST: How to do this? -- don't, its very hard *)
(* Inductive N_Top_Bot : Type :=
  | Top
  | Bot
  | X (n : nat)
.

Theorem n_top_bot_ka : @ka_eq N_Top_Bot. *)
