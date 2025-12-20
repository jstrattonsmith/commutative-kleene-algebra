Require Import Coq.Classes.Morphisms.
Require Import Coq.Unicode.Utf8.
Require Import ssreflect.
Require Import Coq.Setoids.Setoid.
Require Import Undecidability.MinskyMachines.MM2.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
(* From Coq Require Import Lia. *)

From Coq Require Import List. Import ListNotations.
From Coq Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Require Import List Relations.Relation_Operators. *)

(* Print mm2_instr_at.
#[local] Set Implicit Arguments.
Check clos_refl_trans.
Check (clos_refl_trans _ (mm2_step _)). *)

(* ------- ------- *)
(* ------- Commuting Relations ------- *)
(* ------- ------- *)

(* Definition commuting_relation X (R : Relation_Definitions.relation X) :=
  Reflexive R /\ Symmetric R.

Definition commute X R (H : commuting_relation R) (x y : X) := R x y.

Definition commutable X R := commuting_relation X R.

Definition discrete X R (H : commuting_relation X R) (x y : X) :=
  R x y <-> x = y. (* QUEST: what kind of equality is meant here? *)

Definition commutative X R (H : commuting_relation X R) :=
  ∀ (x y : X), commute X R H x y. *)

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
Delimit Scope ka_scope with ka.
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

Reserved Notation "e1 ≡ e2" (at level 80, no associativity).

Inductive ka_eq {T : Type} : ka_term T -> ka_term T -> Prop :=
  | Ka_refl : Reflexive (@ka_eq T)
  | Ka_sym : Symmetric (@ka_eq T)
  | Ka_trans : Transitive (@ka_eq T)

  | Ka_Plus : Proper ((@ka_eq T) ==> (@ka_eq T) ==> (@ka_eq T)) K_Plus
  | Ka_Dot : Proper ((@ka_eq T) ==> (@ka_eq T) ==> (@ka_eq T)) K_Dot
  | Ka_Star : Proper ((@ka_eq T) ==> (@ka_eq T)) K_Star

  (* including the following to allow for commuting terms *)
  | LR_Com x y : (L x)⋅(R y) ≡ (R y)⋅(L x)

  | Dot_Id1 t : t ⋅ 1 ≡ t
  | Dot_Id2 t : 1 ⋅ t ≡ t
  | Dot_Z1  t : t ⋅ 0 ≡ 0
  | Dot_Z2  t : 0 ⋅ t ≡ 0
  | Dot_Assoc x y z : x ⋅ (y ⋅ z) ≡ (x ⋅ y) ⋅ z

  | Plus_Id t : 0 + t ≡ t
  | Plus_Com (x y : ka_term T) : x + y ≡ y + x
  | Plus_Assoc x y z : x + (y + z) ≡ (x + y) + z
  | Plus_Idemp x : x + x ≡ x

  | Dist_L x y z : x ⋅ (y + z) ≡ x⋅y + x⋅z
  | Dist_R x y z : (x + y) ⋅ z ≡ x⋅z + y⋅z

  | Star t : t✶ ≡ 1 + (t ⋅ (t✶))
  where "e1 ≡ e2" := (ka_eq e1 e2).

Notation "x ≢ y" := (not (ka_eq x y)) (at level 80, no associativity).

Global Existing Instance Ka_refl.
Global Existing Instance Ka_sym.
Global Existing Instance Ka_trans.
Global Existing Instance Ka_Plus.
Global Existing Instance Ka_Dot.
Global Existing Instance Ka_Star.

Add Parametric Relation T : (ka_term T) ka_eq as ka_eq.

Lemma Ka_refl' {T} (t : ka_term T) : t ≡ t.
Proof. reflexivity. Qed.

Global Hint Resolve Ka_refl' : core.

Lemma Plus_Id' : ∀ T (t : ka_term T), t + 0 ≡ t.
Proof.
  intros T t.
  rewrite Plus_Com; rewrite Plus_Id.
  reflexivity.
Qed.

Lemma ka_neq_sym : ∀ T (x y : ka_term T), x ≢ y <-> y ≢ x.
Proof.
  intros T x y; split; intros H G; symmetry in G; apply H in G; assumption.
Qed.

(* QUEST: How to declare this to work with symmetry tactic? *)
Hint Resolve ka_neq_sym : core.
(* Global Existing Instance ka_neq_sym. *)

Definition ka_leq {T} (x y : ka_term T) : Prop := ((y + x) ≡ y)%ka.
Notation "x ≤ y" := (ka_leq x y) : ka_scope.


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

Lemma leq_trans : ∀ (t1 t2 t3 : ka_term T), t1 ≤ t2 -> t2 ≤ t3 -> t1 ≤ t3.
Proof.
  intros.
  unfold ka_leq in *.
  rewrite - H0.
  rewrite - H.
  rewrite Plus_Assoc.
  rewrite - Plus_Assoc.
  rewrite Plus_Idemp.
  reflexivity.
Qed.

Global Instance leq_proper :
  Proper (ka_eq ==> ka_eq ==> iff) (@ka_leq T).
Proof.
  rewrite /ka_leq => e1 e2 e12 e3 e4 e34.
  split.
  - intros. rewrite - e34. rewrite - e12. assumption.
  - intros. rewrite e12. rewrite e34. assumption.
Qed.

Lemma star_expand : forall (t : ka_term T), t✶ ≡ 1 + t⋅t✶.
Proof. intros. apply Star. Qed.

Lemma star_leq : forall (t : ka_term T), 1 + t⋅t✶ ≤ t✶.
Proof.
  intros.
  rewrite - star_expand.
  apply leq_reflex.
Qed.

Lemma leq_antisym : forall (x y : ka_term T), x ≤ y -> y ≤ x -> x ≡ y.
Proof.
  intros.
  unfold ka_leq in H, H0.
  rewrite - H. rewrite Plus_Com. symmetry. assumption.
Qed.

Definition build_term (side : T -> ka_term T) := fold_right (λ (n : T) t, side n ⋅ t).

Definition string_to_ka_term ls :=
  match ls with (l1, l2) =>
    (build_term L 1 l1)⋅(build_term R 1 l2)
  end.

Definition interp (n : nat) (P : list mm2_instr) :=
  match nth n P mm2_inc_a with
  | mm2_inc_a => R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M (S n))
  | mm2_inc_b => (lr a)✶ ⋅ R b ⋅ (lr b)✶  ⋅ R (Q_M (S n))
  | mm2_dec_a n' => (lr b)✶ ⋅ (R (Q_M n'))
                    + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  | mm2_dec_b n' => (lr a)✶ ⋅ (R (Q_M n'))
                    + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  end.

Definition interp_single (n : nat) (instr : mm2_instr) :=
  match instr with
  | mm2_inc_a =>    R a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ R (Q_M (S n))
  | mm2_inc_b =>    (lr a)✶ ⋅ R b ⋅ (lr b)✶  ⋅ R (Q_M (S n))
  | mm2_dec_a n' => (lr b)✶ ⋅ (R (Q_M n'))
                    + L a ⋅ (lr a)✶ ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  | mm2_dec_b n' => (lr a)✶ ⋅ (R (Q_M n'))
                    + (lr a)✶ ⋅ L b ⋅ (lr b)✶ ⋅ (R (Q_M (S n)))
  end.

Definition pair_append (s1 s2 : list T * list T) :=
  match s1, s2 with
  | (s1l, s1r), (s2l, s2r) => (s1l ++ s2l, s1r ++ s2r)
  end.

Lemma pair_append_eq_nil : ∀ s s',
  pair_append s s' = ([], []) -> s = ([], []) ∧ s' = ([], []).
Proof.
  intros.
  destruct s, s'.
  simpl in H; injection H;
  intros G K; clear H.
  apply app_eq_nil in G as [G1 G2], K as [K1 K2];
  subst;
  auto.
Qed.

(* used *)
Lemma pair_append_id_r : ∀ s, pair_append s ([], []) = s.
Proof.
  intros. unfold pair_append.
  destruct s.
  repeat (rewrite List.app_nil_r).
  reflexivity.
Qed.

(* used *)
Lemma pair_append_id_l : ∀ s, pair_append ([], []) s = s.
Proof.
  intros. unfold pair_append.
  destruct s.
  repeat (rewrite List.app_nil_l).
  reflexivity.
Qed.

(* used *)
Lemma pair_append_assoc : ∀ s1 s2 s3,
  pair_append s1 (pair_append s2 s3) = pair_append (pair_append s1 s2) s3.
Proof.
  intros.
  destruct s1, s2, s3.
  simpl. repeat (rewrite List.app_assoc); reflexivity.
Qed.

Definition ka_pred_zero (s : list T * list T) := False.

Definition ka_pred_unit (s : list T * list T) := s = ([], []).

Definition ka_pred_left (e : T) (s : list T * list T) := s = ([e], []).

Definition ka_pred_right (e : T) (s : list T * list T) := s = ([], [e]).

Definition ka_pred_add P Q (s : list T * list T) : Prop :=
  P s ∨ Q s.

Definition ka_pred_mul P Q s :=
  ∃ s1 s2, s = pair_append s1 s2 ∧ P s1 ∧ Q s2.

Definition ka_pred_power P n :=
  Nat.iter n (ka_pred_mul P) ka_pred_unit.

Definition ka_pred_star P s := ∃ n, ka_pred_power P n s.

Fixpoint lang_interp term :=
  match term with
  | 0 => ka_pred_zero
  | 1 => ka_pred_unit
  | L e => ka_pred_left e
  | R e => ka_pred_right e
  | e1 + e2 => ka_pred_add (lang_interp e1) (lang_interp e2)
  | e1 ⋅ e2 => ka_pred_mul (lang_interp e1) (lang_interp e2)
  | e✶ => ka_pred_star (lang_interp e)
  end.

(* used *)
Lemma l_i_dot_1_r : ∀ (x : ka_term T) s, lang_interp (x ⋅ 1) s <-> lang_interp x s.
Proof.
  split; intros; simpl in *.
  - destruct H as [s1 [s2 [H1 [H2 H3]]]];
    unfold ka_pred_unit in H3; subst;
    rewrite pair_append_id_r; assumption.
  - simpl; exists s, ([], []); repeat split;
    [symmetry; apply pair_append_id_r | assumption].
Qed.

(* used *)
Lemma l_i_dot_1_l : ∀ (x : ka_term T) s, lang_interp (1 ⋅ x) s <-> lang_interp x s.
Proof.
  split; intros; simpl in *.
  - destruct H as [s1 [s2 [H1 [H2 H3]]]];
    unfold ka_pred_unit in H2; subst;
    rewrite pair_append_id_l; assumption.
  - exists ([], []), s; repeat split;
    [symmetry; apply pair_append_id_l | assumption].
Qed.

(* QUEST: do we need bidirectionality here? I don't think this holds...but wanted to check *)
Theorem l_i_equality : ∀ t1 t2, t1 ≡ t2 -> ∀ s, lang_interp t1 s <-> lang_interp t2 s.
Proof.
  intros t1 t2 H.
  induction H.
  - reflexivity.
  - intros. symmetry. apply IHka_eq.
  - intros. rewrite IHka_eq1. apply IHka_eq2.
  - simpl; split; intros; destruct H1 as [H1 | H1].
    + rewrite IHka_eq1 in H1; left; assumption.
    + rewrite IHka_eq2 in H1; right; assumption.
    + rewrite - IHka_eq1 in H1; left; assumption.
    + rewrite - IHka_eq2 in H1; right; assumption.
  - simpl; split; intros;
    destruct H1 as [s1 [s2 [G1 [G2 G3]]]]; exists s1, s2;
    repeat split; try assumption.
    + rewrite IHka_eq1 in G2; assumption.
    + rewrite IHka_eq2 in G3; assumption.
    + rewrite - IHka_eq1 in G2; assumption.
    + rewrite - IHka_eq2 in G3; assumption.
  - simpl; split; intros G;
    unfold ka_pred_star, ka_pred_power, ka_pred_unit, ka_pred_mul in *;
    destruct G as [n G];
    exists n; generalize dependent s; induction n;
    simpl in *; intros; try assumption;
    destruct G as [s1 [s2 [Hs1s2 [HLI1 Hiter]]]];
    exists s1, s2; repeat split; try assumption;
    try (apply IHn; assumption);
    [rewrite - IHka_eq; assumption | rewrite IHka_eq; assumption].
  - intros; unfold lang_interp, ka_pred_mul, ka_pred_left, ka_pred_right in *;
    split; intros; destruct H as [s1 [s2 [H1 [H2 H3]]]];
    exists s2, s1; repeat split; try assumption; subst; reflexivity.
  - intros; rewrite l_i_dot_1_r; reflexivity.
  - intros; rewrite l_i_dot_1_l; reflexivity.
  - split; intros; simpl in *;
    unfold ka_pred_mul, ka_pred_zero in *;
    [destruct H as [_ [_ [_ [_ H]]]]; assumption | contradiction].
  - split; intros; simpl in *;
    unfold ka_pred_mul, ka_pred_zero in *;
    [destruct H as [_ [_ [_ [H _]]]]; assumption | contradiction].
  - split; intros; simpl in *;
    unfold ka_pred_mul in *.
    + destruct H as [s1 [s2 [Hs1s2 [HLI1 [s3 [s4 [Hs3s4 [HLI3 HLI4]]]]]]]].
      exists (pair_append s1 s3), s4; repeat split; try assumption.
      * rewrite - pair_append_assoc. rewrite - Hs3s4; assumption.
      * exists s1, s3; repeat split; assumption.
    + destruct H as [s1 [s2 [Hs1s2 [[s3 [s4 [Hs3s4 [HLI3 HLI4]]]] HLI2]]]].
      exists s3, (pair_append s4 s2); repeat split; try assumption.
      * rewrite pair_append_assoc; rewrite - Hs3s4; assumption.
      * exists s4, s2; repeat split; assumption.
  - simpl; split; intros; [destruct H; [contradiction | assumption] | right; assumption].
  - simpl; intros; unfold ka_pred_add in *; rewrite or_comm; reflexivity.
  - simpl; intros; unfold ka_pred_add in *; rewrite or_assoc; reflexivity.
  - simpl; split; intros; unfold ka_pred_add in *;
    [destruct H; assumption | left; assumption].
  - simpl; split; intros; unfold ka_pred_add, ka_pred_mul in *.
    + destruct H as [s1 [s2 [HS1s2 [HLI1 [HLI2 | HLI3]]]]];
      [left | right]; exists s1, s2; repeat split; assumption.
    + destruct H as [[s1 [s2 [Hs1s2 [HLI1 HLI2]]]] | [s1 [s2 [Hs1s2 [HLI1 HLI2]]]]];
      exists s1, s2; repeat split; try assumption; [left | right]; assumption.
  - simpl; split; intros; unfold ka_pred_add, ka_pred_mul in *.
    + destruct H as [s1 [s2 [Hs1s2 [[HS1|HS1] HS2]]]];
      [left | right]; exists s1, s2; repeat split; assumption.
    + destruct H as [[s1 [s2 [Hs1s2 [HLI1 HLI2]]]] | [s1 [s2 [Hs1s2 [HLI1 HLI2]]]]];
      exists s1, s2; repeat split; try assumption; [left | right]; assumption.
  - simpl; split; intros; unfold ka_pred_star in *.
    + destruct H as [n H].
      unfold ka_pred_add, ka_pred_power in *.
      destruct n; simpl in H.
      * left; assumption.
      * unfold ka_pred_mul in H;
        destruct H as [s1 [s2 [Hs1s2 [HS1 Hpow]]]];
        unfold ka_pred_add, ka_pred_mul, ka_pred_star; right;
        exists s1, s2; repeat split; try assumption;
        exists n; assumption.
    + unfold ka_pred_add in H; destruct H as [H | H].
      * exists 0%nat; simpl; assumption.
      * unfold ka_pred_power, ka_pred_mul in *;
        destruct H as [s1 [s2 [Hs1s2 [HLI1 [n HPow]]]]];
        subst; exists (S n); simpl;
        exists s1, s2; repeat split; assumption.
Qed.

Global Instance lang_interp_proper : Proper (ka_eq ==> eq ==> iff) lang_interp.
Proof.
  intros t1 t2 et1t2 s1 s2 es1s2.
  rewrite es1s2.
  apply l_i_equality.
  assumption.
Qed.

(* used *)
Lemma leq_leq_dot : ∀ (x1 x2 y1 y2 : ka_term T), x1 ≤ y1 -> x2 ≤ y2 -> x1⋅x2 ≤ y1⋅y2.
Proof.
  intros x1 x2 y1 y2 H G.
  unfold ka_leq in H, G.
  unfold ka_leq.
  rewrite - H; rewrite - G.
  rewrite Dist_L; repeat (rewrite Dist_R).
  rewrite Plus_Assoc; rewrite - Plus_Assoc.
  rewrite Plus_Idemp.
  reflexivity.
Qed.

(* used *)
Lemma leq_plus : ∀ (x1 x2 : ka_term T), x1 ≤ x1 + x2.
Proof.
  intros.
  unfold ka_leq.
  rewrite Plus_Com;
  rewrite Plus_Assoc;
  rewrite Plus_Idemp.
  reflexivity.
Qed.

(* used *)
Lemma one_leq_star : ∀ (t : ka_term T), 1 ≤ t ✶.
Proof.
  intros.
  rewrite Star.
  apply leq_plus.
Qed.

(* used *)
Lemma li_term_to_string_true : ∀ s, lang_interp (string_to_ka_term s) s.
Proof.
  intros.
  destruct s as (sl, sr).
  simpl.
  exists (sl, []), ([], sr).
  repeat split.
  - simpl. rewrite app_nil_r; reflexivity.
  - induction sl as [| e1 sl' IHsl'].
    + reflexivity.
    + simpl. unfold ka_pred_mul.
      exists ([e1], []), (sl', []).
      repeat split. assumption.
  - induction sr as [| e1 sr' IHsr'].
    + reflexivity.
    + simpl. unfold ka_pred_mul.
      exists ([], [e1]), ([], sr').
      repeat split. assumption.
Qed.

(* unused *)
Lemma build_term__pull_out_base : ∀ s (side : T -> ka_term T) (t : ka_term T),
  side = R ∨ side = L -> build_term side t s
    ≡ (build_term side 1 s) ⋅ t.
Proof.
  intros. destruct H as [H | H];
  generalize dependent t;
  try (induction s; intros; simpl; [
    rewrite Dot_Id2; reflexivity
  | rewrite IHs; rewrite Dot_Assoc; reflexivity
  ]).
Qed.

(* used *)
Lemma build_term__commutes : ∀ s t side1 side2,
  (side1 = L ∧ side2 = R) ∨ (side1 = R ∧ side2 = L) ->
  (build_term side1 1 s) ⋅ side2 t
    ≡ side2 t ⋅ (build_term side1 1 s).
Proof.
  intros.
  destruct H as [H | H]; destruct H as [H1 H2]; subst;
  try (induction s as [|c s IHs]; simpl; [
      rewrite Dot_Id2; rewrite Dot_Id1; reflexivity
    | rewrite - Dot_Assoc; rewrite IHs;
      repeat (rewrite Dot_Assoc); rewrite LR_Com; reflexivity
  ]).
Qed.

(* used *)
Lemma string_to_term__pair_append__commute : ∀ s s',
  string_to_ka_term (pair_append s s') ≡ (string_to_ka_term s) ⋅ (string_to_ka_term s').
Proof.
  intros.
  destruct s as (s1, s1'), s' as (s2, s2').
  induction s1 as [|c1 s1 IHs1].
  - induction s1' as [|c1' s1' IHs1'].
    + simpl. repeat (rewrite Dot_Id2); reflexivity.
    + simpl in *.
      rewrite Dot_Assoc.
      rewrite build_term__commutes; try (left; auto).
      rewrite - Dot_Assoc.
      rewrite IHs1'.
      repeat (rewrite Dot_Id2).
      repeat (rewrite Dot_Assoc).
      reflexivity.
  - simpl in *.
    rewrite - Dot_Assoc.
    rewrite IHs1.
    repeat (rewrite Dot_Assoc).
    reflexivity.
Qed.

(* unused *)
Lemma destruct_power : ∀ t n s,
  ka_pred_power (lang_interp t) n s ->
    ∃ (ls : list (list T * list T)),
      s = fold_right pair_append ([], []) ls
        ∧ fold_right and True (List.map (lang_interp t) ls).
Proof.
  intros.
  generalize dependent s.
  induction n as [|n IHn].
  - intros. simpl in H. unfold ka_pred_unit in H.
    subst.
    exists [].
    simpl. repeat split.
  - intros. simpl in H; unfold ka_pred_mul in H.
    destruct H as [s1 [s2 [Hs1s2 [HLI1 Hpow]]]].
    apply IHn in Hpow as [ls [Hs2 Hls]].
    exists (s1::ls).
    repeat split; try assumption.
    simpl. rewrite - Hs2. assumption.
Qed.

(* used, but unused *)
Lemma term_leq_term_star : ∀ (t : ka_term T), t ≤ t✶.
Proof.
  intros.
  (* rewrite {2} Star. *)
  rewrite Star.
  rewrite Star.
  rewrite Dist_L.
  rewrite Dot_Id1.
  rewrite Plus_Com.
  rewrite - Plus_Assoc.
  apply leq_plus.
Qed.

(* unused *)
Lemma leq_term__leq_term_star : ∀ (t t': ka_term T), t ≤ t' -> t ≤ t'✶.
Proof.
  intros.
  apply leq_trans with (t2:=t'); [assumption | apply term_leq_term_star].
Qed.

Lemma leq1__leq2__leq1_dot_2 : ∀ (t1 t2 t3 t4 : ka_term T),
  t1 ≤ t3 -> t2 ≤ t4 -> t1⋅t2 ≤ t3⋅t4.
Proof.
  intros t1 t2 t3 t4 H1 H2.
  unfold ka_leq in H1, H2.
  rewrite - H1.
  rewrite - H2.
  rewrite Dist_R; repeat (rewrite Dist_L).
  repeat (rewrite Plus_Assoc).
  rewrite Plus_Com.
  apply leq_plus.
Qed.

(* unused *)
Lemma t__leq__t_star : ∀ (t : ka_term T), t ≤ t✶.
Proof.
  intros.
  unfold ka_leq.
  rewrite Star.
  rewrite Star.
  rewrite Dist_L.
  rewrite Dot_Id1.
  rewrite - Plus_Assoc.
  assert (H : t + t ⋅ (t ⋅ t ✶) + t ≡ t + t ⋅ (t ⋅ t ✶) ).
  { rewrite Plus_Com. rewrite Plus_Assoc.
    rewrite Plus_Idemp. reflexivity. }
  rewrite H.
  rewrite Plus_Assoc.
  reflexivity.
Qed.

(* used *)
Lemma t_tstar__leq__tstar : ∀ (t : ka_term T), t⋅t✶ ≤ t✶.
Proof.
  intros.
  rewrite [X in _ ≤ X] Star.
  rewrite Plus_Com.
  apply leq_plus.
Qed.

(* used, but unused *)
Lemma leq__leq_dot_L : ∀ (t1 t2 t3 : ka_term T), t2 ≤ t3 -> t1 ⋅ t2 ≤ t1 ⋅ t3.
Proof.
  intros.
  unfold ka_leq in H.
  rewrite - H.
  rewrite Dist_L.
  rewrite Plus_Com.
  apply leq_plus.
Qed.

(* unused *)
Lemma leq__leq_dot_R : ∀ (t1 t2 t3 : ka_term T), t1 ≤ t3 -> t1 ⋅ t2 ≤ t3 ⋅ t2.
Proof.
  intros.
  unfold ka_leq in H.
  rewrite - H.
  rewrite Dist_R.
  rewrite Plus_Com.
  apply leq_plus.
Qed.

(* unused *)
Lemma pow_leq_star : ∀ (t : ka_term T) n, t^n ≤ t✶.
Proof.
  intros.
  generalize dependent t.
  induction n as [| n IHn].
  - intros. unfold ka_power. apply one_leq_star.
  - intros. simpl.
    rewrite Star.
    assert (H : t⋅t^n ≤ t⋅t✶).
    { apply leq__leq_dot_L. apply IHn. }
    apply leq_trans with (t2:=t⋅t✶).
    + assumption.
    + rewrite Plus_Com. apply leq_plus.
Qed.

(* Theorem 5 *)
Theorem term_lang_equiv : ∀ s t, string_to_ka_term s ≤ t <-> lang_interp t s.
Proof.
  intros; split; intros H.
  - unfold ka_leq in H.
    rewrite l_i_equality. symmetry in H. apply H.
    simpl.
    unfold ka_pred_add. right.
    apply li_term_to_string_true.
  - generalize dependent s.
    induction t; intros.
    + simpl in H. contradiction.
    + simpl in H. unfold ka_pred_unit in H.
      subst. simpl. rewrite Dot_Id2. apply leq_reflex.
    + inversion H. simpl. repeat (rewrite Dot_Id1). apply leq_reflex.
    + inversion H. simpl. rewrite Dot_Id2; rewrite Dot_Id1; apply leq_reflex.
    + simpl in H; unfold ka_pred_add in H. destruct H as [H1 | H2].
      * apply IHt1 in H1.
        apply leq_trans with (t2:=t1);
        [assumption | apply leq_plus].
      * apply IHt2 in H2.
        apply leq_trans with (t2:=t2);
        [assumption | rewrite Plus_Com; apply leq_plus].
    + simpl in H. unfold ka_pred_mul in H.
      destruct H as [s1 [s2 [Hs1s2 [HLI1 HLI2]]]].
      apply IHt1 in HLI1; apply IHt2 in HLI2.
      subst. destruct s1, s2. rewrite string_to_term__pair_append__commute.
      apply leq_leq_dot; assumption.
    + simpl in H. unfold ka_pred_star in H.
      destruct H as [n H].
      generalize dependent s.
      induction n as [| n IHn].
      * intros; simpl in H.
        unfold ka_pred_unit in H; subst.
        simpl; rewrite Dot_Id1.
        apply one_leq_star.
      * intros. simpl in H.
        destruct H as [s1 [s2 [Hs1s2 [HLI1 Hpow]]]].
        apply IHn in Hpow.
        subst.
        apply IHt in HLI1.
        destruct s1 as (s1, s1'), s2 as (s2, s2').
        rewrite string_to_term__pair_append__commute.
        assert (H : string_to_ka_term (s1, s1') ⋅ string_to_ka_term (s2, s2') ≤ t⋅t✶).
        {
          apply leq1__leq2__leq1_dot_2; assumption.
        }
        apply leq_trans with (t2:=t⋅t✶);
        [assumption | apply t_tstar__leq__tstar].
Qed.

(* unused *)
Lemma zero_neq_one : (@K_Zero T ≢ @K_One T)%ka.
Proof.
  intros H.
  (* QUEST: why was using apply not working here?? *)
  have eq_langs := l_i_equality H.
  specialize (eq_langs ([], [])).
  simpl in eq_langs.
  unfold ka_pred_zero, ka_pred_unit in eq_langs.
  rewrite eq_langs.
  reflexivity.
Qed.

(* unused *)
Lemma zero_neq_L : ∀ a, (@K_Zero T ≢ L a).
Proof.
  intros a H.
  have eq_langs := l_i_equality H.
  specialize (eq_langs ([a], [])).
  simpl in eq_langs.
  unfold ka_pred_zero, ka_pred_left in eq_langs.
  rewrite eq_langs.
  reflexivity.
Qed.

(* unused *)
Lemma zero_neq_R : ∀ a, (@K_Zero T ≢ R a).
Proof.
  intros a H.
  have eq_langs := l_i_equality H.
  specialize (eq_langs ([], [a])).
  simpl in eq_langs.
  unfold ka_pred_zero, ka_pred_left in eq_langs.
  rewrite eq_langs.
  reflexivity.
Qed.

(* unused *)
Lemma zero_neq_one_plus_t : ∀ (t : ka_term T), 0 ≢ 1 + t.
Proof.
  intros t H.
  have G := l_i_equality H.
  specialize (G ([], [])).
  simpl in G.
  unfold ka_pred_zero, ka_pred_add, ka_pred_unit in G.
  rewrite G. left. reflexivity.
Qed.

(* unused *)
Lemma zero_neq_L_plus_t : ∀ (t : ka_term T) a, 0 ≢ L a + t.
Proof.
  intros t a H.
  have G := l_i_equality H.
  specialize (G ([a], [])).
  simpl in G.
  unfold ka_pred_zero, ka_pred_add, ka_pred_unit in G.
  rewrite G. left. reflexivity.
Qed.

(* unused *)
Lemma zero_neq_R_plus_t : ∀ (t : ka_term T) a, 0 ≢ R a + t.
Proof.
  intros t a H.
  have G := l_i_equality H.
  specialize (G ([], [a])).
  simpl in G.
  unfold ka_pred_zero, ka_pred_add, ka_pred_unit in G.
  rewrite G. left. reflexivity.
Qed.

(* unused *)
Lemma neq_reflex_false : ∀ (t : ka_term T), not (t ≢ t).
Proof.
  intros t H; apply H; reflexivity.
Qed.

(* Corollary 8' *)
Lemma either_empty_or_nonzero : ∀ (t : ka_term T), t ≡ 0 ∨ ∃ s, lang_interp t s.
Proof.
  intros t.
  induction t.
  - left; reflexivity.
  - right. exists ([], []). reflexivity.
  - right. exists ([t], []). reflexivity.
  - right. exists ([], [t]). reflexivity.
  - destruct IHt1 as [IHt1 | IHt1]; destruct IHt2 as [IHt2 | IHt2].
    + left. rewrite IHt1. rewrite IHt2. apply Plus_Idemp.
    + right. destruct IHt2 as [s H].
      exists s. rewrite IHt1.
      rewrite Plus_Id; assumption.
    + right; destruct IHt1 as [s H].
      exists s; rewrite IHt2.
      rewrite Plus_Id'.
      assumption.
    + destruct IHt1 as [s1 H1], IHt2 as [s2 H2].
      right. exists s1.
      simpl. unfold ka_pred_add.
      left; assumption.
  - destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2].
    + left. rewrite H1. apply Dot_Z2.
    + left. rewrite H1. apply Dot_Z2.
    + left. rewrite H2. apply Dot_Z1.
    + destruct H1 as [s1 H1], H2 as [s2 H2].
      right.
      exists (pair_append s1 s2).
      simpl.
      unfold ka_pred_mul.
      exists s1, s2.
      auto.
  - right. exists ([], []).
    simpl.
    unfold ka_pred_star.
    exists 0%nat.
    reflexivity.
Qed.


Lemma interp_build_term_l : ∀ s, lang_interp (build_term L 1 s) (s, []).
Proof.
  intros s. induction s as [| c s IHs].
  - reflexivity.
  - simpl in *.
    unfold ka_pred_mul, ka_pred_left.
    exists ([c], []), (s, []).
    repeat split; intuition.
Qed.

Lemma interp_build_term_r : ∀ s, lang_interp (build_term R 1 s) ([], s).
Proof.
  intros s. induction s as [| c s IHs].
  - reflexivity.
  - simpl in *.
    unfold ka_pred_mul, ka_pred_left.
    exists ([], [c]), ([], s).
    repeat split; intuition.
Qed.

(* would be nice to prove *)
(* Lemma test : ∀ (t t' : ka_term T), t ≤ t' -> t ≡ t' ∨ ∃ s, lang_interp t' s ∧ not (lang_interp t s).
Proof.
  intros.
  unfold ka_leq in H.
  have eq_langs := l_i_equality H.
  simpl in eq_langs.
  unfold ka_pred_add in eq_langs.
  left. *)

(* Corollary 8'' *)
Lemma no_string_leq_0 : ∀ s, not (string_to_ka_term s ≤ 0).
Proof.
  intros s H.
  unfold ka_leq in H.
  rewrite Plus_Id in H.
  destruct s as (s1, s2).
  simpl in H.
  have eq_langs := l_i_equality H.
  specialize (eq_langs (s1, s2)).
  simpl in eq_langs; unfold ka_pred_mul, ka_pred_zero in eq_langs.
  apply eq_langs.
  exists (s1, []), ([], s2).
  repeat split.
  - simpl; rewrite app_nil_r; reflexivity.
  - apply interp_build_term_l.
  - apply interp_build_term_r.
Qed.

(* unused *)
Lemma no_string_equiv_0 : ∀ s, string_to_ka_term s ≢ 0.
Proof.
  intros s H.
  rewrite <- Plus_Id in H. (* QUEST: ssreflect way of writing this? *)
  apply no_string_leq_0 in H; assumption.
Qed.

(* unused *)
Lemma zero_leq_anything : ∀ (t : ka_term T), 0 ≤ t.
Proof.
  intros.
  unfold ka_leq.
  apply Plus_Id'.
Qed.

Lemma zero_eq_sum : ∀ (t t' : ka_term T), 0 ≡ t + t' <-> 0 ≡ t ∧ 0 ≡ t'.
Proof.
  intros t t'; split.
  - intros H. generalize dependent t'.
    induction t.
    + intros t' H. rewrite Plus_Id in H.
      intuition.
    + intros t' H.
      apply zero_neq_one_plus_t in H.
      exfalso; assumption.
    + intros t' H.
      apply zero_neq_L_plus_t in H.
      exfalso; assumption.
    + intros t' H.
      apply zero_neq_R_plus_t in H.
      exfalso; assumption.
    + intros t' H.
      rewrite - Plus_Assoc in H.
      apply IHt1 in H as [H1 H2].
      apply IHt2 in H2 as [H2 H3].
      rewrite - H1.
      rewrite - H2.
      rewrite Plus_Idemp.
      intuition.
    + intros t' H.
    admit.
    + intros t' H.
      rewrite Star in H.
      rewrite - Plus_Assoc in H.
      apply zero_neq_one_plus_t in H.
      contradiction.
  - intros [H1 H2].
    rewrite - H1; rewrite - H2.
    rewrite Plus_Id.
    reflexivity.
Admitted.

Lemma zero_eq_prod : ∀ (t1 t2 : ka_term T), 0 ≡ t1 ⋅ t2 -> t1 ≡ 0 ∨ t2 ≡ 0.
Proof.
  intros t1 t2 H.
  generalize dependent t2.
  induction t1.
  - intros t2 H; left; reflexivity.
  - intros t2 H. rewrite Dot_Id2 in H.
    right; symmetry; assumption.
  - intros t2 H.
    have [Ht2 | [s Ht2]] := either_empty_or_nonzero t2.
    + right; assumption.
    + have eq_langs := l_i_equality H.
      simpl in eq_langs.
      unfold ka_pred_zero, ka_pred_mul, ka_pred_left in eq_langs.
      exfalso; rewrite eq_langs.
      exists ([t], []), s.
      repeat split.
      auto.
  - intros t2 H.
    have [Ht2 | [s Ht2]] := either_empty_or_nonzero t2.
    + right; assumption.
    + have eq_langs := l_i_equality H.
      simpl in eq_langs.
      unfold ka_pred_zero, ka_pred_mul, ka_pred_right in eq_langs.
      exfalso; rewrite eq_langs.
      exists ([], [t]), s.
      repeat split.
      auto.
  - intros t2 H.
    Search K_Zero.
    have [Ht2 | [s Ht2]] := either_empty_or_nonzero t2.
    + right; assumption.
    + have eq_langs := l_i_equality H.
      simpl in eq_langs.
      unfold ka_pred_zero, ka_pred_mul, ka_pred_add in eq_langs.
Admitted.

(* used but unused *)
Lemma zero_neq_prod : ∀ (t1 t2 : ka_term T), 0 ≢ t1 ⋅ t2 (*<*)-> t1 ≢ 0 ∧ t2 ≢ 0.
Proof.
  (* split;  *)intros t1 t2 H.
  split; intros G.
    + rewrite G in H.
      rewrite Dot_Z2 in H.
      apply H; reflexivity.
    + rewrite G in H.
      rewrite Dot_Z1 in H.
      apply H; reflexivity.
Qed.

(* unused *)
Lemma zero_neq_const_dot_term : ∀ (t t': ka_term T) a, (t ≡ 1 ∨ t ≡ L a ∨ t ≡ R a) -> 0 ≢ t⋅t' -> 0 ≢ t'.
Proof.
  intros t t' a H G.
  destruct H as [H | [H | H]]; rewrite H in G; clear H;
  try (rewrite Dot_Id2 in G; assumption);
  apply zero_neq_prod in G as [G1 G2];
  apply ka_neq_sym; assumption.
Qed.

(* QUEST: is there a nice way to merge these two lemmas? *)
Lemma lang_interp_build_l : ∀ (s1 s2 s3 : list T),
  lang_interp (build_term L 1 s1) (s2, s3) -> s2 = s1 ∧ s3 = [].
Proof.
  intros s1 s2 s3 H. simpl in H.
  generalize dependent s2;
  generalize dependent s3.
  induction s1 as [|c s1 IHs1].
  + intros. simpl in H; unfold ka_pred_unit in H.
    inversion H. intuition.
  + intros.
    simpl in H;
    unfold ka_pred_mul in H.
    destruct H as [s4 [s5 [Hp [Hl HLI]]]].
    unfold ka_pred_left in Hl.
    subst. destruct s5 as (s5, s5'). simpl in Hp.
    inversion Hp; subst.
    apply IHs1 in HLI as [Heq H5].
    subst. intuition.
Qed.

Lemma lang_interp_build_r : ∀ (s1 s2 s3 : list T),
  lang_interp (build_term R 1 s1) (s2, s3) -> s1 = s3 ∧ s2 = [].
Proof.
  intros s1 s2 s3 H. simpl in H.
  generalize dependent s2;
  generalize dependent s3.
  induction s1 as [|c s1 IHs1].
  + intros. simpl in H; unfold ka_pred_unit in H.
    inversion H. intuition.
  + intros.
    simpl in H;
    unfold ka_pred_mul in H.
    destruct H as [s4 [s5 [Hp [Hr HLI]]]].
    unfold ka_pred_right in Hr.
    subst. destruct s5 as (s5, s5'). simpl in Hp.
    inversion Hp. subst.
    apply IHs1 in HLI as [Heq H5].
    subst. intuition.
Qed.

Lemma string_interp_self : ∀ s s', lang_interp (string_to_ka_term s) s' <-> s = s'.
Proof.
  intros.
  split.
  - intros H.
    destruct s as (s1, s2), s' as (s1', s2').
    simpl in H.
    unfold ka_pred_mul in H.
    destruct H as [s3 [s4 [Hs1s2' [HLIs1 HLIs2]]]].
    destruct s3 as (s3, s3'), s4 as (s4, s4').
    simpl in Hs1s2'.
    rewrite Hs1s2'.
    apply lang_interp_build_l in HLIs1 as [H1 H2];
    apply lang_interp_build_r in HLIs2 as [H3 H4].
    subst; simpl; rewrite app_nil_r.
    reflexivity.
  - intros H. rewrite H.
    apply li_term_to_string_true.
Qed.

Fixpoint map_indexed' {A} {B} (f : nat -> A -> B) n ls :=
  match ls with
  | [] => []
  | hd :: tl => f n hd :: map_indexed' f (S n) tl
  end.

Definition map_indexed {A} {B} (f : nat -> A -> B) ls := map_indexed' f 0 ls.

Definition term_product (ls : list (ka_term T)) := fold_right (λ t t', t⋅t') 1 ls.

Definition term_sum (ls : list (ka_term T)) := fold_right (λ t t', t+t') 0 ls.

Definition cstring_sum (ls : list (list T * list T)) := term_sum (map string_to_ka_term ls).

Fixpoint empty_bool (t : ka_term T) :=
  match t with
  | K_Zero => true
  | K_One => false
  | L _ => false
  | R _ => false
  | K_Plus t1 t2 => empty_bool t1 && empty_bool t2
  | K_Dot t1 t2 => empty_bool t1 || empty_bool t2
  | K_Star _ => false
  end.

Global Instance empty_bool_proper : Proper (@ka_eq T ==> eq) empty_bool.
Proof.
move=> t1 t2; elim: t1 t2 / => //=.
- congruence.
- congruence.
- congruence.
- by move=> ?; rewrite Bool.orb_false_r.
- by move=> ?; rewrite Bool.orb_true_r.
- by move=> ???; rewrite Bool.orb_assoc.
- by move=> ??; rewrite Bool.andb_comm.
- by move=> ???; rewrite Bool.andb_assoc.
- by move=> ?; rewrite Bool.andb_diag.
- by move=> ???; rewrite Bool.orb_andb_distrib_r.
- by move=> ???; rewrite Bool.orb_andb_distrib_l.
Qed.

Lemma empty_boolP t : empty_bool t = true ↔ t ≡ 0.
Proof.
split => [|-> //=].
elim: t => //=.
- move=> t1 IH1 t2 IH2 /andb_true_iff [/IH1 -> /IH2 ->].
  exact: Plus_Id.
- move=> t1 IH1 t2 IH2 /orb_true_iff [/IH1 ->|/IH2 ->];
  by rewrite ?Dot_Z1 ?Dot_Z2.
Qed.

Fixpoint below_one (t : ka_term T) :=
  match t with
  | K_Zero => true
  | K_One => true
  | L _ => false
  | R _ => false
  | K_Plus t1 t2 => below_one t1 && below_one t2
  | K_Dot t1 t2 => empty_bool t1 || empty_bool t2 || below_one t1 && below_one t2
  | K_Star t => empty_bool t
  end.

Lemma empty_bool_below_one t : empty_bool t = true → below_one t = true.
Proof.
elim: t => //=.
- by move=> t1 IH1 t2 IH2 /andb_true_iff [/IH1 -> /IH2 ->].
- move=> t1 IH1 t2 IH2 /orb_true_iff [->|->] //=.
  by rewrite orb_true_r.
Qed.

Global Instance below_one_proper : Proper (@ka_eq T ==> eq) below_one.
Proof.
move=> t1 t2; elim: t1 t2 / => //=.
- congruence.
- congruence.
- by move=> t11 t12 e1 -> t21 t22 e2 ->; rewrite e1 e2.
- by move=> ?? {2}->.
- move=> t; rewrite orb_false_r andb_true_r.
  case e: empty_bool => //=.
  by rewrite empty_bool_below_one.
- move=> t; case e: empty_bool => //=.
  by rewrite empty_bool_below_one.
- by move=> t; rewrite orb_true_r.
- move=> t1 t2 t3.
  case e1: (empty_bool t1) => //=.
  case e2: (empty_bool t2) => //=.
  case e3: (empty_bool t3) => //=.
  by rewrite andb_assoc.
- by move=> ??; rewrite andb_comm.
- by move=> ???; rewrite andb_assoc.
- by move=> ?; rewrite andb_diag.
- move=> t1 t2 t3.
  case e1: (empty_bool t1) => //=.
  case e2: (empty_bool t2) => //=.
    by rewrite (empty_bool_below_one e2) andb_true_l.
  case e3: (empty_bool t3) => //=.
    by rewrite (empty_bool_below_one e3) !andb_true_r.
  by case: (below_one t1).
- move=> t1 t2 t3.
  case e1: (empty_bool t1) => //=.
    by rewrite (empty_bool_below_one e1) /=.
  case e2: (empty_bool t2) => //=.
    by rewrite (empty_bool_below_one e2) !andb_true_r.
  case e3: (empty_bool t3) => //=.
  case: (below_one t3).
  + by rewrite !andb_true_r.
  + by rewrite !andb_false_r.
- move=> t; rewrite orb_false_r.
  case e: empty_bool => //=.
  by rewrite andb_false_r.
Qed.

Lemma below_oneP t : below_one t = true ↔ t ≡ 0 ∨ t ≡ 1.
Proof.
split => [|- [->|->] //=].
elim: t => //=; eauto.
- move=> t1 IH1 t2 IH2 /andb_true_iff [/IH1 [] -> /IH2 [] ->].
  + by rewrite Plus_Id; eauto.
  + by rewrite Plus_Id; eauto.
  + by rewrite Plus_Id'; eauto.
  + by rewrite Plus_Idemp; eauto.
- move=> t1 IH1 t2 IH2 /orb_true_iff [].
  + by case/orb_true_iff=> [] /empty_boolP ->;
    rewrite ?Dot_Z1 ?Dot_Z2; eauto.
  + case/andb_true_iff=> /IH1 [] -> /IH2 [] ->.
    * by rewrite Dot_Z1; eauto.
    * by rewrite Dot_Z2; eauto.
    * by rewrite Dot_Z1; eauto.
    * by rewrite Dot_Id1; eauto.
- move=> t IH /empty_boolP ->; right.
  by rewrite Star Dot_Z2 Plus_Id'.
Qed.

Definition finite_term t := ∃ ls, ∀ s, In s ls <-> lang_interp t s.

(* Lemma test : ∀ (P Q R : (list T * list T) -> Prop), (∀ s, P s <-> Q s) -> (∀ s, P s <-> Q s ∨ R s).
Proof.
  intros. *)

Lemma finite_terms__finite_sum : ∀ t t', finite_term t ∧ finite_term t' -> finite_term (t + t').
Proof.
  intros t t' [[l1 H1] [l2 H2]].
  unfold finite_term.
  simpl.
  unfold ka_pred_add.
  exists (l1 ++ l2).
  intros s.
  split.
  + intros H.
    apply in_app_or in H as [H | H];
    [apply H1 in H | apply H2 in H];
    intuition.
  + intros [H | H]; apply in_or_app;
    [apply H1 in H | apply H2 in H];
    intuition.
Qed.

Lemma finite_term_dist_over_plus : ∀ t t', finite_term (t + t') <-> finite_term t ∧ finite_term t'.
Proof.
  intros t t'. split.
  - intros [ls H].
    simpl in H;
    unfold ka_pred_add in H.
    (* admit. *)
    split; unfold finite_term.
    + exists ls.
      intros s.
      rewrite H.
      split.
      * intros [G | G]; try assumption.
        admit.
      * intuition.
    + exists ls.
      intros s.
      rewrite H.
      split.
      * intros [G | G]; try assumption.
        admit.
      * intuition.
  - intros [[l1 H1] [l2 H2]].
    unfold finite_term.
    simpl.
    unfold ka_pred_add.
    exists (l1 ++ l2).
    intros s.
    split.
    + intros H.
      apply in_app_or in H as [H | H];
      [apply H1 in H | apply H2 in H];
      intuition.
    + intros [H | H]; apply in_or_app;
      [apply H1 in H | apply H2 in H];
      intuition.
Admitted.

Lemma finite_term_dist_over_dot : ∀ t t', finite_term (t ⋅ t') <-> finite_term t ∧ finite_term t'.
Proof.
Admitted.

Lemma cstring_app_commute : ∀ l1 l2,
  cstring_sum (l1 ++ l2) ≡ (cstring_sum l1) + (cstring_sum l2).
Proof.
  intros.
  induction l1 as [| c1 l1 IHl1].
  + simpl.
    unfold cstring_sum; simpl.
    rewrite Plus_Id; reflexivity.
  + simpl. unfold cstring_sum. simpl.
    unfold cstring_sum in IHl1.
    rewrite IHl1.
    apply Plus_Assoc.
Qed.

Lemma zero_star : (@K_Zero T)✶ ≡ @K_One T.
Proof.
  rewrite Star.
  rewrite Dot_Z2.
  rewrite Plus_Com.
  rewrite Plus_Id.
  reflexivity.
Qed.

Lemma one_star : (@K_One T)✶ ≡ @K_One T.
Proof.
Admitted.

Lemma finite_star : ∀ (t : ka_term T), t ≡ 0 ∨ t ≡ 1 ∨ not (finite_term (t✶)).
Proof.
  intros t.
  induction t;
  try (left; reflexivity);
  try (right; left; reflexivity);
  right; right; intros [ls H].
  - induction ls as [| c l IHl].
    + specialize (H ([], [])).
      simpl in H.
      rewrite H.
      unfold ka_pred_left, ka_pred_star.
      exists 0%nat.
      reflexivity.
+ Admitted.

(* Theorem 6' *)
Theorem finite_def : ∀ t,
  (∃ ls, t ≡ cstring_sum ls)
  <->
  finite_term t.
Proof.
  intros t; split.
  - intros [ls H].
    exists ls.
    intros s.
    rewrite H; clear H.
    induction ls as [| c ls IHls].
    + simpl. reflexivity.
    + simpl. unfold ka_pred_add.
      rewrite - IHls.
      rewrite string_interp_self.
      reflexivity.
  -
    (* intros [ls H].
    exists ls.
    induction t.
    + simpl in H. unfold ka_pred_zero in H.
      induction ls.
      * reflexivity.
      * specialize (H a0). simpl in H.
        exfalso; apply H. intuition.
    + simpl in H. unfold ka_pred_unit in H.
      induction ls as [| c ls IHls].
      * specialize (H ([], []));
        simpl in H.
        exfalso; intuition.
      * simpl in H.
        specialize (H c); simpl in H. *)
    (* unfold finite_term. *)
    (* intros [ls H]. *)
    induction t(* ; intros [ls H] *).
    + intros [ls H]. exists []. reflexivity.
    + intros [ls H]. exists [([], [])]. unfold cstring_sum. simpl.
      rewrite Dot_Id2; rewrite Plus_Id'.
      reflexivity.
    + intros [ls H]. exists [([t], [])]; unfold cstring_sum; simpl.
      repeat (rewrite Dot_Id1);
      rewrite Plus_Id'.
      reflexivity.
    + intros [ls H]. exists [([], [t])]; unfold cstring_sum; simpl.
      rewrite Dot_Id1;
      rewrite Dot_Id2;
      rewrite Plus_Id'.
      reflexivity.
    + rewrite finite_term_dist_over_plus. intros [H1 H2].
      apply IHt1 in H1 as [l1 H1].
      apply IHt2 in H2 as [l2 H2].
      exists (l1 ++ l2).
      simpl.
      rewrite cstring_app_commute.
      rewrite H1; rewrite H2.
      reflexivity.
    + admit.
    + intros [ls H].
      induction t.
      * exists [([], [])].
        unfold cstring_sum.
        simpl.
        rewrite zero_star.
        rewrite Plus_Com; rewrite Plus_Id;
        rewrite Dot_Id2.
        reflexivity.
      * exists [([], [])].
        unfold cstring_sum;
        simpl.
        rewrite one_star.
        rewrite Plus_Com; rewrite Plus_Id;
        rewrite Dot_Id2.
        reflexivity.
      *

    (* + rewrite finite_term_dist_over_dot. intros [H1 H2].
      apply IHt1 in H1 as [l1 H1].
      apply IHt2 in H2 as [l2 H2].

    intros [[l1 H1] [l2 H2]]. simpl in H.
      unfold ka_pred_add in H.
      unfold finite_term in IHt1, IHt2.
      induction ls as [|c ls IHls].
      * have [t_cond1 | [s1 t_cond1]] := either_empty_or_nonzero t1;
        have [t_cond2 | [s2 t_cond2]] := either_empty_or_nonzero t2;
        try (specialize (H s1); simpl in H; exfalso; rewrite H; intuition).
        -- exists []. rewrite t_cond1; rewrite t_cond2; rewrite Plus_Idemp.
           reflexivity.
        -- specialize (H s2).
           simpl in H.
           exfalso. rewrite H. intuition.
      * simpl in H.
        specialize (H c) as [c' H]. *)
Admitted.

(* Corollary 7' *)
Theorem finite_terms_interp__equiv : ∀ (t t' : ka_term T),
  finite_term t -> finite_term t' ->
    (∀ s, lang_interp t s <-> lang_interp t' s) ->
      t ≡ t'.
Proof.
  intros t t' Hft Hft' Hli.
  have Hft1 := Hft.
  have Hft1' := Hft'.
  apply finite_def in Hft1 as [ls Htsum], Hft1' as [ls' Htsum'].
  destruct Hft as [s Ht], Hft' as [s' Ht'].
  rewrite Hli in Ht.
  rewrite Htsum.
  rewrite Htsum'.
  unfold cstring_sum.
  unfold cstring_sum.
  induction ls as [|c ls IHls], ls' as [|c' ls'].
  - reflexivity.
  - simpl in *.
    unfold cstring_sum in Htsum.
    simpl in Htsum.
  induction ls as [|c ls IHls].
  - unfold cstring_sum in Htsum. simpl in Htsum. simpl.
  assert (G : cstring_sum ls ≡ cstring_sum ls').
  {
    unfold cstring_sum.
    unfold map.
    compute.
  }

(* QUEST: How to allow term_list_to_term to be generic here? *)

(* Definition C_M (P : list mm2_instr) := *)



(* Fixpoint R_M' (P' P : list mm2_instr) (n : nat) := match P with
  | [] => 0
  | hd :: tl => (interp n P) ⋅ (L (Q_M n)) + R_M' tl P (S n)
  end. *)

(* Definition R_M (P : list mm2_instr) := R_M' P P 1. *)

(* Fixpoint C_M' (P : list mm2_instr) (n : nat) := match P with
  | [] => 0
  | _::tl => L (Q_M n) + C_M' tl (S n)
  end. *)

(* Definition C_M (P : list mm2_instr) := (L a)✶ ⋅ (L b)✶ ⋅ (C_M' P 1). *)

End Theory.
(* -------------- *)

Definition R_M (P : list mm2_instr) :=
   term_list_to_term (map_indexed interp_single P).

(* Local Open Scope ka_scope. *)

Example string_to_ka_term__test1 :
  string_to_ka_term ([a; b; a; a], [a; b; a; a]) ≡ (lr a ⋅ lr b ⋅ lr a ⋅ lr a).
Proof.
  simpl; unfold lr_term.
  rewrite Dot_Id1.
  repeat (rewrite Dot_Assoc).
  reflexivity.
Qed.

Example string_to_ka_term__test2 :
  string_to_ka_term Σ_M [a; b; c_1] ≡ lr a ⋅ lr b ⋅ lr c_1.
Proof.
  simpl; unfold lr_term.
  rewrite Dot_Id1.
  repeat (rewrite Dot_Assoc).
  reflexivity.
Qed.

Check lang_interp.
Theorem term_leq_R_M__in_lang_interp : ∀ P s s', (string_to_ka_term Σ_M L s) ⋅ (string_to_ka_term Σ_M R s') ≤ R_M P <-> lang_interp Σ_M (R_M P) (s, s').
Proof.
  simpl; split; intros.
  - unfold R_M.

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

(* Theorem left_assoc_equiv e : left_assoc e ≡ e.
Proof.
  induction e; try (reflexivity).
  - assert (H : left_assoc (e1 + e2) ≡ (left_assoc e1) + left_assoc e2).
    { simpl. inversion IHe2; subst. compute. }
  rewrite <- IHe1. generalize dependent IHe2.
    induction e2; try reflexivity.
    intros. rewrite <- IHe2.
    simpl.
    compute. *)

(* Definition canonicalize e := left_assoc (remove_1 (compose_L_R (collect_L_R e [] []))).

Theorem canonicalize_equiv e : canonicalize e ≡ e.
Proof.
  induction e; try (compute; reflexivity).
  - unfold canonicalize.
    assert
    unfold collect_L_R.
  assert (H : canonicalize (e1 + e2) ≡ (canonicalize e1) + (canonicalize e2)).
    { rewrite IHe1. rewrite IHe2. compute. }
  unfold canonicalize.
    unfold collect_L_R. *)

End Canonicalization.

Local Open Scope ka_scope.

Example check_canonicalize : canonicalize Σ_M (R a ⋅ L a ⋅ R b ⋅ L b) ≡ L a ⋅ L b ⋅ R a ⋅ R b.
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

(* Example to_L__R_ex1 : ∀ x y, to_L__R ((lr x)⋅(lr y)) ≡ (L x)⋅(L y)⋅(R x)⋅(R y).
Proof.
  intros.
  (* unfold lr_term. *)
  reflexivity.
Qed.

Example to_L__R_ex2 : ∀ x y z, to_L__R ((lr x)⋅(lr y)⋅(lr z)) ≡ L x⋅L y⋅L z⋅R x⋅R y⋅R z.
Proof.
  intros.
  simpl. *)



Lemma plus_interleave : ∀ (x y z w : ka_term T), x + y + z + w ≡ x + z + y + w.
Proof.
  intros.
  rewrite <- Plus_Assoc.
  rewrite <- Plus_Assoc.
  assert (G : y + (z + w) ≡ (z + w) + y). { apply Plus_Com. }
  rewrite G.
  assert (H : y + w ≡ w + y). { apply Plus_Com. }
  rewrite <- Plus_Assoc.
  rewrite <- H.
  rewrite Plus_Assoc.
  rewrite Plus_Assoc.
  reflexivity.
Qed.

Lemma extra_one_ignore : forall (x : ka_term T), 1 + 1 + x ≡ 1 + x.
Proof.
  intros.
  rewrite Plus_Idemp.
  reflexivity.
Qed.

Print step_relation.
Locate "lr".




Lemma x_xstar__xtar_x : forall (t : ka_term T), t⋅t✶ ≡ t✶⋅t.
Proof.
  intros.
  induction t.
  - rewrite Dot_Z2. rewrite Dot_Z1. reflexivity.
  - rewrite Dot_Id2. rewrite Dot_Id1. reflexivity.
  - admit.
  - admit.
  - rewrite Dist_R. rewrite Dist_L.
Admitted. (* should follow from t⋅t✶ ≡ t✶ ≡ t✶⋅t *)


Lemma x_x_star : forall (t : ka_term T), t✶ ≡ t✶⋅t.
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
  assert (H : t ≡ t⋅1).
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
  ≡ [[l a]]⋅[[r a]]⋅[[l b]]⋅[[r b]]⋅[[l (Q_M 1)]]⋅[[r (Q_M 1)]].
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
  ka_power kat (n + m) ≡ K_Dot (ka_power kat n) (ka_power kat m).
Proof.
  intros.
  induction n.
  - simpl. rewrite Dot_Id2. reflexivity.
  - simpl. rewrite IHn. rewrite Dot_Assoc. reflexivity.
Qed.

Lemma test : forall T (t : ka_term T), t + 0 ≡ t.
Proof.
intros. rewrite Plus_Com. by constructor. Qed.

Lemma plus_assoc_swap1 : ∀ T (x y z : ka_term T),
  x + (y + z) ≡ x + (z + y).
Proof.
  intros. assert (H: y+z ≡ z + y).
  - apply Plus_Com.
  - rewrite H. reflexivity.
Qed.

Lemma plus_assoc_swap2 : ∀ T (x y z : ka_term T),
  x + (y + z) ≡ (x + z) + y.
Proof.
  intros. assert (H: y+z≐z+y).
  - apply Plus_Com.
  - rewrite H. apply Plus_Assoc.
Qed.

(* QUEST: why does this struggle with typing? *)
Lemma test_1 : forall (T:Type) (x y z : ka_term T), x ≤ y -> (x + z ≡ (x + y) + z).
Proof.
  intros. unfold ka_leq in H. rewrite Plus_Com in H. rewrite H. reflexivity.
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
