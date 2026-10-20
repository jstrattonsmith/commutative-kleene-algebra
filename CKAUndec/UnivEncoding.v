(* A second MM2 encoding, adapted from the universality construction of
   Xu, Zhou, Walker and Kincaid (arXiv:2607.09635, Section 4) to pre-KA.
   The carrier is `list L * nat`, where `L = option (mm_sym Q)` (`None` is
   the separator `#`) and the `nat` component counts a letter that
   commutes with everything. A run `c0, ..., cN` of the machine is the
   word `# c0 # c1 # ... # cN #`, a configuration `(n, q, m)` being
   `a^n q b^m`.

   The inequality is `bal_star ⊑ univ_ub c0`, where `bal_star` (from
   KA/balanced.v) is the star of the balanced letters `([t], 1)`. The
   upper bound collects error detectors: each one recognizes a
   balanced prefix that cannot be the prefix of a correct run reaching
   `(0, q0, 0)`, padded with `bal_star`. Weighted letters (`(a, 0)`,
   `(a, 2)`, ...) make a pattern balanced exactly when a counter
   changes incorrectly between two consecutive configurations.

   - Completeness (`univ_complete_gen`): if the run halts at
     `(0, q0, 0)`, every word deviating from the run word is caught at
     the letter where it deviates, so KA/balanced.v's
     `bal_univ_complete` applies with `D` = length of the run word + 1.
   - Soundness (`univ_sound_gen`): the run word of a run halting
     elsewhere is matched by no detector.

   The first part is generic over a deterministic two-counter program
   on a finite state set; `Section MM2Univ` instantiates it with
   CKAUndec/Encoding.v's MM2 adapter. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite fin relations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.balanced.
From kacc Require Import KA.BinaryAlphabetTransport KA.BalancedBinary.
From kacc Require Import CKAUndec.Encoding.
From Undecidability.MinskyMachines.Util Require Import
  MM2_facts MM2_stepper MM2_simulator.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

(* `ka_scope` reads a bare `1` as the unit of the ambient monoid, which for
   the weights (KA/balanced.v's additive `nat`) is `0`. Numerals here are
   natural numbers; the unit of KA terms is written `1%ka`. *)
Local Open Scope nat_scope.

Section UnivGeneric.

Context {Q : Type} `{!EqDecision Q, !Finite Q}.

Notation L := (option_setoid (@mm_sym_setoid Q)).
Notation M := (prod_monoid (list_monoid L) nat_add_monoid).
Notation term := (ka_term M).

Notation hash := (None : L).
Notation la := (Some mm_a : L).
Notation lb := (Some mm_b : L).
Notation lq q := (Some (mm_q q) : L).

Notation bstar := (bal_star (A := L)).
Notation bal := (bal (A := L)).

(** ** The machine *)

Variable prog : Q → mm_instr Q.
Variable nxt : Q → Q.
Variable acts : list Q.
Variable q0 : Q.

Definition uconf : Type := nat * Q * nat.

Definition ustep (c : uconf) : uconf :=
  let '(n, q, m) := c in
  match prog q with
  | mm_inc_a => (S n, nxt q, m)
  | mm_inc_b => (n, nxt q, S m)
  | mm_dec_a j => match n with 0 => (0, nxt q, m) | S n => (n, j, m) end
  | mm_dec_b j => match m with 0 => (n, nxt q, 0) | S m => (n, j, m) end
  end.

(* A run: every configuration but the last is active and steps to the
   next one. *)
Fixpoint uchain (cs : list uconf) : Prop :=
  match cs with
  | c :: ((c' :: _) as cs') => c.1.2 ∈ acts ∧ c' = ustep c ∧ uchain cs'
  | _ => True
  end.

(* The next state and the counter constants, given whether each counter
   is zero. `ma`/`fa` satisfy `n + ma = n' + 1` and `n' + fa = n + 1`,
   where `n'` is the next value of the first counter (`ustep_arith`);
   `mb`/`fb` likewise for the second one. *)
Definition unext (q : Q) (za zb : bool) : Q :=
  match prog q with
  | mm_dec_a j => if za then nxt q else j
  | mm_dec_b j => if zb then nxt q else j
  | _ => nxt q
  end.

Definition ma (q : Q) (za : bool) : nat :=
  match prog q with
  | mm_inc_a => 2
  | mm_dec_a _ => if za then 1 else 0
  | _ => 1
  end.

Definition fa (q : Q) (za : bool) : nat :=
  match prog q with
  | mm_inc_a => 0
  | mm_dec_a _ => if za then 1 else 2
  | _ => 1
  end.

Definition mb (q : Q) (zb : bool) : nat :=
  match prog q with
  | mm_inc_b => 2
  | mm_dec_b _ => if zb then 1 else 0
  | _ => 1
  end.

Definition fb (q : Q) (zb : bool) : nat :=
  match prog q with
  | mm_inc_b => 0
  | mm_dec_b _ => if zb then 1 else 2
  | _ => 1
  end.

Lemma ustep_arith n q m :
  let '(n', q', m') := ustep (n, q, m) in
  let za := Nat.eqb n 0 in
  let zb := Nat.eqb m 0 in
  q' = unext q za zb ∧
  n + ma q za = n' + 1 ∧ n' + fa q za = n + 1 ∧
  m + mb q zb = m' + 1 ∧ m' + fb q zb = m + 1.
Proof.
rewrite /ustep /unext /ma /fa /mb /fb.
case: (prog q) => [||j|j]; case: n => [|n]; case: m => [|m] /=;
  repeat split; first [reflexivity | lia].
Qed.

(** ** Words *)

Definition uword (c : uconf) : list L :=
  let '(n, q, m) := c in repeat la n ++ lq q :: repeat lb m.

Definition cw (c : uconf) : list L := uword c ++ [hash].

Fixpoint rw (cs : list uconf) : list L :=
  match cs with [] => [] | c :: cs => cw c ++ rw cs end.

Definition run (cs : list uconf) : list L := hash :: rw cs.

(** ** Terms *)

Definition wl (t : L) (k : nat) : term := Unit ([t], k).
Definition cst (k : nat) : term := Unit ([], k).
Definition wstar (t : L) (k : nat) : term := star (wl t k).

(* A block of `t`s of weight `k` each, empty iff `z`. *)
Definition gw (t : L) (z : bool) (k : nat) : term :=
  if z then 1%ka else wl t k ⋅ wstar t k.

(* A block of `t`s of total weight at most its length, empty iff `z`. *)
Definition gs (t : L) (z : bool) : term :=
  if z then 1%ka else wstar t 0 ⋅ (wl t 0 ⊔ wl t 1) ⋅ wstar t 1.

Definition qall : term := ⨆ q ∈ enum Q, wl (lq q) 1.

Definition qbut (q' : Q) : term :=
  ⨆ q ∈ enum Q, if bool_decide (q = q') then ⊥ else wl (lq q) 1.

(* `# a^n q b^m #`, the configuration whose successor is checked. *)
Definition head (q : Q) (blkA blkB : term) : term :=
  wl hash 1 ⋅ blkA ⋅ wl (lq q) 1 ⋅ blkB ⋅ wl hash 1.

(* Wrong next state. *)
Definition w_ctrl q za zb : term :=
  head q (gw la za 1) (gw lb zb 1) ⋅ wstar la 1 ⋅ qbut (unext q za zb).

(* Too many `a`s: fires on the offending `a`. *)
Definition w_ma q za zb : term :=
  head q (gw la za 2) (gw lb zb 1) ⋅ wstar la 0 ⋅ cst (ma q za).

(* Too few `a`s: fires on the next state. *)
Definition w_fa q za zb : term :=
  head q (gs la za) (gw lb zb 1) ⋅ wstar la 2 ⋅ qall ⋅ cst (fa q za).

(* Too many `b`s: fires on the offending `b`. *)
Definition w_mb q za zb : term :=
  head q (gw la za 1) (gw lb zb 2) ⋅ wstar la 1 ⋅ qall ⋅ wstar lb 0 ⋅
  cst (mb q zb).

(* Too few `b`s: fires on the next `#`. *)
Definition w_fb q za zb : term :=
  head q (gw la za 1) (gs lb zb) ⋅ wstar la 1 ⋅ qall ⋅ wstar lb 2 ⋅
  wl hash 1 ⋅ cst (fb q zb).

Definition w_all q za zb : term :=
  w_ctrl q za zb ⊔ w_ma q za zb ⊔ w_fa q za zb ⊔ w_mb q za zb ⊔ w_fb q za zb.

Definition e_win : term :=
  ⨆ q ∈ acts, ⨆ za ∈ [true; false], ⨆ zb ∈ [true; false], w_all q za zb.

(* Pairs of adjacent letters that never occur in a run word. *)
Definition bad (x y : L) : bool :=
  match x, y with
  | None, None | None, Some mm_b => true
  | Some mm_a, None | Some mm_a, Some mm_b => true
  | Some (mm_q _), Some mm_a | Some mm_b, Some mm_a => true
  | Some (mm_q _), Some (mm_q _) | Some mm_b, Some (mm_q _) => true
  | _, _ => false
  end.

Definition e_shape : term :=
  ⨆ x ∈ enum L, ⨆ y ∈ enum L, if bad x y then bal [x; y] else ⊥.

Definition e_halt0 : term := bal [hash; lq q0; hash].

(* Wrong letters while reading the initial configuration. *)
Fixpoint init_errs (pre w : list L) : term :=
  match w with
  | [] => ⊥
  | t0 :: w =>
    (⨆ t ∈ enum L, if bool_decide (t = t0) then ⊥ else bal (pre ++ [t]))
    ⊔ init_errs (pre ++ [t0]) w
  end.

Definition e_pre (c0 : uconf) : term :=
  init_errs [] (run [c0]) ⊔ bstar ⋅ (e_halt0 ⊔ e_shape ⊔ e_win).

(* Short words: proper prefixes of a run word that has not halted. *)
Definition e_end : term :=
  1%ka ⊔ bal [hash]
  ⊔ bstar ⋅ (⨆ t ∈ enum L, if bool_decide (t = hash) then ⊥ else bal [t])
  ⊔ bstar ⋅ (⨆ q ∈ acts, head q (wstar la 1) (wstar lb 1)).

Definition univ_ub (c0 : uconf) : term := e_end ⊔ e_pre c0 ⋅ bstar.

(** ** Languages of the building blocks *)

Implicit Types (w v u : list L) (k : nat).

Lemma l_unit_eq (x y : M) : l (Unit x) y ↔ y = x.
Proof. by split => [/M_equiv_eq|->]. Qed.

Lemma l_mul_inv (X Y : term) w k :
  l (X ⋅ Y) (w, k) →
  ∃ w1 k1 w2 k2, w = w1 ++ w2 ∧ k = k1 + k2 ∧ l X (w1, k1) ∧ l Y (w2, k2).
Proof.
case=> - [w1 k1] [] - [w2 k2] [] /M_equiv_eq [-> ->] [] H1 H2.
by exists w1, k1, w2, k2.
Qed.

Lemma l_mul_intro (X Y : term) w1 k1 w2 k2 :
  l X (w1, k1) → l Y (w2, k2) → l (X ⋅ Y) (w1 ++ w2, k1 + k2).
Proof. by move=> H1 H2; exists (w1, k1), (w2, k2). Qed.

Lemma l_join (X Y : term) y : l (X ⊔ Y) y ↔ l X y ∨ l Y y.
Proof. by []. Qed.

Lemma l_one y : l (1%ka : term) y ↔ y = ([], 0).
Proof. exact: l_unit_eq. Qed.

Lemma l_wl t k' w k : l (wl t k') (w, k) ↔ w = [t] ∧ k = k'.
Proof. by rewrite l_unit_eq; split => [[-> ->]|[-> ->]]. Qed.

Lemma l_cst k' w k : l (cst k') (w, k) ↔ w = [] ∧ k = k'.
Proof. by rewrite l_unit_eq; split => [[-> ->]|[-> ->]]. Qed.

Lemma l_wstar t k' w k :
  l (wstar t k') (w, k) ↔ ∃ n, w = repeat t n ∧ k = k' * n.
Proof.
split.
- case=> n; elim: n w k => [|n IH] w k /=.
    by move=> /M_equiv_eq [-> ->]; exists 0; split => //; lia.
  case=> - [w1 k1] [] - [w2 k2] [] /M_equiv_eq [-> ->] [].
  move=> /l_unit_eq [-> ->] /IH [i [-> ->]].
  by exists (S i); split => //=; rewrite nat_add_mulE; lia.
- case=> n [-> ->]; exists n; elim: n => [|n IH].
    by apply: M_eq_equiv; rewrite Nat.mul_0_r.
  exists ([t], k'), (repeat t n, k' * n); split; last by split.
  apply: M_eq_equiv; rewrite M_mulE; f_equal; lia.
Qed.

Lemma l_gw t z k' w k :
  l (gw t z k') (w, k) ↔
  ∃ n, w = repeat t n ∧ k = k' * n ∧ z = Nat.eqb n 0.
Proof.
rewrite /gw; case: z; split.
- by move=> /l_one [-> ->]; exists 0.
- by case=> - [|n] [-> [-> //]]; rewrite l_one Nat.mul_0_r.
- case/l_mul_inv => w1 [k1 [w2 [k2 [-> [->]]]]].
  case=> /l_wl [-> ->] /l_wstar [n [-> ->]].
  by exists (S n); split => //; split => //=; lia.
- case=> - [|n] [-> [-> //]] _.
  have -> : k' * S n = k' + k' * n by lia.
  apply: (l_mul_intro (w1 := [t])); first exact/l_wl.
  by apply/l_wstar; exists n.
Qed.

Lemma l_gs t z w k :
  l (gs t z) (w, k) ↔ ∃ n, w = repeat t n ∧ k ≤ n ∧ z = Nat.eqb n 0.
Proof.
rewrite /gs; case: z; split.
- by move=> /l_one [-> ->]; exists 0.
- by case=> - [|n] [-> [? //]]; rewrite l_one; have -> : k = 0 by lia.
- case/l_mul_inv => w12 [k12 [w3 [k3 [-> [->]]]]].
  case=> /l_mul_inv [w1 [k1 [w2 [k2 [-> [-> [H1 H2]]]]]]] H3.
  case/l_wstar: H1 => n1 [-> ->]; case/l_wstar: H3 => n3 [-> ->].
  have [-> Hk2] : w2 = [t] ∧ k2 ≤ 1.
  { by case/l_join: H2 => /l_wl [-> ->]; split => //; lia. }
  exists (n1 + S n3); split; first by rewrite repeat_app -app_assoc.
  by split; [lia|rewrite Nat.add_succ_r].
- case=> - [|n] [-> [Hk _]] //.
  have [n1 [n3 [k2 [-> [-> Hk2]]]]] : ∃ n1 n3 k2,
      S n = n1 + S n3 ∧ k = k2 + n3 ∧ k2 ≤ 1.
  { case: k Hk => [|k] Hk.
    - by exists n, 0, 0; split => //; lia.
    - by exists (n - k), k, 1; split => //; lia. }
  have -> : repeat t (n1 + S n3) = (repeat t n1 ++ [t]) ++ repeat t n3.
  { by rewrite repeat_app -app_assoc. }
  have -> : k2 + n3 = 0 * n1 + k2 + 1 * n3 by lia.
  apply: l_mul_intro; last by apply/l_wstar; exists n3.
  apply: l_mul_intro; first by apply/l_wstar; exists n1.
  apply/l_join.
  by case: k2 Hk2 => [|[|?]] ?; [left|right|lia]; apply/l_wl.
Qed.

Lemma l_qall w k : l qall (w, k) ↔ ∃ q, w = [lq q] ∧ k = 1.
Proof.
rewrite /qall semi_lattice_morphism_join_list elem_of_lang_join_list.
split.
- by case=> q [] _ /l_wl [-> ->]; exists q.
- case=> q [-> ->]; exists q; split; first exact: elem_of_enum.
  exact/l_wl.
Qed.

Lemma l_qbut q' w k :
  l (qbut q') (w, k) ↔ ∃ q, q ≠ q' ∧ w = [lq q] ∧ k = 1.
Proof.
rewrite /qbut semi_lattice_morphism_join_list elem_of_lang_join_list.
split.
- case=> q [] _; rewrite /compose; case_bool_decide as Hq; first by case.
  by move=> /l_wl [-> ->]; exists q.
- case=> q [? [-> ->]]; exists q; split; first exact: elem_of_enum.
  by rewrite /compose; case_bool_decide; last apply/l_wl.
Qed.

Lemma l_head q A B w k :
  l (head q A B) (w, k) ↔
  ∃ wA kA wB kB, w = hash :: wA ++ lq q :: wB ++ [hash] ∧
    k = kA + kB + 3 ∧ l A (wA, kA) ∧ l B (wB, kB).
Proof.
rewrite /head; split.
- case/l_mul_inv => w4 [k4 [w5 [k5 [-> [-> [H4 /l_wl [-> ->]]]]]]].
  case/l_mul_inv: H4 => w3 [k3 [wB [kB [-> [-> [H3 HB]]]]]].
  case/l_mul_inv: H3 => w2 [k2 [w3' [k3' [-> [-> [H2 /l_wl [-> ->]]]]]]].
  case/l_mul_inv: H2 => w1 [k1 [wA [kA [-> [-> [/l_wl [-> ->] HA]]]]]].
  exists wA, kA, wB, kB; split; last by split => //; lia.
  by rewrite /= -!app_assoc.
- case=> wA [kA [wB [kB [-> [-> [HA HB]]]]]].
  have -> : hash :: wA ++ lq q :: wB ++ [hash] =
            ((([hash] ++ wA) ++ [lq q]) ++ wB) ++ [hash].
  { by rewrite /= -!app_assoc. }
  have -> : kA + kB + 3 = (((1 + kA) + 1) + kB) + 1 by lia.
  apply: l_mul_intro; last exact/l_wl.
  apply: l_mul_intro => //.
  apply: l_mul_intro; last exact/l_wl.
  apply: l_mul_intro => //; exact/l_wl.
Qed.

Lemma l_mul_intro' (X Y : term) w1 k1 w2 k2 w k :
  l X (w1, k1) → l Y (w2, k2) → w = w1 ++ w2 → k = k1 + k2 →
  l (X ⋅ Y) (w, k).
Proof. by move=> H1 H2 -> ->; apply: l_mul_intro. Qed.

Ltac weq :=
  rewrite /= ?app_nil_r -?app_assoc /= -?app_assoc /= ?app_nil_r; reflexivity.

Ltac len := simpl; repeat (rewrite length_app /=); rewrite ?repeat_length; lia.

Ltac lenH H :=
  simpl in H; repeat (rewrite length_app /= in H); rewrite ?repeat_length in H.

Ltac head_intro n m :=
  apply/l_head; eexists (repeat la n), _, (repeat lb m), _;
  split; first reflexivity; split; first reflexivity; split.

Ltac gw_intro n :=
  apply/l_gw; exists n; split; first reflexivity; split; first reflexivity;
  assumption.

(** ** The window patterns *)

Lemma l_w_ctrl q za zb v :
  l (w_ctrl q za zb) (v, length v) ↔
  ∃ n m j q'', v = hash :: uword (n, q, m) ++ hash :: repeat la j ++ [lq q''] ∧
    za = Nat.eqb n 0 ∧ zb = Nat.eqb m 0 ∧ q'' ≠ unext q za zb.
Proof.
rewrite /w_ctrl; split.
- case/l_mul_inv => v1 [k1 [v2 [k2 [-> [_ [H1 /l_qbut [q'' [Hq [-> _]]]]]]]]].
  case/l_mul_inv: H1 => v0 [k0 [v3 [k3 [-> [_ [H0 /l_wstar [j [-> _]]]]]]]].
  case/l_head: H0 => wA [kA [wB [kB [-> [_ [HA HB]]]]]].
  case/l_gw: HA => n [-> [_ Hza]]; case/l_gw: HB => m [-> [_ Hzb]].
  by exists n, m, j, q''; split; first weq.
- case=> n [m [j [q'' [-> [Hza [Hzb Hq]]]]]].
  eapply l_mul_intro'; first eapply l_mul_intro'.
  + by head_intro n m; [gw_intro n|gw_intro m].
  + by apply/l_wstar; exists j.
  + reflexivity.
  + reflexivity.
  + by apply/l_qbut; exists q''.
  + weq.
  + len.
Qed.

Lemma l_w_ma q za zb v :
  l (w_ma q za zb) (v, length v) ↔
  ∃ n m j, v = hash :: uword (n, q, m) ++ hash :: repeat la j ∧
    za = Nat.eqb n 0 ∧ zb = Nat.eqb m 0 ∧ j = n + ma q za.
Proof.
rewrite /w_ma; split.
- case/l_mul_inv => v1 [k1 [v2 [k2 [? [Hk [H1 /l_cst [? ?]]]]]]].
  case/l_mul_inv: H1 => v0 [k0 [v3 [k3 [? [? [H0 /l_wstar [j [? ?]]]]]]]].
  case/l_head: H0 => wA [kA [wB [kB [? [? [HA HB]]]]]].
  case/l_gw: HA => n [? [? Hza]]; case/l_gw: HB => m [? [? Hzb]].
  subst; exists n, m, j; split; first weq.
  by do 2!split => //; lenH Hk; lia.
- case=> n [m [j [-> [Hza [Hzb Hj]]]]].
  eapply l_mul_intro'; first eapply l_mul_intro'.
  + by head_intro n m; [gw_intro n|gw_intro m].
  + by apply/l_wstar; exists j.
  + reflexivity.
  + reflexivity.
  + exact/l_cst.
  + weq.
  + len.
Qed.

Lemma l_w_fa q za zb v :
  l (w_fa q za zb) (v, length v) ↔
  ∃ n m j q'', v = hash :: uword (n, q, m) ++ hash :: repeat la j ++ [lq q''] ∧
    za = Nat.eqb n 0 ∧ zb = Nat.eqb m 0 ∧ j + fa q za ≤ n.
Proof.
rewrite /w_fa; split.
- case/l_mul_inv => v1 [k1 [v2 [k2 [? [Hk [H1 /l_cst [? ?]]]]]]].
  case/l_mul_inv: H1 => v0 [k0 [v4 [k4 [? [? [H0 /l_qall [q'' [? ?]]]]]]]].
  case/l_mul_inv: H0 => v5 [k5 [v3 [k3 [? [? [H5 /l_wstar [j [? ?]]]]]]]].
  case/l_head: H5 => wA [kA [wB [kB [? [? [HA HB]]]]]].
  case/l_gs: HA => n [? [HkA Hza]]; case/l_gw: HB => m [? [? Hzb]].
  subst; exists n, m, j, q''; split; first weq.
  by do 2!split => //; lenH Hk; lia.
- case=> n [m [j [q'' [-> [Hza [Hzb Hj]]]]]].
  eapply l_mul_intro'; first eapply l_mul_intro'; first eapply l_mul_intro'.
  + head_intro n m; last by gw_intro m.
    apply/l_gs; exists n; split; first reflexivity.
    by split; [instantiate (1 := n - j - fa q za); lia|].
  + by apply/l_wstar; exists j.
  + reflexivity.
  + reflexivity.
  + by apply/l_qall; exists q''.
  + reflexivity.
  + reflexivity.
  + exact/l_cst.
  + weq.
  + len.
Qed.

Lemma l_w_mb q za zb v :
  l (w_mb q za zb) (v, length v) ↔
  ∃ n m j q'' i,
    v = hash :: uword (n, q, m) ++ hash :: repeat la j ++ lq q'' ::
        repeat lb i ∧
    za = Nat.eqb n 0 ∧ zb = Nat.eqb m 0 ∧ i = m + mb q zb.
Proof.
rewrite /w_mb; split.
- case/l_mul_inv => v1 [k1 [v2 [k2 [? [Hk [H1 /l_cst [? ?]]]]]]].
  case/l_mul_inv: H1 => v6 [k6 [v7 [k7 [? [? [H6 /l_wstar [i [? ?]]]]]]]].
  case/l_mul_inv: H6 => v0 [k0 [v4 [k4 [? [? [H0 /l_qall [q'' [? ?]]]]]]]].
  case/l_mul_inv: H0 => v5 [k5 [v3 [k3 [? [? [H5 /l_wstar [j [? ?]]]]]]]].
  case/l_head: H5 => wA [kA [wB [kB [? [? [HA HB]]]]]].
  case/l_gw: HA => n [? [? Hza]]; case/l_gw: HB => m [? [? Hzb]].
  subst; exists n, m, j, q'', i; split; first weq.
  by do 2!split => //; lenH Hk; lia.
- case=> n [m [j [q'' [i [-> [Hza [Hzb Hi]]]]]]].
  eapply l_mul_intro'; first eapply l_mul_intro'; first eapply l_mul_intro';
    first eapply l_mul_intro'.
  + by head_intro n m; [gw_intro n|gw_intro m].
  + by apply/l_wstar; exists j.
  + reflexivity.
  + reflexivity.
  + by apply/l_qall; exists q''.
  + reflexivity.
  + reflexivity.
  + by apply/l_wstar; exists i.
  + reflexivity.
  + reflexivity.
  + exact/l_cst.
  + weq.
  + len.
Qed.

Lemma l_w_fb q za zb v :
  l (w_fb q za zb) (v, length v) ↔
  ∃ n m j q'' i,
    v = hash :: uword (n, q, m) ++ hash :: repeat la j ++ lq q'' ::
        repeat lb i ++ [hash] ∧
    za = Nat.eqb n 0 ∧ zb = Nat.eqb m 0 ∧ i + fb q zb ≤ m.
Proof.
rewrite /w_fb; split.
- case/l_mul_inv => v1 [k1 [v2 [k2 [? [Hk [H1 /l_cst [? ?]]]]]]].
  case/l_mul_inv: H1 => v8 [k8 [v9 [k9 [? [? [H8 /l_wl [? ?]]]]]]].
  case/l_mul_inv: H8 => v6 [k6 [v7 [k7 [? [? [H6 /l_wstar [i [? ?]]]]]]]].
  case/l_mul_inv: H6 => v0 [k0 [v4 [k4 [? [? [H0 /l_qall [q'' [? ?]]]]]]]].
  case/l_mul_inv: H0 => v5 [k5 [v3 [k3 [? [? [H5 /l_wstar [j [? ?]]]]]]]].
  case/l_head: H5 => wA [kA [wB [kB [? [? [HA HB]]]]]].
  case/l_gw: HA => n [? [? Hza]]; case/l_gs: HB => m [? [HkB Hzb]].
  subst; exists n, m, j, q'', i; split; first weq.
  by do 2!split => //; lenH Hk; lia.
- case=> n [m [j [q'' [i [-> [Hza [Hzb Hi]]]]]]].
  eapply l_mul_intro'; first eapply l_mul_intro'; first eapply l_mul_intro';
    first eapply l_mul_intro'; first eapply l_mul_intro'.
  + head_intro n m; first by gw_intro n.
    apply/l_gs; exists m; split; first reflexivity.
    by split; [instantiate (1 := m - i - fb q zb); lia|].
  + by apply/l_wstar; exists j.
  + reflexivity.
  + reflexivity.
  + by apply/l_qall; exists q''.
  + reflexivity.
  + reflexivity.
  + by apply/l_wstar; exists i.
  + reflexivity.
  + reflexivity.
  + exact/l_wl.
  + reflexivity.
  + reflexivity.
  + exact/l_cst.
  + weq.
  + len.
Qed.

(** ** Structure of run words *)

Lemma hash_not_in_uword c : hash ∉ uword c.
Proof.
case: c => [[n q] m] /=; rewrite elem_of_app elem_of_cons !elem_of_list_In.
case=> [H|[H|H]] //; by have := repeat_spec _ _ _ H.
Qed.

Lemma app_hash_split x y u v :
  hash ∉ x → x ++ hash :: y = u ++ hash :: v →
  (u = x ∧ v = y) ∨ (∃ u', u = x ++ hash :: u' ∧ y = u' ++ hash :: v).
Proof.
elim: x u => [|a x IH] [|b u] /= Hx.
- by case=> ->; left.
- by case=> <- ->; right; exists u.
- by case=> E _; case: Hx; rewrite E; apply: elem_of_list_here.
- case=> <-; move/not_elem_of_cons: Hx => [_ Hx] /(IH _ Hx).
  case=> [[-> ->]|[u' [-> ->]]]; [left|right] => //.
  by exists u'.
Qed.

Lemma rw_app cs1 cs2 : rw (cs1 ++ cs2) = rw cs1 ++ rw cs2.
Proof. by elim: cs1 => //= c cs1 ->; rewrite app_assoc. Qed.

Lemma run_snoc cs c : run (cs ++ [c]) = run cs ++ uword c ++ [hash].
Proof. by rewrite /run rw_app /= /cw app_nil_r. Qed.

Lemma run_ends cs : ∃ y, run cs = y ++ [hash].
Proof.
elim/rev_ind: cs => [|c cs [y Hy]]; first by exists [].
exists (run cs ++ uword c).
by rewrite /run rw_app /= /cw app_nil_r -!app_assoc.
Qed.

(* Splitting a run word at a separator. *)
Lemma run_split cs u v :
  run cs = u ++ hash :: v →
  ∃ cs1 cs2, cs = cs1 ++ cs2 ∧ v = rw cs2 ∧ run cs1 = u ++ [hash].
Proof.
rewrite /run; elim: cs u => [|c cs IH] u /=.
  case: u => [|? [|??]] /= [] //.
  by move=> <-; exists [], [].
case: u => [|t u] /= [].
  by move=> <-; exists [], (c :: cs).
move=> <-; rewrite /cw -app_assoc /=.
case/app_hash_split; first exact: hash_not_in_uword.
- by case=> -> ->; exists [c], cs; rewrite /= /cw app_nil_r.
- case=> u' [-> /(f_equal (cons hash)) /(IH (hash :: u'))].
  case=> cs1 [cs2 [-> [-> Hr]]].
  exists (c :: cs1), cs2; split => //; split => //.
  by rewrite /= /cw -app_assoc /= Hr; weq.
Qed.

Lemma repeat_app_inv (t : L) j n z z' :
  repeat t j ++ z = repeat t n ++ z' →
  (j ≤ n ∧ z = repeat t (n - j) ++ z') ∨ (n ≤ j ∧ z' = repeat t (j - n) ++ z).
Proof.
elim: j n => [|j IH] [|n] /=; try (by left; split => //; lia);
  try (by right; split => //; lia).
by case=> /IH [[? ?]|[? ?]]; [left|right]; split => //; lia.
Qed.

Lemma repeat_letter_inv (t : L) j n y y' z z' :
  y ≠ t → y' ≠ t →
  repeat t j ++ y :: z = repeat t n ++ y' :: z' → j = n ∧ y = y' ∧ z = z'.
Proof.
move=> Hy Hy'; elim: j n => [|j IH] [|n] /=.
- by case=> -> ->.
- by case=> E _; case: (Hy E).
- by case=> E _; case: (Hy' (eq_sym E)).
- by case=> /IH [-> [-> ->]].
Qed.

Lemma repeat_prefix_inv (t : L) j n z y' z' :
  y' ≠ t → repeat t j ++ z = repeat t n ++ y' :: z' → j ≤ n.
Proof.
move=> Hy'; elim: j n => [|j IH] [|n] /=; try lia.
- by case=> E _; case: (Hy' (eq_sym E)).
- by case=> /IH; lia.
Qed.

Lemma uword_inv c c' y y' :
  uword c ++ hash :: y = uword c' ++ hash :: y' → c = c' ∧ y = y'.
Proof.
case: c c' => [[n q] m] [[n' q'] m'] /=; rewrite -!app_assoc /=.
case/repeat_letter_inv => // - -> [[->]].
by case/repeat_letter_inv => // -> [_ ->].
Qed.

Lemma run_parse cs u c z :
  run cs = u ++ hash :: uword c ++ hash :: z →
  ∃ cs1 cs2, cs = cs1 ++ c :: cs2 ∧ z = rw cs2.
Proof.
case/run_split => cs1 [cs2 [-> [+ _]]].
case: cs2 => [|c' cs2] /=.
- by move=> /(f_equal length); rewrite length_app /=; lia.
- rewrite /cw -app_assoc /= => /uword_inv [<- ->].
  by exists cs1, cs2.
Qed.

Lemma uchain_tail c cs : uchain (c :: cs) → uchain cs.
Proof. by case: cs => //= c' cs [_ []]. Qed.

Lemma uchain_app_inv cs1 cs2 : uchain (cs1 ++ cs2) → uchain cs2.
Proof. by elim: cs1 => //= c cs1 IH /uchain_tail. Qed.

Lemma uchain_step cs1 c c' cs2 :
  uchain (cs1 ++ c :: c' :: cs2) → c.1.2 ∈ acts ∧ c' = ustep c.
Proof. by move=> /uchain_app_inv /= [? [? _]]. Qed.

(** Adjacent letters of a run word. *)

Fixpoint nobad (w : list L) : Prop :=
  match w with
  | x :: ((y :: _) as w') => bad x y = false ∧ nobad w'
  | _ => True
  end.

Lemma nobad_app u x v : nobad (u ++ [x]) → nobad (x :: v) → nobad (u ++ x :: v).
Proof.
elim: u => //= a [|b u] IH /=; first by case=> ? _ ?.
by case=> ? /IH H /H.
Qed.

Lemma nobad_spec u x y z : nobad (u ++ x :: y :: z) → bad x y = false.
Proof.
elim: u => [|a u IH] /=; first by case.
by case: u IH => [|b u] IH /= [_ H]; exact: IH H.
Qed.

Lemma nobad_repeat (x t y : L) n :
  bad x t = false → bad t t = false → bad t y = false → bad x y = false →
  nobad (x :: repeat t n ++ [y]).
Proof.
move=> Hxt Htt Hty Hxy; elim: n x Hxt Hxy => [|n IH] x Hxt Hxy /=.
- by split.
- by split => //; apply: IH.
Qed.

Lemma nobad_run cs : nobad (run cs).
Proof.
elim: cs => [|[[n q] m] cs IH]; first by [].
have -> : run ((n, q, m) :: cs) =
          (hash :: repeat la n) ++ lq q :: (repeat lb m ++ hash :: rw cs).
{ by rewrite /run /= /cw -!app_assoc. }
apply: nobad_app; first by apply: nobad_repeat.
rewrite app_comm_cons; apply: nobad_app => //.
by apply: nobad_repeat.
Qed.

(** ** Membership in the detectors *)

Lemma l_join_list {I} (f : I → term) xs y :
  l (join_list f xs) y ↔ ∃ x, x ∈ xs ∧ l (f x) y.
Proof. by rewrite semi_lattice_morphism_join_list elem_of_lang_join_list. Qed.

Lemma l_bal_eq w' v k : l (bal w') (v, k) ↔ v = w' ∧ k = length w'.
Proof. by rewrite l_unit_eq; split => [[-> ->]|[-> ->]]. Qed.

Lemma l_pad (X : term) w :
  l (bstar ⋅ X) (w, length w) ↔ ∃ u v, w = u ++ v ∧ l X (v, length v).
Proof.
split.
- case/l_mul_inv => u [ku [v [kv [-> [Hk [/l_bal_star /= Hu Hv]]]]]].
  exists u, v; split => //.
  by have -> : length v = kv by rewrite length_app in Hk; lia.
- case=> u [v [-> Hv]]; rewrite length_app; apply: l_mul_intro => //.
  exact/l_bal_star.
Qed.

Lemma l_e_win y :
  l e_win y ↔ ∃ q za zb, q ∈ acts ∧ l (w_all q za zb) y.
Proof.
split.
- case/l_join_list => q [Hq /l_join_list [za [_ /l_join_list [zb [_ H]]]]].
  by exists q, za, zb.
- case=> q [za [zb [Hq H]]]; apply/l_join_list; exists q; split => //.
  apply/l_join_list; exists za; split; first by clear H; case: za; set_solver.
  apply/l_join_list; exists zb; split; first by clear H; case: zb; set_solver.
  done.
Qed.

Lemma l_e_shape v k :
  l e_shape (v, k) ↔ ∃ x y, v = [x; y] ∧ k = 2 ∧ bad x y = true.
Proof.
split.
- case/l_join_list => x [_ /l_join_list [y [_]]].
  case E: (bad x y); last by case.
  by case/l_bal_eq => -> ->; exists x, y.
- case=> x [y [-> [-> E]]]; apply/l_join_list; exists x.
  split; first exact: elem_of_enum.
  apply/l_join_list; exists y; split; first exact: elem_of_enum.
  by rewrite E; apply/l_bal_eq.
Qed.

Lemma l_init_errs_inv pre w v k :
  l (init_errs pre w) (v, k) →
  ∃ p t0 r t, w = p ++ t0 :: r ∧ t ≠ t0 ∧ v = pre ++ p ++ [t].
Proof.
elim: w pre => [|t0 w IH] pre; cbn [init_errs]; first by case.
case/l_join.
- case/l_join_list => t [_]; case: bool_decide_reflect => Ht; first by case.
  by case/l_bal_eq => -> _; exists [], t0, w, t.
- case/IH => p [t0' [r [t [-> [Ht ->]]]]].
  by exists (t0 :: p), t0', r, t; rewrite -app_assoc.
Qed.

Lemma l_init_errs_intro pre p t0 r t :
  t ≠ t0 →
  l (init_errs pre (p ++ t0 :: r)) (pre ++ p ++ [t], length (pre ++ p ++ [t])).
Proof.
move=> Ht; elim: p pre => [|a p IH] pre; cbn [init_errs app].
- apply/l_join; left; apply/l_join_list; exists t.
  split; first exact: elem_of_enum.
  by case: bool_decide_reflect => // _; apply/l_bal_eq.
- apply/l_join; right.
  by move: (IH (pre ++ [a])); rewrite -app_assoc.
Qed.

(** ** Soundness: a run word matches no detector *)

Lemma next_conf cs u n q m tl z :
  uchain cs → q ∈ acts → tl ≠ [] →
  run cs = u ++ (hash :: uword (n, q, m) ++ hash :: tl) ++ z →
  ∃ r, tl ++ z = uword (ustep (n, q, m)) ++ hash :: r.
Proof.
move=> Hc Hq Htl Hrun.
have : run cs = u ++ hash :: uword (n, q, m) ++ hash :: (tl ++ z).
{ rewrite Hrun; weq. }
case/run_parse => cs1 [[|c' cs2] [Ecs Ez]].
- by case: tl {Hrun} Htl Ez.
- move: Hc; rewrite Ecs => /uchain_step [_ <-].
  by exists (rw cs2); rewrite Ez /= /cw -app_assoc.
Qed.

Lemma win_sound cs u v z q za zb :
  uchain cs → q ∈ acts → run cs = u ++ v ++ z →
  l (w_all q za zb) (v, length v) → False.
Proof.
move=> Hc Hq Hrun.
have Hnext : ∀ n m tl, v = hash :: uword (n, q, m) ++ hash :: tl → tl ≠ [] →
    let '(n', q', m') := ustep (n, q, m) in
    ∃ r, tl ++ z = repeat la n' ++ lq q' :: repeat lb m' ++ hash :: r.
{ move=> n m tl Ev Htl; rewrite Ev in Hrun.
  case: (next_conf Hc Hq Htl Hrun) => r.
  case: (ustep (n, q, m)) => [[n' q'] m'] /= ->.
  by exists r; rewrite -app_assoc. }
case/l_join => [/l_join [/l_join [/l_join [H|H]|H]|H]|H].
- case/l_w_ctrl: H => n [m [j [q'' [Ev [? [? Hne]]]]]].
  subst za zb.
  move: (Hnext n m _ Ev ltac:(by destruct j)) (ustep_arith n q m).
  case: (ustep (n, q, m)) => [[n' q'] m'] [r] /= Hr [Hq' _].
  rewrite -app_assoc /= in Hr.
  by case/repeat_letter_inv: Hr => // _ [[E] _]; apply: Hne; rewrite E Hq'.
- case/l_w_ma: H => n [m [j [Ev [? [? Hj]]]]].
  subst za zb.
  have Hne : repeat la j ≠ [].
  { rewrite Hj; case: (n) => [|?] //=; rewrite /ma; by case: (prog q). }
  move: (Hnext n m _ Ev Hne).
  move: (ustep_arith n q m).
  case: (ustep (n, q, m)) => [[n' q'] m'] [_ [A1 _]] [r] /repeat_prefix_inv.
  by move=> /(_ ltac:(done)); lia.
- case/l_w_fa: H => n [m [j [q'' [Ev [? [? Hj]]]]]].
  subst za zb.
  move: (Hnext n m _ Ev ltac:(by destruct j)) (ustep_arith n q m).
  case: (ustep (n, q, m)) => [[n' q'] m'] [r] /= Hr [_ [_ [A2 _]]].
  rewrite -app_assoc /= in Hr.
  by case/repeat_letter_inv: Hr => // E _; lia.
- case/l_w_mb: H => n [m [j [q'' [i [Ev [? [? Hi]]]]]]].
  subst za zb.
  move: (Hnext n m _ Ev ltac:(by destruct j)) (ustep_arith n q m).
  case: (ustep (n, q, m)) => [[n' q'] m'] [r] /= Hr [_ [_ [_ [A3 _]]]].
  rewrite -app_assoc /= in Hr.
  case/repeat_letter_inv: Hr => // _ [_] /repeat_prefix_inv.
  by move=> /(_ ltac:(done)); lia.
- case/l_w_fb: H => n [m [j [q'' [i [Ev [? [? Hi]]]]]]].
  subst za zb.
  move: (Hnext n m _ Ev ltac:(by destruct j)) (ustep_arith n q m).
  case: (ustep (n, q, m)) => [[n' q'] m'] [r] /= Hr [_ [_ [_ [_ A4]]]].
  rewrite -!app_assoc /= in Hr.
  case/repeat_letter_inv: Hr => // _ [_].
  rewrite -app_assoc /= => /repeat_letter_inv.
  by case=> // E _; lia.
Qed.

Lemma run_cons c cs : run (c :: cs) = run [c] ++ rw cs.
Proof. by rewrite /run /= app_nil_r. Qed.

Lemma rw_nil cs : rw cs = [] → cs = [].
Proof. by case: cs => //= c cs; rewrite /cw -app_assoc; case: (uword c). Qed.

Lemma univ_sound_lang c0 cs cs' cl :
  q0 ∉ acts → uchain (c0 :: cs) → c0 :: cs = cs' ++ [cl] → cl.1.2 ∉ acts →
  l (univ_ub c0) (run (c0 :: cs), length (run (c0 :: cs))) →
  cl = (0, q0, 0).
Proof.
move=> Hq0 Hc Ecs Hcl.
have Hend : ∀ c cs1 cs2, c0 :: cs = cs1 ++ c :: cs2 →
    cs2 = [] ∧ cl = c ∨ c.1.2 ∈ acts.
{ move=> c cs1 [|c' cs2] E.
  - left; split => //; move: E; rewrite Ecs.
    by move=> E'; case: (app_inj_tail _ _ _ _ E').
  - by right; move: Hc; rewrite E => /uchain_step []. }
case/l_join => [He|Hp].
- exfalso; case/l_join: He => [/l_join [/l_join [H|H]|H]|H].
  + by case/l_one: H.
  + case/l_bal_eq: H => E _; move: E; rewrite /run => - [] E.
    by have := rw_nil (cs := c0 :: cs) E.
  + case/l_pad: H => u [v [Ew /l_join_list [t [_]]]].
    rewrite /compose; case: bool_decide_reflect => Ht; first by case.
    case/l_bal_eq => Ev _; case: (run_ends (c0 :: cs)) => y Ey.
    move: Ey; rewrite Ew Ev => E'.
    by case: (app_inj_tail _ _ _ _ E') => _ /Ht.
  + case/l_pad: H => u [v [Ew /l_join_list [q [Hq]]]].
    case/l_head => wA [kA [wB [kB [Ev [_ [/l_wstar [n [Ea _]]]]]]]].
    case/l_wstar => m [Eb _]; subst.
    have : run (c0 :: cs) = u ++ hash :: uword (n, q, m) ++ hash :: [].
    { rewrite Ew; weq. }
    case/run_parse => cs1 [cs2 [E Ez]].
    have Ecs2 := rw_nil (eq_sym Ez); subst cs2.
    move: Ecs; rewrite E => E'; case: (app_inj_tail _ _ _ _ E') => _ Ecl.
    by apply: Hcl; rewrite -Ecl.
- case/l_mul_inv: Hp => w1 [k1 [w2 [k2 [Ew [Hk [H1 /l_bal_star /= Hk2]]]]]].
  have {Hk Hk2} Hk1 : k1 = length w1 by rewrite Ew length_app in Hk; lia.
  subst k1; case/l_join: H1 => [H|H].
  + case/l_init_errs_inv: H => p [t0 [r [t [Ei [Ht Ew1]]]]].
    move: Ew; rewrite run_cons Ei Ew1 /= -!app_assoc /=.
    by move=> /app_inv_head [] E _; case: (Ht (eq_sym E)).
  + case/l_pad: H => u [v [Ew1 H]]; subst w1.
    case/l_join: H => [/l_join [H|H]|H].
    * case/l_bal_eq: H => Ev _; subst v.
      have : run (c0 :: cs) = u ++ hash :: uword (0, q0, 0) ++ hash :: w2.
      { rewrite Ew; weq. }
      case/run_parse => cs1 [cs2 [E _]].
      by case: (Hend _ _ _ E) => [[_ ->]|].
    * case/l_e_shape: H => x [y [Ev [_ Hb]]]; subst v.
      have E : run (c0 :: cs) = u ++ x :: y :: w2 by rewrite Ew -app_assoc.
      have := nobad_spec (u := u) (x := x) (y := y) (z := w2).
      by rewrite Hb -E => /(_ (nobad_run _)).
    * case/l_e_win: H => q [za [zb [Hq H]]].
      by case: (win_sound Hc Hq (u := u) (z := w2) ltac:(rewrite Ew; weq) H).
Qed.

Theorem univ_sound_gen c0 cs cs' cl :
  q0 ∉ acts → uchain (c0 :: cs) → c0 :: cs = cs' ++ [cl] → cl.1.2 ∉ acts →
  bstar ⊑ univ_ub c0 → cl = (0, q0, 0).
Proof.
move=> Hq0 Hc Ecs Hcl /(bal_univ_sound (run (c0 :: cs))).
exact: univ_sound_lang.
Qed.

(** ** Completeness: every deviation is caught where it happens *)

Definition caught (w : list L) : Prop :=
  ∃ u v, w = u ++ v ∧ l (e_halt0 ⊔ e_shape ⊔ e_win) (v, length v).

Lemma caught_pre c0 w : caught w → l (e_pre c0) (w, length w).
Proof.
by case=> u [v [-> H]]; apply/l_join; right; apply/l_pad; exists u, v.
Qed.

Lemma caught_bigram p x t :
  (∃ u, p = u ++ [x]) → bad x t = true → caught (p ++ [t]).
Proof.
case=> u -> Hb; exists u, [x; t]; split; first by rewrite -app_assoc.
by apply/l_join; left; apply/l_join; right; apply/l_e_shape; exists x, t.
Qed.

Lemma caught_win u v q za zb :
  q ∈ acts → l (w_all q za zb) (v, length v) → caught (u ++ v).
Proof.
move=> Hq H; exists u, v; split => //.
by apply/l_join; right; apply/l_e_win; exists q, za, zb.
Qed.

Lemma snoc_repeat (u : list L) (x t : L) k :
  ∃ u', u ++ x :: repeat t k = u' ++ [match k with 0 => x | S _ => t end].
Proof.
case: k => [|k]; first by exists u.
exists (u ++ x :: repeat t k); rewrite -app_assoc /=.
by rewrite -repeat_cons.
Qed.

Lemma prefix_split (t : L) n y z x t0 r :
  x ++ t0 :: r = repeat t n ++ y :: z →
  (∃ k, k < n ∧ x = repeat t k ∧ t0 = t) ∨ (x = repeat t n ∧ t0 = y) ∨
  (∃ x', x = repeat t n ++ y :: x' ∧ x' ++ t0 :: r = z).
Proof.
elim: n x => [|n IH] [|a x] /=.
- by case=> -> _; right; left.
- by case=> -> E; right; right; exists x.
- by case=> -> _; left; exists 0; split => //; lia.
- case=> -> /IH [[k [? [-> ->]]]|[[-> ->]|[x' [-> E]]]].
  + by left; exists (S k); split => //; lia.
  + by right; left.
  + by right; right; exists x'.
Qed.

Lemma win_detect n q m u x t0 r t :
  q ∈ acts → x ++ t0 :: r = cw (ustep (n, q, m)) → t ≠ t0 →
  caught (u ++ hash :: uword (n, q, m) ++ hash :: x ++ [t]).
Proof.
move=> Hq; move: (ustep_arith n q m).
case: (ustep (n, q, m)) => [[n' q'] m'] [Hq' [A1 [A2 [A3 A4]]]].
rewrite /cw /= -app_assoc /= => Hx Ht.
have Hwin : ∀ tl,
    l (w_all q (n =? 0) (m =? 0)) (hash :: uword (n, q, m) ++ hash :: tl,
                       length (hash :: uword (n, q, m) ++ hash :: tl)) →
    x ++ [t] = tl →
    caught (u ++ hash :: uword (n, q, m) ++ hash :: x ++ [t]).
{ move=> tl HX ->; exists u, (hash :: uword (n, q, m) ++ hash :: tl).
  split => //; apply/l_join; right; apply/l_e_win.
  by exists q, (n =? 0), (m =? 0). }
set P := u ++ hash :: uword (n, q, m).
have EP : u ++ hash :: uword (n, q, m) ++ hash :: x ++ [t] =
          (P ++ hash :: x) ++ [t] by rewrite /P; weq.
case/prefix_split: Hx => [[k [Hk [? E0]]]|[[? E0]|[x' [? Hx']]]]; subst x.
- (* inside the `a` block *)
  subst t0; destruct t as [[| |q'']|]; try by exfalso; apply: Ht.
  + rewrite EP; apply: caught_bigram; first exact: snoc_repeat.
    by case: (k).
  + apply: (Hwin (repeat la k ++ [lq q''])); last done.
    do 2 (apply/l_join; left); apply/l_join; right.
    apply/l_w_fa; exists n, m, k, q''; do !split => //; lia.
  + rewrite EP; apply: caught_bigram; first exact: snoc_repeat.
    by case: (k).
- (* at the state *)
  subst t0; destruct t as [[| |q'']|].
  + apply: (Hwin (repeat la (S n'))).
    * do 3 (apply/l_join; left); apply/l_join; right.
      apply/l_w_ma; exists n, m, (S n'); do !split => //; lia.
    * by rewrite -repeat_cons.
  + rewrite EP; apply: caught_bigram; first exact: snoc_repeat.
    by case: (n').
  + apply: (Hwin (repeat la n' ++ [lq q''])); last done.
    do 4 (apply/l_join; left).
    apply/l_w_ctrl; exists n, m, n', q''; do !split => //.
    by move=> E; apply: Ht; rewrite E Hq'.
  + rewrite EP; apply: caught_bigram; first exact: snoc_repeat.
    by case: (n').
- (* inside the `b` block *)
  have EP' :
    u ++ hash :: uword (n, q, m) ++ hash :: (repeat la n' ++ lq q' :: x') ++ [t]
           = ((P ++ hash :: repeat la n') ++ lq q' :: x') ++ [t].
  { rewrite /P; weq. }
  case/prefix_split: Hx' => [[k [Hk [? E0]]]|[[? E0]|[x'' [_ Hn]]]];
    last by case: x'' Hn.
  all: subst x' t0; destruct t as [[| |q'']|]; try by exfalso; apply: Ht.
  + rewrite EP'; apply: caught_bigram; first exact: snoc_repeat.
    by case: (k).
  + rewrite EP'; apply: caught_bigram; first exact: snoc_repeat.
    by case: (k).
  + apply: (Hwin (repeat la n' ++ lq q' :: repeat lb k ++ [hash])).
    * apply/l_join; right.
      apply/l_w_fb; exists n, m, n', q', k; do !split => //; lia.
    * by rewrite -!app_assoc.
  + rewrite EP'; apply: caught_bigram; first exact: snoc_repeat.
    by case: (m').
  + apply: (Hwin (repeat la n' ++ lq q' :: repeat lb (S m'))).
    * apply/l_join; left; apply/l_join; right.
      apply/l_w_mb; exists n, m, n', q', (S m'); do !split => //; lia.
    * by rewrite -app_assoc /= -repeat_cons.
  + rewrite EP'; apply: caught_bigram; first exact: snoc_repeat.
    by case: (m').
Qed.

Lemma detect_from c cs u x t0 r t :
  uchain (c :: cs) → rw cs = x ++ t0 :: r → t ≠ t0 →
  caught (u ++ hash :: uword c ++ hash :: x ++ [t]).
Proof.
elim: cs c u x => [|c' cs IH] c u x Hc E Ht.
  by case: x E.
case: Hc => Hq [Ec' Hc'].
have Hrec : ∀ y, x = cw c' ++ y → rw cs = y ++ t0 :: r →
    caught (u ++ hash :: uword c ++ hash :: x ++ [t]).
{ move=> y -> Ek; move: (IH c' (u ++ hash :: uword c) y Hc' Ek Ht).
  by rewrite /cw; congr caught; weq. }
case: (app_eq_app _ _ _ _ E) => - [|y0 y] [[E1 E2]|[E1 E2]].
- apply: (Hrec []); first by rewrite E1 !app_nil_r.
  by rewrite E2.
- exact: Hrec E1 E2.
- move: E2 => [] Ey0 _; subst y0.
  clear Hrec; case: c Hq Ec' => [[n q] m] Hq Ec'; simpl in Hq.
  by apply: (win_detect u Hq _ Ht); rewrite -Ec' E1.
- exact: Hrec E1 E2.
Qed.

Lemma detect c0 cs p t0 r t :
  uchain (c0 :: cs) → run (c0 :: cs) = p ++ t0 :: r → t ≠ t0 →
  l (e_pre c0) (p ++ [t], length (p ++ [t])).
Proof.
rewrite run_cons => Hc E Ht.
have Hrest : ∀ y, p = run [c0] ++ y → rw cs = y ++ t0 :: r →
    l (e_pre c0) (p ++ [t], length (p ++ [t])).
{ move=> y -> Ek; apply: caught_pre.
  move: (detect_from [] Hc Ek Ht); rewrite /run /=.
  by congr caught; rewrite /cw; weq. }
case: (app_eq_app _ _ _ _ E) => - [|y0 y] [[E1 E2]|[E1 E2]].
- apply: (Hrest []); first by rewrite E1 !app_nil_r.
  by rewrite E2.
- exact: Hrest E1 E2.
- move: E2 => [] Ey0 _; subst y0.
  apply/l_join; left; rewrite E1.
  exact: (l_init_errs_intro [] p y Ht).
- exact: Hrest E1 E2.
Qed.

Lemma prefix_end c0 cs p t0 r :
  uchain (c0 :: cs) → run (c0 :: cs) = p ++ t0 :: r → l e_end (p, length p).
Proof.
move=> Hc; elim/rev_ind: p => [|x p _] E.
  by do 3 (apply/l_join; left); apply/l_one.
case: (decide (x = hash)) => [Ex|Hx].
- subst x; rewrite -app_assoc /= in E.
  case/run_split: E => cs1 [cs2 [Ecs [Er Ep]]].
  elim/rev_ind: cs1 Ecs Ep => [|c cs1 _] Ecs Ep.
    rewrite /run /= in Ep.
    have -> : p = [] by case: p Ep => [|? [|??]] //= [].
    apply/l_join; left; apply/l_join; left; apply/l_join; right.
    exact/l_bal_eq.
  case: (run_ends cs1) => y Ey.
  rewrite run_snoc Ey in Ep.
  have {}Ep : p = y ++ hash :: uword c.
  { have E' : (y ++ hash :: uword c) ++ [hash] = p ++ [hash]
      by rewrite -Ep; weq.
    by case: (app_inj_tail _ _ _ _ E'). }
  case: cs2 Ecs Er => [|c' cs2] Ecs; first by [].
  move=> _; rewrite Ecs -app_assoc /= in Hc; case/uchain_step: Hc => Hq _.
  apply/l_join; right; rewrite Ep.
  have -> : (y ++ hash :: uword c) ++ [hash] = y ++ hash :: uword c ++ [hash]
    by rewrite -app_assoc.
  apply/l_pad; exists y, (hash :: uword c ++ [hash]); split => //.
  apply/l_join_list; exists c.1.2; split => //.
  destruct c as [[n q] m]; simpl in Hq; apply/l_head.
  exists (repeat la n), n, (repeat lb m), m; split; first weq.
  split; first len.
  by split; [apply/l_wstar; exists n|apply/l_wstar; exists m]; split => //; lia.
- apply/l_join; left; apply/l_join; right.
  apply/l_pad; exists p, [x]; split => //.
  apply/l_join_list; exists x; split; first exact: elem_of_enum.
  by rewrite /compose; case_bool_decide => //; apply/l_bal_eq.
Qed.

Lemma first_diff (w w0 : list L) :
  (∃ r, w0 = w ++ r) ∨ (∃ r, w = w0 ++ r) ∨
  (∃ p t t0 r r0, w = p ++ t :: r ∧ w0 = p ++ t0 :: r0 ∧ t ≠ t0).
Proof.
elim: w w0 => [|t w IH] [|t0 w0].
- by left; exists [].
- by left; exists (t0 :: w0).
- by right; left; exists (t :: w).
- case: (decide (t = t0)) => [<-|Ht].
  + case: (IH w0) => [[r ->]|[[r ->]|[p [a [a0 [r [r0 [-> [-> Ha]]]]]]]]].
    * by left; exists r.
    * by right; left; exists r.
    * by right; right; exists (t :: p), a, a0, r, r0.
  + by right; right; exists [], t, t0, w, w0.
Qed.

(* The language-level facts KA/balanced.v's bal_univ_complete consumes,
   with D = |run word| + 1; also used by KA/BalancedBinary.v. *)
Lemma univ_complete_lang c0 cs cs' :
  uchain (c0 :: cs) → c0 :: cs = cs' ++ [(0, q0, 0)] →
  let D := S (length (run (c0 :: cs))) in
  (∀ w, length w < D → l (univ_ub c0) (w, length w)) ∧
  (∀ w, length w = D → ∃ w1 w2, w = w1 ++ w2 ∧ l (e_pre c0) (w1, length w1)).
Proof.
move=> Hc Ecs; set w0 := run (c0 :: cs).
have Hw0 : l (e_pre c0) (w0, length w0).
{ case: (run_ends cs') => y Ey.
  have -> : w0 = y ++ [hash; lq q0; hash].
  { by rewrite /w0 Ecs run_snoc Ey; weq. }
  apply: caught_pre; exists y, [hash; lq q0; hash]; split => //.
  by apply/l_join; left; apply/l_join; left; apply/l_bal_eq. }
have Htail : ∀ w1 w2, l (e_pre c0) (w1, length w1) →
    l (univ_ub c0) (w1 ++ w2, length (w1 ++ w2)).
{ move=> w1 w2 H; apply/l_join; right; rewrite length_app.
  by apply: l_mul_intro => //; apply/l_bal_star. }
split.
- move=> w Hw; case: (first_diff w w0) =>
    [[[|t0 r] Er]|[[r Er]|[p [t [t0 [r [r0 [-> [Er Ht]]]]]]]]].
  + have -> : w = w0 by rewrite Er app_nil_r.
    by move: (Htail w0 [] Hw0); rewrite app_nil_r.
  + by apply/l_join; left; apply: (prefix_end Hc Er).
  + have Er0 : r = [].
    { by move: Hw; rewrite Er length_app; case: r {Er}; [|simpl; lia]. }
    have -> : w = w0 by rewrite Er Er0 app_nil_r.
    by move: (Htail w0 [] Hw0); rewrite app_nil_r.
  + have -> : p ++ t :: r = (p ++ [t]) ++ r by rewrite -app_assoc.
    exact: Htail (detect Hc Er Ht).
- move=> w Hw; case: (first_diff w w0) =>
    [[r Er]|[[r ->]|[p [t [t0 [r [r0 [-> [Er Ht]]]]]]]]].
  + by move: Hw; rewrite Er length_app; lia.
  + by exists w0, r.
  + by exists (p ++ [t]), r; split; [rewrite -app_assoc|exact: detect Hc Er Ht].
Qed.

Theorem univ_complete_gen c0 cs cs' :
  uchain (c0 :: cs) → c0 :: cs = cs' ++ [(0, q0, 0)] → bstar ⊑ univ_ub c0.
Proof.
move=> Hc Ecs; case: (univ_complete_lang Hc Ecs) => Hshort Hlong.
apply: (bal_univ_complete (Pre := e_pre c0)
          (D := S (length (run (c0 :: cs))))).
- exact: sqsubseteq_join_right.
- exact: Hshort.
- exact: Hlong.
Qed.

End UnivGeneric.

(** * Instantiation with MM2 programs *)

Section MM2Univ.

Variable P : list mm2_instr.
Notation Q := (fin (S (S (length P)))).

Notation prog := (@mm2_prog P).
Notation nxt := (@next_state P).
Notation acts := (active_states P).

Definition uconf_of (s : mm2_state) : @uconf Q :=
  (s.2.1, translate_state P s.1, s.2.2).

Lemma step_uconf s s' :
  mm2_step P s s' →
  (uconf_of s).1.2 ∈ acts ∧ uconf_of s' = ustep prog nxt (uconf_of s).
Proof.
move/mm2_step_fun_spec; rewrite /mm2_step_fun.
case: s => [[|pc] [a b]] //=.
case Hnth: (nth_error P pc) => [ρ|] //= [<-].
have Hpc : pc < length P by apply/nth_error_Some; congruence.
split; first exact: (@translate_state_active P (S pc) ltac:(lia)).
rewrite /uconf_of /ustep /= (mm2_prog_spec Hnth).
have Hnext :
  next_state (translate_state P (S pc)) = translate_state P (S (S pc)).
{ by rewrite /next_state translate_state_spec. }
by case: ρ {Hnth} => [||j|j] /=; rewrite ?Hnext //; [case: a|case: b].
Qed.

Lemma rtc_uchain s1 s2 :
  rtc (mm2_step P) s1 s2 →
  ∃ cs cs', uchain prog nxt acts (uconf_of s1 :: cs) ∧
    uconf_of s1 :: cs = cs' ++ [uconf_of s2].
Proof.
elim=> [s|s s' s'' Hs _ [cs [cs' [Hc E]]]]; first by exists [], [].
exists (uconf_of s' :: cs), (uconf_of s :: cs'); split; last by rewrite E.
by case: (step_uconf Hs) => ? ?; split.
Qed.

Lemma F1_not_active : (Fin.F1 : Q) ∉ acts.
Proof. by case/elem_of_active_state. Qed.

Lemma stop_not_active s : mm2_stop P s → (uconf_of s).1.2 ∉ acts.
Proof.
move/MM2_facts.mm2_stop_index_iff; rewrite /uconf_of /=.
case: s => [[|i] [a b]] /= Hs; first exact: F1_not_active.
rewrite nat_to_fin_ge; first lia.
by case/elem_of_active_state => q /Fin.FS_inj.
Qed.

Lemma uconf_of_halt0 s : uconf_of s = (0, Fin.F1, 0) → s = (0, (0, 0)).
Proof. by case: s => [[|i] [a b]] //= [-> ->]. Qed.

Definition univ_ub_mm2 (s1 : mm2_state) :=
  univ_ub prog nxt acts Fin.F1 (uconf_of s1).

Theorem univ_completeness s1 :
  rtc (mm2_step P) s1 (0, (0, 0)) →
  bal_star (A := option_setoid (@mm_sym_setoid Q)) ⊑ univ_ub_mm2 s1.
Proof.
case/rtc_uchain => cs [cs' [Hc E]].
exact: (univ_complete_gen Hc E).
Qed.

Theorem univ_soundness s1 s2 :
  rtc (mm2_step P) s1 s2 → mm2_stop P s2 →
  bal_star (A := option_setoid (@mm_sym_setoid Q)) ⊑ univ_ub_mm2 s1 →
  s2 = (0, (0, 0)).
Proof.
case/rtc_uchain => cs [cs' [Hc E]] Hstop Hle.
apply: uconf_of_halt0.
exact: (univ_sound_gen F1_not_active Hc E (stop_not_active Hstop) Hle).
Qed.

(** ** Over the binary alphabet *)

Notation TL := (option_setoid (@mm_sym_setoid Q)).

Definition encL : TL → list bool := enc_onehot TL.
Definition kL : nat := length (enum TL).

Lemma kL_pos : 0 < kL.
Proof.
rewrite /kL; case E: (enum TL) => [|? ?]; last by simpl; lia.
have H : (None : TL) ∈ enum TL by apply: elem_of_enum.
by rewrite E in H; case: (not_elem_of_nil _ H).
Qed.

Definition univ_ub_bin (s1 : mm2_state) :=
  bin_ub encL kL (e_end acts) (e_pre prog nxt acts Fin.F1 (uconf_of s1)).

Theorem univ_completeness_bin s1 :
  rtc (mm2_step P) s1 (0, (0, 0)) →
  bal_star (A := bool_setoid) ⊑ univ_ub_bin s1.
Proof.
case/rtc_uchain => cs [cs' [Hc E]].
case: (univ_complete_lang Hc E) => Hshort Hlong.
apply: (bin_complete (E := e_end acts)
          (P := e_pre prog nxt acts Fin.F1 (uconf_of s1))
          (D := S (length (run (uconf_of s1 :: cs))))
          (enc_onehot_length TL) kL_pos).
- exact: Hshort.
- exact: Hlong.
Qed.

Theorem univ_soundness_bin s1 s2 :
  rtc (mm2_step P) s1 s2 → mm2_stop P s2 →
  bal_star (A := bool_setoid) ⊑ univ_ub_bin s1 →
  s2 = (0, (0, 0)).
Proof.
case/rtc_uchain => cs [cs' [Hc E]] Hstop Hle.
have Hl := bin_sound (enc_onehot_inj' TL) (enc_onehot_length TL) kL_pos Hle.
apply: uconf_of_halt0.
refine (univ_sound_lang F1_not_active Hc E (stop_not_active Hstop) _).
exact: (Hl _ (run (uconf_of s1 :: cs))).
Qed.

End MM2Univ.

(* As for CKAUndec/Encoding.v's red_leq: extract the elaborated inequality
   from univ_completeness's type. *)
Definition univ_leq (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@univ_completeness P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target_univ (c y : nat) : Prop :=
  univ_leq (progOf c) (1, (y, 0)).

Definition univ_leq_bin (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@univ_completeness_bin P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target_univ_bin (c y : nat) : Prop :=
  univ_leq_bin (progOf c) (1, (y, 0)).
