(* Two-counter (MM2) machines as two-ended Post normal systems
   (RegexUnif/Invariant.v's `dstep`), in place of the deterministic tag
   system of the source sketch.

   A configuration `(i, (n, m))` is the word `cword` = `q_i aⁿ bᵐ #` over
   `option (mm_sym Q)`, with `None` the end marker `#` and `q_i` the
   letter of CKAUndec/Encoding.v's `translate_state` (pc 0, every pc
   beyond the program, and each pc in between get distinct letters).
   Each instruction becomes at most three rules (`rules_of`), reading
   the state letter and at most one more letter at the front, or the
   end marker and at most one more letter at the back; the end marker
   turns every zero test into a positive pattern. On encoded words the
   rules simulate MM2 step for step (`cword_step`, `cword_step_inv`).

   Halting anywhere but `(0, (0, 0))` shows as a prefix in `mm2_bad`:
   `q_out` (any pc past the program), `q₀ a` or `q₀ b` (`cword_bad`).
   The accepting word `q₀ #` (`cword_accept_ok`) and the words of
   running configurations (`cword_active_ok`) have none. `run_path`
   collects the configurations of a halting run, a finite set closed
   under steps by determinism. Nothing here is about KA. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list finite fin relations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts.
From kacc Require Import KA.algebra CKAUndec.Encoding RegexUnif.Invariant.

Local Open Scope nat_scope.

Lemma repeat_snoc {X} (z : X) k : repeat z (S k) = repeat z k ++ [z].
Proof. by elim: k => //= k ->. Qed.

Lemma snoc_inj {X} (l1 l2 : list X) (z1 z2 : X) :
  l1 ++ [z1] = l2 ++ [z2] → l1 = l2 ∧ z1 = z2.
Proof. exact: app_inj_tail. Qed.

Section MM2Deque.

Variable P : list mm2_instr.

Notation n := (length P).
Notation Q := (fin (S (S (length P)))).
Notation sym := (option (mm_sym Q)).
Notation A := (option_setoid (@mm_sym_setoid Q)).

Implicit Types (s t : nat * (nat * nat)) (x : list sym).

(** * Letters and configuration words *)

Definition lq (i : nat) : sym := Some (mm_q (translate_state P i)).
Definition la : sym := Some mm_a.
Definition lb : sym := Some mm_b.
Definition lh : sym := None.

Definition body (na nb : nat) : list sym :=
  repeat la na ++ repeat lb nb ++ [lh].

Definition cword s : list sym := lq s.1 :: body s.2.1 s.2.2.

Lemma lq_nat_zero : fin_to_nat (translate_state P 0) = 0.
Proof. by []. Qed.

Lemma lq_nat_in i : 0 < i ≤ n → fin_to_nat (translate_state P i) = S i.
Proof. case: i => [|i] Hi; first lia. by apply: translate_state_spec; lia. Qed.

Lemma lq_nat_out i : n < i → fin_to_nat (translate_state P i) = 1.
Proof.
case: i => [|i] Hi; first lia.
by rewrite /translate_state nat_to_fin_ge //; lia.
Qed.

Lemma lq_inj i j : 0 < i ≤ n → lq i = lq j → j = i.
Proof.
move=> Hi [/(f_equal fin_to_nat)]; rewrite lq_nat_in //.
case: (decide (j = 0)) => [->|Hj0]; first by rewrite lq_nat_zero.
case: (decide (j ≤ n)) => Hjn.
- by rewrite lq_nat_in //; lia.
- by rewrite lq_nat_out //; lia.
Qed.

Lemma lq_out i : n < i → lq i = lq (S n).
Proof.
move=> Hi; rewrite /lq; do 2 f_equal.
by apply: fin_to_nat_inj; rewrite !lq_nat_out //; lia.
Qed.

Lemma lq_zero_out : lq 0 ≠ lq (S n).
Proof.
move=> H; have : fin_to_nat (translate_state P 0) =
                 fin_to_nat (translate_state P (S n)).
{ by rewrite /lq in H; congruence. }
by rewrite lq_nat_zero lq_nat_out //; lia.
Qed.

(** * Shapes of `aⁿ bᵐ #` *)

Lemma body_cons_a na nb x :
  body na nb = la :: x → ∃ na', na = S na' ∧ x = body na' nb.
Proof.
case: na => [|na] /=; last by move=> [<-]; exists na.
by case: nb.
Qed.

Lemma body_cons_b na nb x :
  body na nb = lb :: x → na = 0 ∧ ∃ nb', nb = S nb' ∧ x = body 0 nb'.
Proof.
case: na => [|na] //=; case: nb => [|nb] //= [<-].
by split => //; exists nb.
Qed.

Lemma body_cons_h na nb x : body na nb = lh :: x → na = 0 ∧ nb = 0 ∧ x = [].
Proof. by case: na => [|na] //=; case: nb => [|nb] //= [<-]. Qed.

Lemma body_snoc na nb : body na nb = (repeat la na ++ repeat lb nb) ++ [lh].
Proof. by rewrite /body app_assoc. Qed.

Lemma body_snoc_h na nb x :
  body na nb = x ++ [lh] → x = repeat la na ++ repeat lb nb.
Proof. by rewrite body_snoc => H; case: (snoc_inj H) => <-. Qed.

Lemma body_snoc_bh na nb x :
  body na nb = x ++ [lb; lh] →
  ∃ nb', nb = S nb' ∧ x = repeat la na ++ repeat lb nb'.
Proof.
have -> : x ++ [lb; lh] = (x ++ [lb]) ++ [lh] by rewrite -app_assoc.
rewrite body_snoc => H; case: (snoc_inj H) => + _ {H}; case: nb => [|nb].
- rewrite app_nil_r => Hx.
  have : In lb (repeat la na) by rewrite Hx; apply: in_or_app; right; left.
  by move=> Hin; case: (repeat_spec _ _ _ Hin).
- rewrite repeat_snoc app_assoc => H'.
  by case: (snoc_inj H') => <- _; exists nb.
Qed.

Lemma body_snoc_ah na nb x :
  body na nb = x ++ [la; lh] →
  nb = 0 ∧ ∃ na', na = S na' ∧ x = repeat la na'.
Proof.
have -> : x ++ [la; lh] = (x ++ [la]) ++ [lh] by rewrite -app_assoc.
rewrite body_snoc => H; case: (snoc_inj H) => + _ {H}; case: nb => [|nb].
- rewrite app_nil_r; case: na => [|na].
  + by move=> /(f_equal length); rewrite length_app /=; lia.
  + rewrite repeat_snoc => H'.
    by case: (snoc_inj H') => <- _; split => //; exists na.
- by rewrite repeat_snoc app_assoc => H'; case: (snoc_inj H').
Qed.

(** * The rules *)

Definition rules_of (i : nat) (ρ : mm2_instr) : list (@drule A) :=
  match ρ with
  | mm2_inc_a => [(([lq i], []), ([lq (S i); la], []))]
  | mm2_inc_b => [(([lq i], [lh]), ([lq (S i)], [lb; lh]))]
  | mm2_dec_a j =>
      [(([lq i; la], []), ([lq j], []));
       (([lq i; lb], []), ([lq (S i); lb], []));
       (([lq i; lh], []), ([lq (S i); lh], []))]
  | mm2_dec_b j =>
      [(([lq i], [lb; lh]), ([lq j], [lh]));
       (([lq i], [la; lh]), ([lq (S i)], [la; lh]));
       (([lq i; lh], []), ([lq (S i); lh], []))]
  end.

Fixpoint rules_from (i : nat) (P' : list mm2_instr) : list (@drule A) :=
  match P' with [] => [] | ρ :: P' => rules_of i ρ ++ rules_from (S i) P' end.

Definition mm2_rules : list (@drule A) := rules_from 1 P.

Lemma elem_of_rules_from i P' r :
  r ∈ rules_from i P' ↔ ∃ k ρ, nth_error P' k = Some ρ ∧ r ∈ rules_of (i + k) ρ.
Proof.
elim: P' i => [|ρ P' IH] i /=.
- by split => [/elem_of_nil|[k [ρ [+ _]]]] //; case: k.
- rewrite elem_of_app IH; split.
  + case=> [Hr|[k [ρ' [Hk Hr]]]]; first by exists 0, ρ; rewrite Nat.add_0_r.
    by exists (S k), ρ'; rewrite -Nat.add_succ_comm.
  + case=> - [|k] [ρ' [/= Hk Hr]].
    * by left; move: Hk Hr => [<-]; rewrite Nat.add_0_r.
    * right; exists k, ρ'; split => //.
      by rewrite (_ : S (i + k) = i + S k) //; lia.
Qed.

Lemma elem_of_mm2_rules r :
  r ∈ mm2_rules ↔ ∃ k ρ, nth_error P k = Some ρ ∧ r ∈ rules_of (S k) ρ.
Proof. exact: elem_of_rules_from. Qed.

Lemma instr_at_nth ρ i :
  mm2_instr_at ρ i P → ∃ k, i = S k ∧ nth_error P k = Some ρ.
Proof.
move=> Hat; have Hi := mm2_instr_at_pos Hat.
exists (Nat.pred i); split => //.
by apply/nth_error_Some_mm2_instr_at_iff; rewrite -Hi.
Qed.

Lemma nth_lt k ρ : nth_error P k = Some ρ → 0 < S k ≤ n.
Proof.
move=> Hk; have : k < length P by apply nth_error_Some; rewrite Hk.
lia.
Qed.

(** * Simulation *)

Lemma in_rules k ρ r :
  nth_error P k = Some ρ → r ∈ rules_of (S k) ρ → r ∈ mm2_rules.
Proof. by move=> Hk Hr; apply/elem_of_mm2_rules; exists k, ρ. Qed.

Lemma dstepI u u' v v' x (w1 w2 : list sym) :
  ((u, u'), (v, v')) ∈ mm2_rules → w1 = u ++ x ++ u' → w2 = v ++ x ++ v' →
  dstep mm2_rules w1 w2.
Proof. by move=> Hr -> ->; exists u, u', v, v', x. Qed.

Lemma cword_step s t : mm2_step P s t → dstep mm2_rules (cword s) (cword t).
Proof.
case=> ρ [Hat Hatom].
case: Hatom Hat => [i na nb|i na nb|i j na nb|i j na nb|i j nb|i j na]
  /instr_at_nth [k [Hi Hk]]; have {Hi} -> : i = S k by exact: Hi.
- apply: (dstepI (x := body na nb) (in_rules Hk (elem_of_list_here _ _)));
    by rewrite app_nil_r.
- apply: (dstepI (x := repeat la na ++ repeat lb nb)
                 (in_rules Hk (elem_of_list_here _ _))).
  + by rewrite /cword body_snoc.
  + by rewrite /cword /body repeat_snoc -!app_assoc.
- apply: (dstepI (x := body na nb) (in_rules Hk (elem_of_list_here _ _)));
    by rewrite app_nil_r.
- apply: (dstepI (x := repeat la na ++ repeat lb nb)
                 (in_rules Hk (elem_of_list_here _ _))).
  + by rewrite /cword /body repeat_snoc -!app_assoc.
  + by rewrite /cword /body -!app_assoc.
- case: nb => [|nb].
  + apply: (dstepI (x := [])
      (in_rules Hk (elem_of_list_further _ _ _ (elem_of_list_further _ _ _
                     (elem_of_list_here _ _))))) => //.
  + apply: (dstepI (x := body 0 nb)
      (in_rules Hk (elem_of_list_further _ _ _ (elem_of_list_here _ _))));
      by rewrite app_nil_r.
- case: na => [|na].
  + apply: (dstepI (x := [])
      (in_rules Hk (elem_of_list_further _ _ _ (elem_of_list_further _ _ _
                     (elem_of_list_here _ _))))) => //.
  + apply: (dstepI (x := repeat la na)
      (in_rules Hk (elem_of_list_further _ _ _ (elem_of_list_here _ _))));
      by rewrite /cword /body repeat_snoc /= -app_assoc.
Qed.

Lemma head_inv k i y z :
  0 < S k ≤ n → lq i :: y = lq (S k) :: z → i = S k ∧ y = z.
Proof.
move=> Hk H; have Hq : lq (S k) = lq i by congruence.
by split; [apply: lq_inj Hk Hq | congruence].
Qed.

(* Closes `mm2_step P (S k, _) _` from the instruction at `S k`. *)
Local Ltac mm2_step_at Hat := eexists; split; [exact: Hat|constructor].

Lemma cword_step_inv s (w2 : list sym) :
  dstep mm2_rules (cword s) w2 → ∃ t, w2 = cword t ∧ mm2_step P s t.
Proof.
case: s => i [na nb] [u [u' [v [v' [x [/elem_of_mm2_rules [k [ρ [Hk Hr]]]
  [Hs ->]]]]]]].
have {}Hs : lq i :: body na nb = u ++ x ++ u' := Hs.
have Hkn := nth_lt Hk.
have Hat : mm2_instr_at ρ (S k) P by apply/nth_error_Some_mm2_instr_at_iff.
case: ρ Hk Hr Hat => [||j|j] Hk Hr Hat.
- move: Hr Hs => /elem_of_list_singleton [-> -> -> ->] /(head_inv Hkn) [-> Hb].
  move: Hb; rewrite /= app_nil_r => <-.
  exists (S (S k), (S na, nb)); split => //.
  by mm2_step_at Hat.
- move: Hr Hs => /elem_of_list_singleton [-> -> -> ->] /(head_inv Hkn) [-> Hb].
  move: Hb => /= /body_snoc_h ->.
  exists (S (S k), (na, S nb)); split; last by mm2_step_at Hat.
  by rewrite /cword /body repeat_snoc -!app_assoc.
- move: Hr Hs => /elem_of_cons [[-> -> -> ->]|/elem_of_cons
    [[-> -> -> ->]|/elem_of_list_singleton [-> -> -> ->]]]
    /(head_inv Hkn) [-> Hb]; move: Hb; rewrite /= app_nil_r.
  + case/body_cons_a => na' [-> ->].
    exists (j, (na', nb)); split => //.
    by mm2_step_at Hat.
  + case/body_cons_b => -> [nb' [-> ->]].
    exists (S (S k), (0, S nb')); split => //.
    by mm2_step_at Hat.
  + case/body_cons_h => -> [-> ->].
    by exists (S (S k), (0, 0)); split => //; mm2_step_at Hat.
- move: Hr Hs => /elem_of_cons [[-> -> -> ->]|/elem_of_cons
    [[-> -> -> ->]|/elem_of_list_singleton [-> -> -> ->]]]
    /(head_inv Hkn) [-> Hb]; move: Hb => /=.
  + case/body_snoc_bh => nb' [-> ->].
    exists (j, (na, nb')); split; last by mm2_step_at Hat.
    by rewrite /cword /body -!app_assoc.
  + case/body_snoc_ah => -> [na' [-> ->]].
    exists (S (S k), (S na', 0)); split; last by mm2_step_at Hat.
    by rewrite /cword /body repeat_snoc /= -app_assoc.
  + rewrite app_nil_r => /body_cons_h [-> [-> ->]].
    by exists (S (S k), (0, 0)); split => //; mm2_step_at Hat.
Qed.

(** * Halting *)

Definition mm2_bad : list (list sym) := [[lq (S n)]; [lq 0; la]; [lq 0; lb]].

Lemma cword_bad s :
  mm2_stop P s → s ≠ (0, (0, 0)) → ∃ b, b ∈ mm2_bad ∧ b `prefix_of` cword s.
Proof.
case: s => i [na nb] /mm2_stop_index_iff /= [->|Hi] Hne.
- case: na Hne => [|na] Hne.
  + case: nb Hne => [|nb] Hne //.
    exists [lq 0; lb]; split; last by exists (body 0 nb).
    by do 2 apply: elem_of_list_further; apply: elem_of_list_here.
  + exists [lq 0; la]; split; last by exists (body na nb).
    by apply: elem_of_list_further; apply: elem_of_list_here.
- exists [lq (S n)]; split; first exact: elem_of_list_here.
  by exists (body na nb); rewrite /cword /= (lq_out Hi).
Qed.

Lemma cword_accept_ok b : b ∈ mm2_bad → ¬ b `prefix_of` cword (0, (0, 0)).
Proof.
rewrite /mm2_bad !elem_of_cons elem_of_nil => Hb [y Hy].
by case: Hb => [?|[?|[?|//]]]; subst b; move: Hy => /= [].
Qed.

Lemma cword_active_ok s b :
  0 < s.1 ≤ n → b ∈ mm2_bad → ¬ b `prefix_of` cword s.
Proof.
case: s => i [na nb] /= Hi.
rewrite /mm2_bad !elem_of_cons elem_of_nil => Hb [y Hy].
case: Hb => [?|[?|[?|//]]]; subst b.
- by have /(lq_inj Hi) : lq i = lq (S n) := f_equal (hd lh) Hy; lia.
- by have /(lq_inj Hi) : lq i = lq 0 := f_equal (hd lh) Hy; lia.
- by have /(lq_inj Hi) : lq i = lq 0 := f_equal (hd lh) Hy; lia.
Qed.

Lemma stop_or_active s : mm2_stop P s ∨ 0 < s.1 ≤ n.
Proof.
case: (decide (s.1 = 0 ∨ n < s.1)) => H.
- by left; apply/mm2_stop_index_iff.
- by right; lia.
Qed.

Lemma rtc_stop_eq s t : rtc (mm2_step P) s t → mm2_stop P s → t = s.
Proof. by case=> // x y z Hxy _ /(_ y Hxy). Qed.

(* The configurations of a halting run: a finite set, closed under steps
   by determinism. *)
Lemma run_path s y :
  rtc (mm2_step P) s y → mm2_stop P y →
  ∃ ls : list (nat * (nat * nat)), s ∈ ls ∧
    (∀ z, z ∈ ls → rtc (mm2_step P) z y) ∧
    (∀ z z', z ∈ ls → mm2_step P z z' → z' ∈ ls).
Proof.
elim=> [x Hstop|x x' y' Hxx' Hrest IH Hstop].
- exists [x]; split; first exact: elem_of_list_here.
  split; first by move=> z /elem_of_list_singleton ->; apply: rtc_refl.
  by move=> z z' /elem_of_list_singleton -> /Hstop.
- have [ls [Hx' [Hreach Hcl]]] := IH Hstop.
  exists (x :: ls); split; first exact: elem_of_list_here.
  split.
  + move=> z /elem_of_cons [->|/Hreach //]; exact: rtc_l Hxx' Hrest.
  + move=> z z' /elem_of_cons [->|Hz] Hzz'.
    * by rewrite (mm2_step_det Hzz' Hxx'); apply: elem_of_list_further.
    * by apply: elem_of_list_further; apply: Hcl Hzz'.
Qed.

End MM2Deque.
