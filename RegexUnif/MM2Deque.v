(* Two-counter (MM2) machines as two-ended Post normal systems
   (RegexUnif/Invariant.v's `dstep`), in place of the deterministic tag
   system of the source sketch, encoded so that every configuration word
   lies in a cell of RegexUnif/Invariant.v made of its first two and last
   two letters, and each such cell is matched by at most one rule.

   A configuration `(i, (n, m))` is the word `cword` = `q_i aⁿ # # bᵐ #`
   over `option (mm_sym Q)`, with `None` the letter `#` and `q_i` the
   letter of CKAUndec/Encoding.v's `translate_state` (pc 0, every pc
   beyond the program, and each pc in between get distinct letters). The
   separator `# #` makes both zero tests positive patterns: `q_i #` at the
   front for `a`, `# #` at the back for `b`. Each instruction gives at
   most two rules (`rules_of`), which read at most two letters at each
   end; on encoded words they simulate MM2 step for step (`cword_step`,
   `cword_step_inv`). The rules of one pc differ in the second letter at
   the front or the second to last at the back, and the rules of
   different pcs in the state letter, so a cell of two-letter words
   determines its rule (`rules_det`).

   The cells (`mm2_cells`) are all pairs of two-letter words except those
   of halted configurations other than `(0, (0, 0))`: those starting with
   `q_out`, and those starting with `q₀` other than `(q₀ #, # #)`. The
   configurations of a run halting at `(0, (0, 0))` are covered by cells
   (`cword_cover_active`, `cword_cover_accept`; `run_path` collects them, a
   finite set closed under steps by determinism), and one halting
   elsewhere is in none (`cword_halt_uncovered`). Nothing here is about
   KA. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list finite fin relations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Undecidability.MinskyMachines Require Import MM2.
From Undecidability.MinskyMachines.Util Require Import MM2_facts.
From kacc Require Import KA.algebra CKAUndec.Encoding.
From kacc Require Import RegexUnif.Invariant.

Local Open Scope nat_scope.

Lemma repeat_snoc {X} (z : X) k : repeat z (S k) = repeat z k ++ [z].
Proof. by elim: k => //= k ->. Qed.

Lemma snoc_inj {X} (l1 l2 : list X) (z1 z2 : X) :
  l1 ++ [z1] = l2 ++ [z2] → l1 = l2 ∧ z1 = z2.
Proof. exact: app_inj_tail. Qed.

Lemma app_pair {X} (l : list X) (y z : X) : l ++ [y; z] = (l ++ [y]) ++ [z].
Proof. by rewrite -app_assoc. Qed.

Lemma split4 {X} (t : list X) :
  4 ≤ length t → ∃ x1 x2 y z1 z2, t = [x1; x2] ++ y ++ [z1; z2].
Proof.
case: t => [|x1 [|x2 t]] /= Hl; try lia.
case: (exists_last (l := t)) => [Ht|t1 [z2 Ht]].
  by move: Hl; rewrite Ht /=; lia.
case: (exists_last (l := t1)) => [Ht1|y [z1 Ht1]].
  by move: Hl; rewrite Ht Ht1 /=; lia.
by exists x1, x2, y, z1, z2; rewrite Ht Ht1 -app_assoc.
Qed.

Section MM2Deque.

Variable P : list mm2_instr.

Notation n := (length P).
Notation Q := (fin (S (S (length P)))).
Notation sym := (option (mm_sym Q)).
Notation A := (option_setoid (@mm_sym_setoid Q)).

Implicit Types (s t : nat * (nat * nat)) (x : list sym).

(** * Letters *)

Definition lq (i : nat) : sym := Some (mm_q (translate_state P i)).
Definition la : sym := Some mm_a.
Definition lb : sym := Some mm_b.
Definition lh : sym := None.

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

(** * MM2 facts *)

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

Lemma head_inv k i y z :
  0 < S k ≤ n → lq i :: y = lq (S k) :: z → i = S k ∧ y = z.
Proof.
move=> Hk H; have Hq : lq (S k) = lq i by congruence.
by split; [apply: lq_inj Hk Hq | congruence].
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

(** * Configuration words *)

Definition body (na nb : nat) : list sym :=
  repeat la na ++ [lh; lh] ++ repeat lb nb ++ [lh].

Definition cword s : list sym := lq s.1 :: body s.2.1 s.2.2.

Lemma cword_length s : 4 ≤ length (cword s).
Proof. rewrite /cword /body /= length_app /= length_app /=; lia. Qed.

Lemma body_cons_a na nb x :
  body na nb = la :: x → ∃ na', na = S na' ∧ x = body na' nb.
Proof. by case: na => [|na] //= [<-]; exists na. Qed.

Lemma body_cons_h na nb x :
  body na nb = lh :: x → na = 0 ∧ x = lh :: repeat lb nb ++ [lh].
Proof. by case: na => [|na] //= [<-]. Qed.

Lemma body_snoc_h na nb x :
  body na nb = x ++ [lh] → x = repeat la na ++ [lh; lh] ++ repeat lb nb.
Proof.
have -> : body na nb = (repeat la na ++ [lh; lh] ++ repeat lb nb) ++ [lh]
  by rewrite /body -!app_assoc.
by move=> /(@snoc_inj sym _ _ _ _) [<-].
Qed.

Lemma body_snoc_bh na nb x :
  body na nb = x ++ [lb; lh] →
  ∃ nb', nb = S nb' ∧ x = repeat la na ++ [lh; lh] ++ repeat lb nb'.
Proof.
rewrite app_pair => /body_snoc_h; case: nb => [|nb].
- by rewrite /= app_pair => /(@snoc_inj sym _ _ _ _) [_].
- rewrite repeat_snoc !app_assoc => /(@snoc_inj sym _ _ _ _) [-> _].
  by exists nb; rewrite -!app_assoc.
Qed.

Lemma body_snoc_hh na nb x :
  body na nb = x ++ [lh; lh] → nb = 0 ∧ x = repeat la na ++ [lh].
Proof.
rewrite app_pair => /body_snoc_h; case: nb => [|nb].
- by rewrite /= app_pair => /(@snoc_inj sym _ _ _ _) [-> _].
- by rewrite repeat_snoc !app_assoc => /(@snoc_inj sym _ _ _ _) [_].
Qed.

(** * The rules *)

Definition rules_of (i : nat) (ρ : mm2_instr) : list (@drule A) :=
  match ρ with
  | mm2_inc_a => [(([lq i], []), ([lq (S i); la], []))]
  | mm2_inc_b => [(([lq i], [lh]), ([lq (S i)], [lb; lh]))]
  | mm2_dec_a j =>
      [(([lq i; la], []), ([lq j], []));
       (([lq i; lh], []), ([lq (S i); lh], []))]
  | mm2_dec_b j =>
      [(([lq i], [lb; lh]), ([lq j], [lh]));
       (([lq i], [lh; lh]), ([lq (S i)], [lh; lh]))]
  end.

Fixpoint rules_from (i : nat) (P' : list mm2_instr) : list (@drule A) :=
  match P' with
  | [] => []
  | ρ :: P' => rules_of i ρ ++ rules_from (S i) P'
  end.

Definition mm2_rules : list (@drule A) := rules_from 1 P.

Lemma elem_of_rules_from i P' r :
  r ∈ rules_from i P' ↔
  ∃ k ρ, nth_error P' k = Some ρ ∧ r ∈ rules_of (i + k) ρ.
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

Lemma rules_of_short i ρ r :
  r ∈ rules_of i ρ → length r.1.1 ≤ 2 ∧ length r.1.2 ≤ 2.
Proof.
case: ρ => [||j|j] /=.
- by move=> /elem_of_list_singleton -> /=; lia.
- by move=> /elem_of_list_singleton -> /=; lia.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->] /=; lia.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->] /=; lia.
Qed.

Lemma rules_of_head i ρ r :
  r ∈ rules_of i ρ → ∃ u, r.1.1 = lq i :: u.
Proof.
case: ρ => [||j|j] /=.
- by move=> /elem_of_list_singleton ->; exists [].
- by move=> /elem_of_list_singleton ->; exists [].
- by case/elem_of_cons => [->|/elem_of_list_singleton ->]; eexists.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->]; exists [].
Qed.

(* Two rules of one instruction differ in a two-letter front or back. *)
Lemma rules_of_apart i ρ r1 r2 :
  r1 ∈ rules_of i ρ → r2 ∈ rules_of i ρ →
  r1 = r2 ∨
  (length r1.1.1 = 2 ∧ length r2.1.1 = 2 ∧ r1.1.1 ≠ r2.1.1) ∨
  (length r1.1.2 = 2 ∧ length r2.1.2 = 2 ∧ r1.1.2 ≠ r2.1.2).
Proof.
case: ρ => [||j|j] /=.
- by move=> /elem_of_list_singleton -> /elem_of_list_singleton ->; left.
- by move=> /elem_of_list_singleton -> /elem_of_list_singleton ->; left.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->];
    case/elem_of_cons => [->|/elem_of_list_singleton ->];
    [left | right; left | right; left | left].
- by case/elem_of_cons => [->|/elem_of_list_singleton ->];
    case/elem_of_cons => [->|/elem_of_list_singleton ->];
    [left | right; right | right; right | left].
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
- apply: (dstepI (x := repeat la na ++ [lh; lh] ++ repeat lb nb)
                  (in_rules Hk (elem_of_list_here _ _))).
  + by rewrite /cword /body /= -!app_assoc.
  + by rewrite /cword /body repeat_snoc -!app_assoc.
- apply: (dstepI (x := body na nb) (in_rules Hk (elem_of_list_here _ _)));
    by rewrite app_nil_r.
- apply: (dstepI (x := repeat la na ++ [lh; lh] ++ repeat lb nb)
                  (in_rules Hk (elem_of_list_here _ _))).
  + by rewrite /cword /body repeat_snoc -!app_assoc.
  + by rewrite /cword /body -!app_assoc.
- apply: (dstepI (x := lh :: repeat lb nb ++ [lh])
    (in_rules Hk (elem_of_list_further _ _ _ (elem_of_list_here _ _))));
    by rewrite app_nil_r.
- apply: (dstepI (x := repeat la na ++ [lh])
    (in_rules Hk (elem_of_list_further _ _ _ (elem_of_list_here _ _))));
    by rewrite /cword /body -!app_assoc.
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
- move: Hr Hs => /elem_of_cons [[-> -> -> ->]|/elem_of_list_singleton
    [-> -> -> ->]] /(head_inv Hkn) [-> Hb]; move: Hb; rewrite /= app_nil_r.
  + case/body_cons_a => na' [-> ->].
    exists (j, (na', nb)); split => //.
    by mm2_step_at Hat.
  + case/body_cons_h => -> ->.
    by exists (S (S k), (0, nb)); split => //; mm2_step_at Hat.
- move: Hr Hs => /elem_of_cons [[-> -> -> ->]|/elem_of_list_singleton
    [-> -> -> ->]] /(head_inv Hkn) [-> Hb]; move: Hb => /=.
  + case/body_snoc_bh => nb' [-> ->].
    exists (j, (na, nb')); split; last by mm2_step_at Hat.
    by rewrite /cword /body -!app_assoc.
  + case/body_snoc_hh => -> ->.
    exists (S (S k), (na, 0)); split; last by mm2_step_at Hat.
    by rewrite /cword /body -!app_assoc.
Qed.

(** * Cells *)

Definition good (c : @cell A) : Prop :=
  head c.1 ≠ Some (lq (S n)) ∧
  (head c.1 = Some (lq 0) → c = ([lq 0; lh], [lh; lh])).

Local Instance good_dec c : Decision (good c).
Proof. rewrite /good; apply _. Defined.

Definition cell2 (z : (sym * sym) * (sym * sym)) : @cell A :=
  ([z.1.1; z.1.2], [z.2.1; z.2.2]).

Local Instance cell2_inj : Inj (=) (=) cell2.
Proof. by move=> [[? ?] [? ?]] [[? ?] [? ?]] [-> -> -> ->]. Qed.

Definition mm2_cells : list (@cell A) := filter good (cell2 <$> enum _).

Lemma mm2_cells_nodup : NoDup mm2_cells.
Proof. apply: NoDup_filter; apply: NoDup_fmap_2; exact: NoDup_enum. Qed.

Lemma elem_of_mm2_cells c :
  c ∈ mm2_cells ↔ good c ∧ ∃ x1 x2 y1 y2 : sym, c = ([x1; x2], [y1; y2]).
Proof.
rewrite /mm2_cells elem_of_list_filter elem_of_list_fmap; split.
- case=> Hg [[[x1 x2] [y1 y2]] [Hc _]]; split; first done.
  by exists x1, x2, y1, y2.
- case=> Hg [x1 [x2 [y1 [y2 Hc]]]]; split; first done.
  by exists ((x1, x2), (y1, y2)); split; last apply: elem_of_enum.
Qed.

Lemma rules_cells_len r c :
  r ∈ mm2_rules → c ∈ mm2_cells →
  length r.1.1 ≤ length c.1 ∧ length r.1.2 ≤ length c.2.
Proof.
move=> /elem_of_mm2_rules [k [ρ [_ /rules_of_short Hr]]].
by case/elem_of_mm2_cells => _ [x1 [x2 [y1 [y2 ->]]]].
Qed.

Lemma rules_det c r1 r2 :
  c ∈ mm2_cells → r1 ∈ mm2_rules → r2 ∈ mm2_rules →
  matches c r1 → matches c r2 → r1 = r2.
Proof.
case/elem_of_mm2_cells => _ [x1 [x2 [y1 [y2 ->]]]].
move=> /elem_of_mm2_rules [k1 [ρ1 [Hk1 Hr1]]].
move=> /elem_of_mm2_rules [k2 [ρ2 [Hk2 Hr2]]] [/= Hp1 Hs1] [/= Hp2 Hs2].
have Hx k ρ r : r ∈ rules_of (S k) ρ → r.1.1 `prefix_of` [x1; x2] →
    x1 = lq (S k).
{ move=> Hr; have [u ->] := rules_of_head Hr => Hp.
  by have := prefix_cons_inv_1 _ _ _ _ Hp. }
have Hk : k2 = k1.
{ have := Hx _ _ _ Hr2 Hp2; rewrite (Hx _ _ _ Hr1 Hp1) => Hq.
  by have := lq_inj (nth_lt Hk1) Hq; lia. }
subst k2; move: Hr2; rewrite Hk2 in Hk1; case: Hk1 => -> Hr2.
case: (rules_of_apart Hr1 Hr2) => [//|[[H1 [H2 Hne]]|[H1 [H2 Hne]]]].
- case: Hne; rewrite (prefix_length_eq _ _ Hp1); first by rewrite H1.
  by rewrite (prefix_length_eq _ _ Hp2) // H2.
- case: Hne; rewrite (suffix_length_eq _ _ Hs1); first by rewrite H1.
  by rewrite (suffix_length_eq _ _ Hs2) // H2.
Qed.

Lemma cword_head s (x1 x2 z1 z2 : sym) (y : list sym) :
  cword s = [x1; x2] ++ y ++ [z1; z2] → x1 = lq s.1.
Proof. by case. Qed.

Lemma cword_cover_active s :
  0 < s.1 ≤ n → ∃ c, c ∈ mm2_cells ∧ in_cell c (cword s).
Proof.
move=> Hs; have [x1 [x2 [y [z1 [z2 Ht]]]]] := split4 (cword_length s).
exists ([x1; x2], [z1; z2]); split; last by exists y.
apply/elem_of_mm2_cells; split; last by exists x1, x2, z1, z2.
rewrite /good /= (cword_head Ht); split.
- move=> H; have Hq : lq s.1 = lq (S n) by congruence.
  by have := lq_inj Hs Hq; lia.
- move=> H; have Hq : lq s.1 = lq 0 by congruence.
  by have := lq_inj Hs Hq; lia.
Qed.

Lemma cword_cover_accept : ∃ c, c ∈ mm2_cells ∧ in_cell c (cword (0, (0, 0))).
Proof.
exists ([lq 0; lh], [lh; lh]); split; last by exists [].
apply/elem_of_mm2_cells; split; last by exists (lq 0), lh, lh, lh.
by split => //= H; apply: lq_zero_out; congruence.
Qed.

Lemma cword_halt_uncovered s c :
  mm2_stop P s → s ≠ (0, (0, 0)) → c ∈ mm2_cells → ¬ in_cell c (cword s).
Proof.
case: s => i [na nb] /mm2_stop_index_iff /= Hstop Hne.
case/elem_of_mm2_cells => - [Hout H0] [x1 [x2 [z1 [z2 Hc]]]] [y]; subst c.
rewrite /cword /= => - [Hx1 Hy]; subst x1.
case: Hstop => [Hi|Hi].
- subst i; case: (H0 eq_refl) => Hx2 Hz1 Hz2; subst x2 z1 z2.
  have [Hna _] := body_cons_h Hy.
  have [Hnb _] := body_snoc_hh (x := lh :: y) Hy.
  by subst na nb.
- by case: Hout; rewrite /= (lq_out Hi).
Qed.

End MM2Deque.
