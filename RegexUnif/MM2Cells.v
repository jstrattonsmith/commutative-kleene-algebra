(* Two-counter (MM2) machines as two-ended Post normal systems, encoded
   for RegexUnif/Cells.v: every configuration word has length at least
   four, so it lies in a cell made of its first two and last two
   letters, and each such cell is matched by at most one rule.

   A configuration `(i, (n, m))` is the word `cfg` = `q_i aⁿ # # bᵐ #`,
   with RegexUnif/MM2Deque.v's letters (`#` is `None`). The separator
   `# #` makes both zero tests positive patterns: `q_i #` at the front
   for `a`, `# #` at the back for `b`. Each instruction gives at most two
   rules (`crules_of`), which read at most two letters at each end. The
   rules of one pc differ in the second letter at the front or the second
   to last at the back, and the rules of different pcs in the state
   letter, so a cell of two-letter words determines its rule
   (`crules_det`).

   The cells (`mm2_cells`) are all pairs of two-letter words except those
   of halted configurations other than `(0, (0, 0))`: those starting with
   `q_out`, and those starting with `q₀` other than `(q₀ #, # #)`. The
   configurations of a run halting at `(0, (0, 0))` are covered by cells
   (`cfg_cover_active`, `cfg_cover_accept`), and one halting elsewhere is
   in none (`cfg_halt_uncovered`). Nothing here is about KA. *)

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
From kacc Require Import RegexUnif.Invariant RegexUnif.Cells RegexUnif.MM2Deque.

Local Open Scope nat_scope.

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

Section MM2Cells.

Variable P : list mm2_instr.

Notation n := (length P).
Notation Q := (fin (S (S (length P)))).
Notation sym := (option (mm_sym Q)).
Notation A := (option_setoid (@mm_sym_setoid Q)).

Local Notation lq := (MM2Deque.lq P).
Local Notation la := (MM2Deque.la P).
Local Notation lb := (MM2Deque.lb P).
Local Notation lh := (MM2Deque.lh P).

Implicit Types (s t : nat * (nat * nat)) (x y : list sym).

(** * Configuration words *)

Definition cbody (na nb : nat) : list sym :=
  repeat la na ++ [lh; lh] ++ repeat lb nb ++ [lh].

Definition cfg s : list sym := lq s.1 :: cbody s.2.1 s.2.2.

Lemma cfg_length s : 4 ≤ length (cfg s).
Proof. rewrite /cfg /cbody /= length_app /= length_app /=; lia. Qed.

Lemma cbody_cons_a na nb x :
  cbody na nb = la :: x → ∃ na', na = S na' ∧ x = cbody na' nb.
Proof. by case: na => [|na] //= [<-]; exists na. Qed.

Lemma cbody_cons_h na nb x :
  cbody na nb = lh :: x → na = 0 ∧ x = lh :: repeat lb nb ++ [lh].
Proof. by case: na => [|na] //= [<-]. Qed.

Lemma cbody_snoc_h na nb x :
  cbody na nb = x ++ [lh] → x = repeat la na ++ [lh; lh] ++ repeat lb nb.
Proof.
have -> : cbody na nb = (repeat la na ++ [lh; lh] ++ repeat lb nb) ++ [lh]
  by rewrite /cbody -!app_assoc.
by move=> /(@snoc_inj sym _ _ _ _) [<-].
Qed.

Lemma cbody_snoc_bh na nb x :
  cbody na nb = x ++ [lb; lh] →
  ∃ nb', nb = S nb' ∧ x = repeat la na ++ [lh; lh] ++ repeat lb nb'.
Proof.
rewrite app_pair => /cbody_snoc_h; case: nb => [|nb].
- by rewrite /= app_pair => /(@snoc_inj sym _ _ _ _) [_].
- rewrite repeat_snoc !app_assoc => /(@snoc_inj sym _ _ _ _) [-> _].
  by exists nb; rewrite -!app_assoc.
Qed.

Lemma cbody_snoc_hh na nb x :
  cbody na nb = x ++ [lh; lh] → nb = 0 ∧ x = repeat la na ++ [lh].
Proof.
rewrite app_pair => /cbody_snoc_h; case: nb => [|nb].
- by rewrite /= app_pair => /(@snoc_inj sym _ _ _ _) [-> _].
- by rewrite repeat_snoc !app_assoc => /(@snoc_inj sym _ _ _ _) [_].
Qed.

(** * The rules *)

Definition crules_of (i : nat) (ρ : mm2_instr) : list (@drule A) :=
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

Fixpoint crules_from (i : nat) (P' : list mm2_instr) : list (@drule A) :=
  match P' with
  | [] => []
  | ρ :: P' => crules_of i ρ ++ crules_from (S i) P'
  end.

Definition mm2_crules : list (@drule A) := crules_from 1 P.

Lemma elem_of_crules_from i P' r :
  r ∈ crules_from i P' ↔
  ∃ k ρ, nth_error P' k = Some ρ ∧ r ∈ crules_of (i + k) ρ.
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

Lemma elem_of_mm2_crules r :
  r ∈ mm2_crules ↔ ∃ k ρ, nth_error P k = Some ρ ∧ r ∈ crules_of (S k) ρ.
Proof. exact: elem_of_crules_from. Qed.

Lemma crules_of_short i ρ r :
  r ∈ crules_of i ρ → length r.1.1 ≤ 2 ∧ length r.1.2 ≤ 2.
Proof.
case: ρ => [||j|j] /=.
- by move=> /elem_of_list_singleton -> /=; lia.
- by move=> /elem_of_list_singleton -> /=; lia.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->] /=; lia.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->] /=; lia.
Qed.

Lemma crules_of_head i ρ r :
  r ∈ crules_of i ρ → ∃ u, r.1.1 = lq i :: u.
Proof.
case: ρ => [||j|j] /=.
- by move=> /elem_of_list_singleton ->; exists [].
- by move=> /elem_of_list_singleton ->; exists [].
- by case/elem_of_cons => [->|/elem_of_list_singleton ->]; eexists.
- by case/elem_of_cons => [->|/elem_of_list_singleton ->]; exists [].
Qed.

(* Two rules of one instruction differ in a two-letter front or back. *)
Lemma crules_of_apart i ρ r1 r2 :
  r1 ∈ crules_of i ρ → r2 ∈ crules_of i ρ →
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

Lemma in_crules k ρ r :
  nth_error P k = Some ρ → r ∈ crules_of (S k) ρ → r ∈ mm2_crules.
Proof. by move=> Hk Hr; apply/elem_of_mm2_crules; exists k, ρ. Qed.

Lemma cdstepI u u' v v' x (w1 w2 : list sym) :
  ((u, u'), (v, v')) ∈ mm2_crules → w1 = u ++ x ++ u' → w2 = v ++ x ++ v' →
  dstep mm2_crules w1 w2.
Proof. by move=> Hr -> ->; exists u, u', v, v', x. Qed.

Lemma cfg_step s t : mm2_step P s t → dstep mm2_crules (cfg s) (cfg t).
Proof.
case=> ρ [Hat Hatom].
case: Hatom Hat => [i na nb|i na nb|i j na nb|i j na nb|i j nb|i j na]
  /instr_at_nth [k [Hi Hk]]; have {Hi} -> : i = S k by exact: Hi.
- apply: (cdstepI (x := cbody na nb) (in_crules Hk (elem_of_list_here _ _)));
    by rewrite app_nil_r.
- apply: (cdstepI (x := repeat la na ++ [lh; lh] ++ repeat lb nb)
                  (in_crules Hk (elem_of_list_here _ _))).
  + by rewrite /cfg /cbody /= -!app_assoc.
  + by rewrite /cfg /cbody repeat_snoc -!app_assoc.
- apply: (cdstepI (x := cbody na nb) (in_crules Hk (elem_of_list_here _ _)));
    by rewrite app_nil_r.
- apply: (cdstepI (x := repeat la na ++ [lh; lh] ++ repeat lb nb)
                  (in_crules Hk (elem_of_list_here _ _))).
  + by rewrite /cfg /cbody repeat_snoc -!app_assoc.
  + by rewrite /cfg /cbody -!app_assoc.
- apply: (cdstepI (x := lh :: repeat lb nb ++ [lh])
    (in_crules Hk (elem_of_list_further _ _ _ (elem_of_list_here _ _))));
    by rewrite app_nil_r.
- apply: (cdstepI (x := repeat la na ++ [lh])
    (in_crules Hk (elem_of_list_further _ _ _ (elem_of_list_here _ _))));
    by rewrite /cfg /cbody -!app_assoc.
Qed.

(* Closes `mm2_step P (S k, _) _` from the instruction at `S k`. *)
Local Ltac mm2_step_at Hat := eexists; split; [exact: Hat|constructor].

Lemma cfg_step_inv s (w2 : list sym) :
  dstep mm2_crules (cfg s) w2 → ∃ t, w2 = cfg t ∧ mm2_step P s t.
Proof.
case: s => i [na nb] [u [u' [v [v' [x [/elem_of_mm2_crules [k [ρ [Hk Hr]]]
  [Hs ->]]]]]]].
have {}Hs : lq i :: cbody na nb = u ++ x ++ u' := Hs.
have Hkn := nth_lt Hk.
have Hat : mm2_instr_at ρ (S k) P by apply/nth_error_Some_mm2_instr_at_iff.
case: ρ Hk Hr Hat => [||j|j] Hk Hr Hat.
- move: Hr Hs => /elem_of_list_singleton [-> -> -> ->] /(head_inv Hkn) [-> Hb].
  move: Hb; rewrite /= app_nil_r => <-.
  exists (S (S k), (S na, nb)); split => //.
  by mm2_step_at Hat.
- move: Hr Hs => /elem_of_list_singleton [-> -> -> ->] /(head_inv Hkn) [-> Hb].
  move: Hb => /= /cbody_snoc_h ->.
  exists (S (S k), (na, S nb)); split; last by mm2_step_at Hat.
  by rewrite /cfg /cbody repeat_snoc -!app_assoc.
- move: Hr Hs => /elem_of_cons [[-> -> -> ->]|/elem_of_list_singleton
    [-> -> -> ->]] /(head_inv Hkn) [-> Hb]; move: Hb; rewrite /= app_nil_r.
  + case/cbody_cons_a => na' [-> ->].
    exists (j, (na', nb)); split => //.
    by mm2_step_at Hat.
  + case/cbody_cons_h => -> ->.
    by exists (S (S k), (0, nb)); split => //; mm2_step_at Hat.
- move: Hr Hs => /elem_of_cons [[-> -> -> ->]|/elem_of_list_singleton
    [-> -> -> ->]] /(head_inv Hkn) [-> Hb]; move: Hb => /=.
  + case/cbody_snoc_bh => nb' [-> ->].
    exists (j, (na, nb')); split; last by mm2_step_at Hat.
    by rewrite /cfg /cbody -!app_assoc.
  + case/cbody_snoc_hh => -> ->.
    exists (S (S k), (na, 0)); split; last by mm2_step_at Hat.
    by rewrite /cfg /cbody -!app_assoc.
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

Lemma crules_cells_len r c :
  r ∈ mm2_crules → c ∈ mm2_cells →
  length r.1.1 ≤ length c.1 ∧ length r.1.2 ≤ length c.2.
Proof.
move=> /elem_of_mm2_crules [k [ρ [_ /crules_of_short Hr]]].
by case/elem_of_mm2_cells => _ [x1 [x2 [y1 [y2 ->]]]].
Qed.

Lemma crules_det c r1 r2 :
  c ∈ mm2_cells → r1 ∈ mm2_crules → r2 ∈ mm2_crules →
  matches c r1 → matches c r2 → r1 = r2.
Proof.
case/elem_of_mm2_cells => _ [x1 [x2 [y1 [y2 ->]]]].
move=> /elem_of_mm2_crules [k1 [ρ1 [Hk1 Hr1]]].
move=> /elem_of_mm2_crules [k2 [ρ2 [Hk2 Hr2]]] [/= Hp1 Hs1] [/= Hp2 Hs2].
have Hx k ρ r : r ∈ crules_of (S k) ρ → r.1.1 `prefix_of` [x1; x2] →
    x1 = lq (S k).
{ move=> Hr; have [u ->] := crules_of_head Hr => Hp.
  by have := prefix_cons_inv_1 _ _ _ _ Hp. }
have Hk : k2 = k1.
{ have := Hx _ _ _ Hr2 Hp2; rewrite (Hx _ _ _ Hr1 Hp1) => Hq.
  by have := lq_inj (nth_lt Hk1) Hq; lia. }
subst k2; move: Hr2; rewrite Hk2 in Hk1; case: Hk1 => -> Hr2.
case: (crules_of_apart Hr1 Hr2) => [//|[[H1 [H2 Hne]]|[H1 [H2 Hne]]]].
- case: Hne; rewrite (prefix_length_eq _ _ Hp1); first by rewrite H1.
  by rewrite (prefix_length_eq _ _ Hp2) // H2.
- case: Hne; rewrite (suffix_length_eq _ _ Hs1); first by rewrite H1.
  by rewrite (suffix_length_eq _ _ Hs2) // H2.
Qed.

Lemma cfg_head s (x1 x2 z1 z2 : sym) y :
  cfg s = [x1; x2] ++ y ++ [z1; z2] → x1 = lq s.1.
Proof. by case. Qed.

Lemma cfg_cover_active s :
  0 < s.1 ≤ n → ∃ c, c ∈ mm2_cells ∧ in_cell c (cfg s).
Proof.
move=> Hs; have [x1 [x2 [y [z1 [z2 Ht]]]]] := split4 (cfg_length s).
exists ([x1; x2], [z1; z2]); split; last by exists y.
apply/elem_of_mm2_cells; split; last by exists x1, x2, z1, z2.
rewrite /good /= (cfg_head Ht); split.
- move=> H; have Hq : lq s.1 = lq (S n) by congruence.
  by have := lq_inj Hs Hq; lia.
- move=> H; have Hq : lq s.1 = lq 0 by congruence.
  by have := lq_inj Hs Hq; lia.
Qed.

Lemma cfg_cover_accept : ∃ c, c ∈ mm2_cells ∧ in_cell c (cfg (0, (0, 0))).
Proof.
exists ([lq 0; lh], [lh; lh]); split; last by exists [].
apply/elem_of_mm2_cells; split; last by exists (lq 0), lh, lh, lh.
by split => //= H; apply: lq_zero_out; congruence.
Qed.

Lemma cfg_halt_uncovered s c :
  mm2_stop P s → s ≠ (0, (0, 0)) → c ∈ mm2_cells → ¬ in_cell c (cfg s).
Proof.
case: s => i [na nb] /mm2_stop_index_iff /= Hstop Hne.
case/elem_of_mm2_cells => - [Hout H0] [x1 [x2 [z1 [z2 Hc]]]] [y]; subst c.
rewrite /cfg /= => - [Hx1 Hy]; subst x1.
case: Hstop => [Hi|Hi].
- subst i; case: (H0 eq_refl) => Hx2 Hz1 Hz2; subst x2 z1 z2.
  have [Hna _] := cbody_cons_h Hy.
  have [Hnb _] := cbody_snoc_hh (x := lh :: y) Hy.
  by subst na nb.
- by case: Hout; rewrite /= (lq_out Hi).
Qed.

End MM2Cells.
