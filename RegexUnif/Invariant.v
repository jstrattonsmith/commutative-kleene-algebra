(* Regular inductive invariants as KA unification problems: the core of
   the proof that KA unification is Sigma^0_1-complete, already for ONE
   equation in which no variable occurs twice on the same side.

   A two-ended Post normal system is a list of rules `((u, u'), (v, v'))`,
   each rewriting `u ++ x ++ u'` to `v ++ x ++ v'` (`dstep`). Tag systems
   are the case `u' = v = []`.

   A cell is a pair `(p, s)` of words, standing for the words
   `p ++ y ++ s`. Given a list of cells, the invariant is not a variable
   but the term `T = ⨆_{(p,s)} p ⋅ X_{p,s} ⋅ s` (`cterm`), with one
   variable per cell. If no rule reads more than a cell's `p` at the
   front or its `s` at the back, a rule `((u, u'), (v, v'))` applied to
   a word of the cell `(u ++ p', s' ++ u')` gives
   `v ++ p' ++ y ++ s' ++ v'`, so the image of `T` under one step is
   again a term, `G = ⨆ (v ++ p') ⋅ X_{p,s} ⋅ (s' ++ v')` (`sterm`). If
   each cell is matched by at most one rule, `G` takes the first
   (`first_rule`) and has each variable at most once. The equation
   `w ⊔ G ⊔ C ≡ T` (`cell_eq`), with a fresh variable `C`, says that `T`
   contains `w` and `G`, i.e. that `T` is an invariant.

   - `cell_sound`: in a language-level solution, every word reachable
     from `w` lies in a cell.
   - `cell_complete`: a finite set of words containing `w`, closed under
     steps and covered by the cells, gives a solution modulo pre-KA, by
     RegexUnif/StarFree.v.
   - `cell_eq_side_linear`: no variable occurs twice on a side. *)

Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list countable finite relations.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.
From kacc Require Import RegexUnif.Syntax RegexUnif.StarFree.

Lemma fmap_as_omap {X Y} (g : X → Y) (xs : list X) :
  g <$> xs = omap (λ x, Some (g x)) xs.
Proof. by elim: xs => //= x xs ->. Qed.

(* Cutting a rule's context out of a cell. *)
Lemma cut_front {X} (u x p y : list X) :
  length u ≤ length p → u ++ x = p ++ y → ∃ p', p = u ++ p' ∧ x = p' ++ y.
Proof.
move=> Hl /app_eq_app [k [[Hu Hy]|[Hp Hx]]]; last by exists k.
have Hk : k = [] by apply: nil_length_inv; move: Hl; rewrite Hu length_app; lia.
by exists []; rewrite Hu Hy Hk !app_nil_r.
Qed.

Lemma cut_back {X} (x u' y s : list X) :
  length u' ≤ length s → x ++ u' = y ++ s → ∃ s', s = s' ++ u' ∧ x = y ++ s'.
Proof.
move=> Hl /app_eq_app [k [[Hx Hs]|[Hy Hu]]]; first by exists k.
have Hk : k = [] by apply: nil_length_inv; move: Hl; rewrite Hu length_app; lia.
by exists []; rewrite Hu Hy Hk !app_nil_r.
Qed.

Lemma rule_cell {X} (u x u' p y s : list X) :
  length u ≤ length p → length u' ≤ length s →
  u ++ x ++ u' = p ++ y ++ s →
  ∃ p' s', p = u ++ p' ∧ s = s' ++ u' ∧ x = p' ++ y ++ s'.
Proof.
move=> Hu Hu' /(cut_front Hu) [p' [-> Hx]].
move: Hx; rewrite app_assoc => /(cut_back Hu') [s' [-> ->]].
by exists p', s'; rewrite -app_assoc.
Qed.

Section Invariant.

Context {A : setoid} `{!LeibnizEquiv A, !EqDecision A, !Finite A}.

Local Instance A_countable : Countable A := finite_countable.

Notation W := (list_monoid A).
Notation UT := (@uterm A).
Notation UE := (@ueq A).

Definition cell : Type := (list A * list A)%type.

Implicit Types (u x y t : list A) (ρ : nat → lang W).

(** * Two-ended Post normal systems *)

Definition drule : Type := ((list A * list A) * (list A * list A))%type.

Definition dstep (Rs : list drule) t t' : Prop :=
  ∃ u u' v v' x, ((u, u'), (v, v')) ∈ Rs ∧
    t = u ++ x ++ u' ∧ t' = v ++ x ++ v'.

Implicit Types (c : cell) (r : drule).

(** * Languages over words *)

Lemma in_mul (L1 L2 : lang W) x :
  (L1 ⋅ L2) x ↔ ∃ x1 x2, x = x1 ++ x2 ∧ L1 x1 ∧ L2 x2.
Proof.
split.
- by case=> x1 [x2 [/leibniz_equiv_iff -> ?]]; exists x1, x2.
- by case=> x1 [x2 [-> ?]]; exists x1, x2.
Qed.

Lemma in_one x : (1 : lang W) x ↔ x = [].
Proof. by split => [/leibniz_equiv_iff|-> /=] //; reflexivity. Qed.

Lemma in_sing y x : lang_sing y x ↔ x = y.
Proof. by split => [/leibniz_equiv_iff|-> /=] //; reflexivity. Qed.

Lemma in_join (L1 L2 : lang W) x : (L1 ⊔ L2) x ↔ L1 x ∨ L2 x.
Proof. reflexivity. Qed.

(** * Building blocks of the terms *)

Definition tw (w : list A) : UT := Unit (inl <$> w).
Definition tjoin (es : list UT) : UT := foldr (λ e acc, e ⊔ acc) ⊥ es.

Lemma tjoin_cons e es : tjoin (e :: es) = e ⊔ tjoin es.
Proof. by []. Qed.

Lemma lsubst_unit ρ cs : lsubst ρ (Unit cs) = mul_list (lsym ρ) cs.
Proof. by []. Qed.

Lemma lsubst_join ρ (e1 e2 : UT) :
  lsubst ρ (e1 ⊔ e2) = lsubst ρ e1 ⊔ lsubst ρ e2.
Proof. by []. Qed.

Lemma lsubst_mul ρ (e1 e2 : UT) :
  lsubst ρ (e1 ⋅ e2) = lsubst ρ e1 ⋅ lsubst ρ e2.
Proof. by []. Qed.

Lemma in_tw ρ w x : lsubst ρ (tw w) x ↔ x = w.
Proof.
rewrite /tw lsubst_unit; elim: w x => [|a w IH] x; first exact: in_one.
rewrite fmap_cons mul_list_cons in_mul; split.
- by case=> x1 [x2 [-> [/in_sing -> /IH ->]]].
- move=> ->; exists [a], w; do !split => //; [exact/in_sing | exact/IH].
Qed.

Lemma in_tjoin ρ es x :
  lsubst ρ (tjoin es) x ↔ ∃ e, e ∈ es ∧ lsubst ρ e x.
Proof.
elim: es => [|e es IH].
- by split => [|[e [/elem_of_nil]]].
- rewrite tjoin_cons lsubst_join in_join IH; split.
  + case=> [He|[e' [He' H]]]; first by exists e; split => //; left.
    by exists e'; split => //; right.
  + by case=> e' [/elem_of_cons [->|He'] H]; [left|right; exists e'].
Qed.

Definition in_cell c t : Prop := ∃ y, t = c.1 ++ y ++ c.2.

Definition matches c r : Prop := r.1.1 `prefix_of` c.1 ∧ r.1.2 `suffix_of` c.2.

Local Instance matches_dec c r : Decision (matches c r).
Proof. rewrite /matches; apply _. Defined.

(** * Terms *)

Definition cvar c : nat := encode_nat (Some c).
Definition slack : nat := encode_nat (None : option cell).

Lemma cvar_inj c c' : cvar c = cvar c' → c = c'.
Proof. by move=> /(inj (encode_nat (A := option cell))) [->]. Qed.

Lemma slack_cvar c : slack ≠ cvar c.
Proof. by move=> /(inj (encode_nat (A := option cell))). Qed.

Definition tx (i : nat) : UT := Unit [inr i].

Definition cell_term c : UT := tw c.1 ⋅ tx (cvar c) ⋅ tw c.2.

(* A matching rule `r` applied to the cell `c`. *)
Definition step_term c r : UT :=
  tw (r.2.1 ++ drop (length r.1.1) c.1) ⋅ tx (cvar c) ⋅
  tw (take (length c.2 - length r.1.2) c.2 ++ r.2.2).

Lemma in_tx ρ i x : lsubst ρ (tx i) x ↔ ρ i x.
Proof.
rewrite /tx lsubst_unit mul_list_cons in_mul; split.
- by case=> x1 [x2 [-> [H /in_one ->]]]; rewrite app_nil_r.
- move=> H; exists x, []; rewrite app_nil_r; do !split => //.
  exact/in_one.
Qed.

Lemma in_wxw ρ u i v t :
  lsubst ρ (tw u ⋅ tx i ⋅ tw v) t ↔ ∃ y, t = u ++ y ++ v ∧ ρ i y.
Proof.
rewrite !lsubst_mul in_mul; split.
- case=> t12 [t3 [-> [/in_mul [t1 [t2 [-> [/in_tw -> /in_tx Hy]]]]
                     /in_tw ->]]].
  by exists t2; rewrite -app_assoc.
- case=> y [-> Hy]; exists (u ++ y), v; rewrite -app_assoc; do !split.
  + apply/in_mul; exists u, y; do !split; [exact/in_tw | exact/in_tx].
  + exact/in_tw.
Qed.

Lemma matches_split c r :
  matches c r →
  c.1 = r.1.1 ++ drop (length r.1.1) c.1 ∧
  c.2 = take (length c.2 - length r.1.2) c.2 ++ r.1.2.
Proof.
move: c r => [p s] [[u u'] [v v']] [/= [p' ->] [s' ->]].
by rewrite drop_app_length length_app Nat.add_sub take_app_length.
Qed.

Lemma uvars_tw u : uvars (tw u) = [].
Proof. by rewrite /tw /=; elim: u. Qed.

Lemma uvars_mul (e1 e2 : UT) : uvars (e1 ⋅ e2) = uvars e1 ++ uvars e2.
Proof. by []. Qed.

Lemma uvars_join (e1 e2 : UT) : uvars (e1 ⊔ e2) = uvars e1 ++ uvars e2.
Proof. by []. Qed.

Lemma uvars_cell_term c : uvars (cell_term c) = [cvar c].
Proof. by rewrite /cell_term !uvars_mul !uvars_tw. Qed.

Lemma uvars_step_term c r : uvars (step_term c r) = [cvar c].
Proof. by rewrite /step_term !uvars_mul !uvars_tw. Qed.

(* A join of terms, at most one per cell, each with its cell's variable
   only. *)
Lemma uvars_omap (f : cell → option UT) cs :
  (∀ c e, f c = Some e → uvars e = [cvar c]) → NoDup cs →
  NoDup (uvars (tjoin (omap f cs))) ∧
  ∀ i, i ∈ uvars (tjoin (omap f cs)) → ∃ c, c ∈ cs ∧ i = cvar c.
Proof.
move=> Hf; elim: cs / => [|c cs Hc _ [IH1 IH2]].
  by split => [|i /elem_of_nil]; first constructor.
have -> : omap f (c :: cs) =
          match f c with Some e => e :: omap f cs | None => omap f cs end
  by [].
case Hfc: (f c) => [e|].
- rewrite tjoin_cons uvars_join (Hf _ _ Hfc) /=; split.
  + constructor => // /IH2 [c' [Hc' /cvar_inj Hcc']].
    by apply: Hc; rewrite Hcc'.
  + move=> i /elem_of_cons [->|/IH2 [c' [Hc' ->]]].
    * by exists c; split => //; apply: elem_of_list_here.
    * by exists c'; split => //; apply: elem_of_list_further.
- split => // i /IH2 [c' [Hc' ->]].
  by exists c'; split => //; apply: elem_of_list_further.
Qed.

Lemma star_free_tjoin_all (es : list UT) :
  (∀ e, e ∈ es → star_free e) → star_free (tjoin es).
Proof.
elim: es => //= e es IH H; split.
- exact: H (elem_of_list_here _ _).
- by apply: IH => e' He'; apply: H; apply: elem_of_list_further.
Qed.

(** * The equation *)

Section Eq.

Variables (Rs : list drule) (cells : list cell) (w : list A).

Definition first_rule c : option drule := head (filter (matches c) Rs).

Lemma first_rule_Some c r : first_rule c = Some r → r ∈ Rs ∧ matches c r.
Proof.
rewrite /first_rule => Hr; have := head_Some_elem_of _ _ Hr.
by rewrite elem_of_list_filter => - [].
Qed.

Definition cterm : UT := tjoin (cell_term <$> cells).
Definition sterm : UT := tjoin (omap (λ c, step_term c <$> first_rule c) cells).

Definition cell_lhs : UT := tw w ⊔ sterm ⊔ tx slack.
Definition cell_eq : UE := (cell_lhs, cterm).

Lemma in_cterm ρ t :
  lsubst ρ cterm t ↔ ∃ c y, c ∈ cells ∧ t = c.1 ++ y ++ c.2 ∧ ρ (cvar c) y.
Proof.
rewrite /cterm in_tjoin; split.
- case=> e [/elem_of_list_fmap [c [-> Hc]] /in_wxw [y [-> Hy]]].
  by exists c, y.
- case=> c [y [Hc [-> Hy]]]; exists (cell_term c); split.
  + by apply/elem_of_list_fmap; exists c.
  + by apply/in_wxw; exists y.
Qed.

Lemma in_sterm ρ t :
  lsubst ρ sterm t ↔ ∃ c r y, c ∈ cells ∧ first_rule c = Some r ∧
    ρ (cvar c) y ∧
    t = (r.2.1 ++ drop (length r.1.1) c.1) ++ y ++
        (take (length c.2 - length r.1.2) c.2 ++ r.2.2).
Proof.
rewrite /sterm in_tjoin; split.
- case=> e [/elem_of_list_omap [c [Hc /fmap_Some [r [Hr ->]]]]].
  by case/in_wxw => y [-> Hy]; exists c, r, y.
- case=> c [r [y [Hc [Hr [Hy ->]]]]]; exists (step_term c r); split.
  + by apply/elem_of_list_omap; exists c; rewrite Hr.
  + by apply/in_wxw; exists y.
Qed.

Lemma cell_eq_iff ρ :
  lsubst ρ cell_lhs ≡ lsubst ρ cterm ↔
  ∀ t, (t = w ∨ lsubst ρ sterm t) ∨ ρ slack t ↔ lsubst ρ cterm t.
Proof.
have HL t : lsubst ρ cell_lhs t ↔ (t = w ∨ lsubst ρ sterm t) ∨ ρ slack t
  by rewrite /cell_lhs !lsubst_join !in_join in_tw in_tx.
by split => H t; [rewrite -HL | rewrite HL]; apply: H.
Qed.

Lemma step_of_cell c r y :
  r ∈ Rs → matches c r →
  dstep Rs (c.1 ++ y ++ c.2)
    ((r.2.1 ++ drop (length r.1.1) c.1) ++ y ++
     (take (length c.2 - length r.1.2) c.2 ++ r.2.2)).
Proof.
move: c r => [p s] [[u u'] [v v']] Hr [/= [p' ->] [s' ->]].
rewrite drop_app_length length_app Nat.add_sub take_app_length.
exists u, u', v, v', (p' ++ y ++ s'); rewrite -!app_assoc; by split.
Qed.

Lemma cell_eq_star_free : star_free cell_lhs ∧ star_free cterm.
Proof.
split; last first.
  rewrite /cterm; apply: star_free_tjoin_all => e.
  by case/elem_of_list_fmap => c [-> _].
split => //; split => //; rewrite /sterm.
apply: star_free_tjoin_all => e /elem_of_list_omap [c [_]].
by case/fmap_Some => r [_ ->].
Qed.

(** * Soundness *)

Section Sound.

(* No rule reads beyond a cell, and each cell is matched by at most one
   rule. *)
Hypothesis Hlen : ∀ r c, r ∈ Rs → c ∈ cells →
  length r.1.1 ≤ length c.1 ∧ length r.1.2 ≤ length c.2.
Hypothesis Hdet : ∀ c r1 r2, c ∈ cells → r1 ∈ Rs → r2 ∈ Rs →
  matches c r1 → matches c r2 → r1 = r2.

Lemma first_rule_det c r :
  c ∈ cells → r ∈ Rs → matches c r → first_rule c = Some r.
Proof.
move=> Hc Hr Hm; rewrite /first_rule.
case Hf: (filter (matches c) Rs) => [|r0 rs].
- have : r ∈ filter (matches c) Rs by apply/elem_of_list_filter.
  by rewrite Hf => /elem_of_nil.
- have /first_rule_Some [Hr0 Hm0] : first_rule c = Some r0
    by rewrite /first_rule Hf.
  by rewrite (Hdet Hc Hr0 Hr Hm0 Hm).
Qed.

Variable ρ : nat → lang W.
Hypothesis Hsol : lsolves ρ [cell_eq].

Lemma cell_sol t : (t = w ∨ lsubst ρ sterm t) ∨ ρ slack t ↔ lsubst ρ cterm t.
Proof. by have /cell_eq_iff := Hsol (elem_of_list_here _ _); apply. Qed.

Lemma cell_step t t' : dstep Rs t t' → lsubst ρ cterm t → lsubst ρ cterm t'.
Proof.
case=> u [u' [v [v' [x [Hr [-> ->]]]]]] /in_cterm [c [y [Hc [Ht Hy]]]].
have [Hu Hu'] := Hlen Hr Hc.
have [p' [s' [Hp [Hs ->]]]] := rule_cell Hu Hu' Ht.
have Hm : matches c ((u, u'), (v, v')) by split; [exists p' | exists s'].
apply/cell_sol; left; right; apply/in_sterm.
exists c, ((u, u'), (v, v')), y; do !split => //.
- exact: first_rule_det Hc Hr Hm.
- rewrite /= Hp Hs drop_app_length length_app Nat.add_sub take_app_length.
  by rewrite -!app_assoc.
Qed.

Lemma cell_reach t : rtc (dstep Rs) w t → lsubst ρ cterm t.
Proof.
have Hw : lsubst ρ cterm w by apply/cell_sol; left; left.
move=> Ht; elim: Ht Hw => // t1 t2 t3 H12 _ IH Ht1.
by apply: IH; apply: cell_step H12 Ht1.
Qed.

End Sound.

Theorem cell_sound ρ :
  (∀ r c, r ∈ Rs → c ∈ cells →
     length r.1.1 ≤ length c.1 ∧ length r.1.2 ≤ length c.2) →
  (∀ c r1 r2, c ∈ cells → r1 ∈ Rs → r2 ∈ Rs →
     matches c r1 → matches c r2 → r1 = r2) →
  lsolves ρ [cell_eq] →
  ∀ t, rtc (dstep Rs) w t → ∃ c, c ∈ cells ∧ in_cell c t.
Proof.
move=> Hlen Hdet Hsol t /(cell_reach Hlen Hdet Hsol).
by case/in_cterm => c [y [Hc [-> _]]]; exists c; split => //; exists y.
Qed.

(** * Completeness *)

Section Complete.

Variable L : list (list A).
Hypothesis Hw : w ∈ L.
Hypothesis Hclosed : ∀ t t', t ∈ L → dstep Rs t t' → t' ∈ L.
Hypothesis Hcover : ∀ t, t ∈ L → ∃ c, c ∈ cells ∧ in_cell c t.

Definition maxlen : nat := list_max (length <$> L).

(* The two-sided derivative of `L`, as a list of words. *)
Definition deriv p s : list (list A) :=
  filter (λ x, p ++ x ++ s ∈ L) (enum_list_lt (S maxlen)).

Lemma elem_of_deriv p s x : x ∈ deriv p s ↔ p ++ x ++ s ∈ L.
Proof.
rewrite /deriv elem_of_list_filter elem_of_enum_list_lt; split; first by case.
move=> Ht; split => //.
have Hmax : ∀ n, n ∈ length <$> L → n ≤ maxlen.
{ rewrite -Forall_forall; exact: (proj1 (list_max_le _ _) (le_n _)). }
have := Hmax (length (p ++ x ++ s)) (elem_of_list_fmap_1 _ _ _ Ht).
rewrite /maxlen !length_app; lia.
Qed.

Definition fC (i : nat) : ka_term W :=
  match decode_nat i : option (option cell) with
  | Some (Some c) => ⨆ y ∈ deriv c.1 c.2, Unit y
  | Some None => ⨆ t ∈ L, Unit t
  | None => ⊥
  end.

Lemma fC_star_free i : star_free (fC i).
Proof.
rewrite /fC; case: (decode_nat i) => [[c|]|] //; exact: star_free_join_list.
Qed.

Lemma l_fC_cell c y : l (fC (cvar c)) y ↔ c.1 ++ y ++ c.2 ∈ L.
Proof.
rewrite /fC /cvar decode_encode_nat.
rewrite (semi_lattice_morphism_join_list (f := @l W)) elem_of_lang_join_list.
split.
- by case=> y' [/elem_of_deriv Hy /in_sing ->].
- by move=> Hy; exists y; split; [exact/elem_of_deriv | exact/in_sing].
Qed.

Lemma l_fC_slack t : l (fC slack) t ↔ t ∈ L.
Proof.
rewrite /fC /slack decode_encode_nat.
rewrite (semi_lattice_morphism_join_list (f := @l W)) elem_of_lang_join_list.
split.
- by case=> t' [Ht /in_sing ->].
- by move=> Ht; exists t; split => //; exact/in_sing.
Qed.

Lemma cell_lsolves : lsolves (λ i, l (fC i)) [cell_eq].
Proof.
move=> q /elem_of_list_singleton ->; apply/cell_eq_iff => t.
have -> : lsubst (λ i, l (fC i)) cterm t ↔ t ∈ L.
{ rewrite in_cterm; split.
  - by case=> c [y [_ [-> /l_fC_cell]]].
  - move=> Ht; have [c [Hc [y Hy]]] := Hcover Ht.
    by exists c, y; do !split => //; apply/l_fC_cell; rewrite -Hy. }
split.
- case=> [[->|]|/l_fC_slack] //.
  case/in_sterm => c [r [y [_ [/first_rule_Some [Hr Hm] [/l_fC_cell Hy ->]]]]].
  by apply: Hclosed Hy _; apply: step_of_cell.
- by move=> Ht; right; apply/l_fC_slack.
Qed.

End Complete.

Theorem cell_complete (L : list (list A)) :
  w ∈ L → (∀ t t', t ∈ L → dstep Rs t t' → t' ∈ L) →
  (∀ t, t ∈ L → ∃ c, c ∈ cells ∧ in_cell c t) →
  unif preka_eqv [cell_eq].
Proof.
move=> Hw Hclosed Hcover.
apply: (unif_of_lsolves (f := fC L)).
- exact: fC_star_free.
- by move=> q /elem_of_list_singleton ->; exact: cell_eq_star_free.
- exact: cell_lsolves.
Qed.

(** * Linearity *)

Theorem cell_eq_side_linear : NoDup cells → side_linear cell_eq.
Proof.
move=> Hnd.
have Hstep c e : step_term c <$> first_rule c = Some e → uvars e = [cvar c]
  by case/fmap_Some => r [_ ->]; exact: uvars_step_term.
have Hcell c e : Some (cell_term c) = Some e → uvars e = [cvar c]
  by case=> <-; exact: uvars_cell_term.
have [HS1 HS2] := uvars_omap Hstep Hnd.
have [HT _] := uvars_omap Hcell Hnd.
split; [change (NoDup (uvars cell_lhs)) | change (NoDup (uvars cterm))].
- rewrite /cell_lhs !uvars_join uvars_tw app_nil_l.
  apply/NoDup_app; do !split => //; last exact: NoDup_singleton.
  move=> i /HS2 [c [_ ->]] /elem_of_list_singleton Hc.
  exact: slack_cvar c (eq_sym Hc).
- by rewrite /cterm fmap_as_omap.
Qed.

End Eq.

End Invariant.
