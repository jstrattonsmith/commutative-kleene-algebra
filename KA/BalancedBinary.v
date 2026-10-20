(* Transporting balanced universality (KA/balanced.v) from `list T * nat`
   to the fixed binary carrier `list bool * nat`.

   Letters are encoded by an injective `enc : T → list bool` of fixed
   length `k > 0`, and weights are scaled by `k`, so that the monoid
   morphism `phi (w, n) = (encw w, k * n)` sends balanced words to balanced
   words. The image of `bal_star` only contains words made of whole valid
   blocks, so the binary upper bound adds two detectors:

   - `bad`: a run of valid blocks followed by an invalid block (a length-k
     word outside the image of `enc`), padded with the binary `bal_star`;
   - `partial`: whole blocks followed by an incomplete final block, which
     only matters for short words.

   For an upper bound of the shape `E ⊔ P ⋅ bal_star` over `T`,
   `bin_ub E P := Phi E ⊔ (Phi P ⊔ bad) ⋅ bal_star ⊔ partial`. The two
   theorems reduce binary universality to the language-level facts that
   KA/balanced.v's `bal_univ_complete` consumes (`bin_complete`), and give
   back membership of every balanced word over `T` (`bin_sound`). *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite.
From Stdlib Require Import Lia Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.balanced.

(* See KA/balanced.v: a bare `1` would be the unit of the additive `nat`
   monoid. *)
Local Open Scope nat_scope.

(** Binary words of a given length. *)

Fixpoint bwords (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n => (cons true <$> bwords n) ++ (cons false <$> bwords n)
  end.

Lemma elem_of_bwords n b : b ∈ bwords n ↔ length b = n.
Proof.
elim: n b => [|n IH] [|x b] /=.
- by rewrite elem_of_list_singleton.
- by rewrite elem_of_list_singleton.
- rewrite elem_of_app !elem_of_list_fmap.
  by split => // - [[? [? _]]|[? [? _]]].
- rewrite elem_of_app !elem_of_list_fmap; split.
  + by case=> - [b' [[_ ->] /IH ->]].
  + case=> /IH Hb; case: x; [left|right]; by exists b.
Qed.

Section BalancedBinary.

Context {T : setoid} `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Variable enc : T → list bool.
Variable k : nat.
Hypothesis enc_inj : ∀ x y, enc x = enc y → x = y.
Hypothesis enc_len : ∀ x, length (enc x) = k.
Hypothesis k_pos : 0 < k.

Notation MT := (prod_monoid (list_monoid T) nat_add_monoid).
Notation MB := (prod_monoid (list_monoid bool_setoid) nat_add_monoid).
Notation bstarT := (bal_star (A := T)).
Notation bstarB := (bal_star (A := bool_setoid)).
Notation balB := (bal (A := bool_setoid)).

Implicit Types (w v : list T) (u b r : list bool).

(** ** The encoding *)

Definition encw w : list bool := concat (enc <$> w).

Lemma encw_app w v : encw (w ++ v) = encw w ++ encw v.
Proof. by rewrite /encw fmap_app concat_app. Qed.

Lemma encw_cons t w : encw (t :: w) = enc t ++ encw w.
Proof. by []. Qed.

Lemma encw_length w : length (encw w) = k * length w.
Proof.
elim: w => [|t w IH]; first by rewrite /= Nat.mul_0_r.
by rewrite encw_cons length_app enc_len IH /=; lia.
Qed.

Lemma encw_prefix w v u :
  encw w = encw v ++ u → ∃ w2, w = v ++ w2 ∧ u = encw w2.
Proof.
elim: v w => [|t v IH] w; first by exists w.
case: w => [|t' w]; rewrite !encw_cons.
- move=> /(f_equal length); rewrite !length_app enc_len; simpl; lia.
- rewrite -app_assoc => /app_inj_1 [].
    by rewrite !enc_len.
  move=> /enc_inj -> /IH [w2 [-> ->]].
  by exists w2.
Qed.

Lemma encw_inj w v : encw w = encw v → w = v.
Proof.
move=> E; have [w2 [-> E2]] : ∃ w2, w = v ++ w2 ∧ [] = encw w2.
{ by apply: encw_prefix; rewrite app_nil_r. }
case: w2 E2 => [|t w2]; first by rewrite app_nil_r.
by rewrite encw_cons => /(f_equal length); rewrite length_app enc_len /=; lia.
Qed.

Lemma mul_k_inj (x y : nat) : k * x = k * y → x = y.
Proof.
move=> H; have Hk : k ≠ 0 by lia.
exact: (proj1 (Nat.mul_cancel_l x y k Hk) H).
Qed.

Definition phi (x : MT) : MB := (encw x.1, k * x.2).

Global Instance phi_morphism : MonoidMorphism phi.
Proof.
split.
- by move=> x y /M_equiv_eq ->.
- by apply: M_eq_equiv; rewrite /phi /= Nat.mul_0_r.
- case=> w1 n1 [w2 n2]; apply: M_eq_equiv.
  rewrite /phi M_mulE /= M_mulE encw_app; f_equal; lia.
Qed.

Definition Phi : ka_term MT → ka_term MB := ka_term_map phi.

Lemma l_Phi e u m :
  l (Phi e) (u, m) ↔ ∃ w n, u = encw w ∧ m = k * n ∧ l e (w, n).
Proof.
rewrite /Phi l_natural /=; split.
- case=> - [w n] [/M_equiv_eq [-> ->] H]; by exists w, n.
- case=> w [n [-> [-> H]]]; by exists (w, n).
Qed.

(** ** The binary detectors *)

Definition img : list (list bool) := enc <$> enum T.

Lemma elem_of_img b : b ∈ img ↔ ∃ t, b = enc t.
Proof.
rewrite /img elem_of_list_fmap; split.
- by case=> t [-> _]; exists t.
- by case=> t ->; exists t; split => //; exact: elem_of_enum.
Qed.

Definition blocks : ka_term MB := star (⨆ t ∈ enum T, Unit (enc t, k)).

Definition bad_blk : ka_term MB :=
  ⨆ b ∈ bwords k, if bool_decide (b ∈ img) then ⊥ else balB b.

Definition bad : ka_term MB := blocks ⋅ bad_blk.

Definition anyblk : ka_term MB := star (⨆ b ∈ bwords k, balB b).

Definition partial : ka_term MB :=
  anyblk ⋅ (⨆ j ∈ seq 1 (k - 1), ⨆ r ∈ bwords j, balB r).

Definition bin_ub (E P : ka_term MT) : ka_term MB :=
  Phi E ⊔ (Phi P ⊔ bad) ⋅ bstarB ⊔ partial.

Lemma l_join_list_iff {I} (f : I → ka_term MB) xs y :
  l (join_list f xs) y ↔ ∃ x, x ∈ xs ∧ l (f x) y.
Proof. by rewrite semi_lattice_morphism_join_list elem_of_lang_join_list. Qed.

Lemma l_join (X Y : ka_term MB) y : l (X ⊔ Y) y ↔ l X y ∨ l Y y.
Proof. by []. Qed.

Lemma l_joinT (X Y : ka_term MT) y : l (X ⊔ Y) y ↔ l X y ∨ l Y y.
Proof. by []. Qed.

Lemma l_balB b' u m : l (balB b') (u, m) ↔ u = b' ∧ m = length b'.
Proof. by split => [/M_equiv_eq [-> ->]|[-> ->]]. Qed.

Lemma l_blocks u m : l blocks (u, m) ↔ ∃ w, u = encw w ∧ m = k * length w.
Proof.
split.
- move: u m; apply: l_star_elim; first by exists []; split => //; lia.
  move=> u1 m1 u2 m2 /l_join_list_iff [t [_ /M_equiv_eq [-> ->]]].
  case=> w [-> ->]; exists (t :: w); split => //=; lia.
- case=> w [-> ->]; elim: w => [|t w IH] /=.
    by rewrite Nat.mul_0_r; apply: l_star_nil.
  have -> : k * S (length w) = k + k * length w by lia.
  apply: l_star_cons IH; apply/l_join_list_iff; exists t.
  by split; [exact: elem_of_enum|].
Qed.

Lemma l_bad u m :
  l bad (u, m) →
  ∃ w b, u = encw w ++ b ∧ length b = k ∧ b ∉ img.
Proof.
case/l_pair_mul_inv => u1 [m1 [b [m2 [-> [_ [/l_blocks [w [-> _]] Hb]]]]]].
case/l_join_list_iff: Hb => b' [/elem_of_bwords Hb'].
case: bool_decide_reflect => Himg; first by case.
by case/l_balB => -> _; exists w, b'.
Qed.

Lemma l_bad_intro w b :
  length b = k → b ∉ img → l bad (encw w ++ b, length (encw w ++ b)).
Proof.
move=> Hb Himg; rewrite length_app.
apply: l_pair_mul_intro; first by apply/l_blocks; exists w; rewrite encw_length.
apply/l_join_list_iff; exists b; split; first exact/elem_of_bwords.
by case: bool_decide_reflect => // _; apply/l_balB.
Qed.

Lemma l_anyblk u m : l anyblk (u, m) → ∃ j, length u = k * j.
Proof.
move: u m; apply: l_star_elim; first by exists 0; simpl; lia.
move=> u1 m1 u2 m2 /l_join_list_iff [b [/elem_of_bwords Hb /l_balB [-> _]]].
by case=> j Hj; exists (S j); rewrite length_app Hj Hb; lia.
Qed.

Lemma l_anyblk_intro j u : length u = k * j → l anyblk (u, length u).
Proof.
elim: j u => [|j IH] u Hu.
  have -> : u = [] by apply/length_zero_iff_nil; lia.
  exact: l_star_nil.
rewrite -(take_drop k u) length_app.
apply: l_star_cons; last by apply: IH; rewrite length_drop; lia.
apply/l_join_list_iff; exists (take k u); split; last exact/l_balB.
by apply/elem_of_bwords; rewrite length_take; lia.
Qed.

(* Every binary word is valid blocks followed either by an invalid block or
   by fewer than `k` letters. *)
Lemma decomp u :
  (∃ w b z, u = encw w ++ b ++ z ∧ length b = k ∧ b ∉ img) ∨
  (∃ w r, u = encw w ++ r ∧ length r < k).
Proof.
move: {2}(length u) (eq_refl (length u)) => n.
elim/lt_wf_ind: n u => n IH u Hn.
case: (decide (length u < k)) => Hlt; first by right; exists [], u.
have Hu : u = take k u ++ drop k u by rewrite take_drop.
have Hb : length (take k u) = k by rewrite length_take; lia.
case: (decide (take k u ∈ img)) => Himg; last first.
  by left; exists [], (take k u), (drop k u).
case/elem_of_img: Himg => t Ht.
have Hlen : length (drop k u) < n by rewrite length_drop; lia.
case: (IH _ Hlen (drop k u) eq_refl) =>
  [[w [b [z [Ez [Hb' Hi]]]]]|[w [r [Er Hr]]]].
- left; exists (t :: w), b, z; split => //.
  by rewrite Hu Ez Ht /= -app_assoc.
- right; exists (t :: w), r; split => //.
  by rewrite Hu Er Ht /= -app_assoc.
Qed.

(** ** Transport *)

Theorem bin_complete (E P : ka_term MT) D :
  (∀ w, length w < D → l (E ⊔ P ⋅ bstarT) (w, length w)) →
  (∀ w, length w = D → ∃ w1 w2, w = w1 ++ w2 ∧ l P (w1, length w1)) →
  bstarB ⊑ bin_ub E P.
Proof.
move=> Hshort Hlong.
have Hpre : ∀ u1 m1 u2,
    l (Phi P ⊔ bad) (u1, m1) → m1 = length u1 →
    l (bin_ub E P) (u1 ++ u2, length (u1 ++ u2)).
{ move=> u1 m1 u2 H Hm; subst m1; rewrite length_app.
  apply/l_join; left; apply/l_join; right.
  by apply: l_pair_mul_intro => //; apply/l_bal_star. }
apply: (bal_univ_complete (Pre := Phi P ⊔ bad) (D := k * D)).
- rewrite /bin_ub.
  trans (Phi E ⊔ (Phi P ⊔ bad) ⋅ bstarB); last exact: sqsubseteq_join_left.
  exact: sqsubseteq_join_right.
- move=> u Hu; case: (decomp u) =>
    [[w [b [z [Eu [Hb Hi]]]]]|[w [r [Eu Hr]]]]; subst u.
  + rewrite app_assoc; apply: (Hpre _ (length (encw w ++ b))) => //.
    by apply/l_join; right; apply: l_bad_intro.
  + case: r Hr Hu => [|x r] Hr Hu.
    * rewrite app_nil_r encw_length.
      have Hw : length w < D.
      { move: Hu; rewrite length_app encw_length /= => Hu.
        nia. }
      case/l_joinT: (Hshort w Hw) => [HE|HP].
      -- apply/l_join; left; apply/l_join; left.
         by apply/l_Phi; exists w, (length w).
      -- case/l_pair_mul_inv: HP =>
           w1 [n1 [w2 [n2 [Ew [En [H1 /l_bal_star Hn2]]]]]].
         rewrite Ew encw_app; apply/l_join; left; apply/l_join; right.
         have -> : k * length (w1 ++ w2) = k * n1 + length (encw w2).
         { simpl in Hn2; rewrite Ew length_app in En.
           rewrite encw_length length_app; nia. }
         apply: l_pair_mul_intro; last exact/l_bal_star.
         by apply/l_join; left; apply/l_Phi; exists w1, n1.
    * apply/l_join; right; rewrite length_app.
      apply: l_pair_mul_intro; first exact: (l_anyblk_intro (j := length w))
        (encw_length w).
      apply/l_join_list_iff; exists (length (x :: r)).
      split; first by apply/elem_of_seq; simpl in *; lia.
      apply/l_join_list_iff; exists (x :: r).
      by split; [exact/elem_of_bwords|exact/l_balB].
- move=> u Hu; case: (decomp u) =>
    [[w [b [z [Eu [Hb Hi]]]]]|[w [r [Eu Hr]]]]; subst u.
  + exists (encw w ++ b), z; split; first by rewrite app_assoc.
    by apply/l_join; right; apply: l_bad_intro.
  + move: Hu; rewrite length_app encw_length => Hu.
    have Hr' : @length (setoid_car bool_setoid) r < k := Hr.
    have Ew : length w = D.
    { case: (Nat.lt_trichotomy (length w) D) => [H|[H|H]] //.
      - by have := Nat.mul_le_mono_l _ _ k H; rewrite Nat.mul_succ_r; lia.
      - by have := Nat.mul_le_mono_l _ _ k H; rewrite Nat.mul_succ_r; lia. }
    have Er : r = [].
    { rewrite Ew in Hu; have Hz : @length (setoid_car bool_setoid) r = 0 by lia.
      by destruct r. }
    subst r; case: (Hlong w Ew) => w1 [w2 [-> H1]].
    exists (encw w1), (encw w2); split; first by rewrite app_nil_r encw_app.
    apply/l_join; left; apply/l_Phi; exists w1, (length w1).
    by rewrite encw_length.
Qed.

(* Only the balanced words of `bin_ub E P` matter, so soundness also holds
   for any upper bound whose balanced words are those of `bin_ub E P`. *)
Theorem bin_sound_lang (E P : ka_term MT) :
  (∀ u, l (bin_ub E P) (u, length u)) →
  ∀ w, l (E ⊔ P ⋅ bstarT) (w, length w).
Proof.
move=> H w; have := H (encw w); rewrite encw_length.
case/l_join => [/l_join [HE|HP]|HPart].
- apply/l_joinT; left; case/l_Phi: HE => w' [n [/encw_inj -> [En HE]]].
  by have <- : n = length w' by apply: mul_k_inj; lia.
- apply/l_joinT; right; case/l_pair_mul_inv: HP =>
    u1 [m1 [u2 [m2 [Ew [Em [H1 /l_bal_star Hm2]]]]]]; simpl in Hm2.
  case/l_join: H1 => [/l_Phi [v [n [Eu1 [Em1 Hv]]]]|/l_bad].
  + subst u1; case/encw_prefix: Ew => w2 [Ew Eu2]; subst w.
    have Hn : length (v ++ w2) = n + length w2.
    { rewrite Eu2 encw_length in Hm2.
      apply: mul_k_inj; rewrite Nat.mul_add_distr_l; lia. }
    rewrite Hn; apply: l_pair_mul_intro => //; exact/l_bal_star.
  + case=> v [b [Eu1 [Hb Hi]]]; exfalso.
    move: Ew; rewrite Eu1 -app_assoc => /encw_prefix [[|t w2] [_ E2]] /=.
    * by move: E2 => /(f_equal length); rewrite length_app /=; lia.
    * move: E2 => /= /app_inj_1 [].
        by rewrite enc_len.
      move=> Ebt _; apply: Hi; apply/elem_of_img; by exists t.
- exfalso; case/l_pair_mul_inv: HPart =>
    u1 [m1 [r [m2 [Ew [_ [/l_anyblk [j Hj] Hr]]]]]].
  case/l_join_list_iff: Hr => i [/elem_of_seq Hi /l_join_list_iff].
  case=> r' [/elem_of_bwords Hr' /l_balB [Er _]]; subst r'.
  move: (f_equal length Ew); rewrite length_app encw_length Hj => El.
  have Hr2 : @length (setoid_car bool_setoid) r = i := Hr'.
  case: (Nat.le_gt_cases (length w) j) => Hwj.
  + have := Nat.mul_le_mono_l _ _ k Hwj; lia.
  + have := Nat.mul_le_mono_l _ _ k Hwj; rewrite Nat.mul_succ_r; lia.
Qed.

Theorem bin_sound (E P : ka_term MT) :
  bstarB ⊑ bin_ub E P → ∀ w, l (E ⊔ P ⋅ bstarT) (w, length w).
Proof. by move=> H; apply: bin_sound_lang => u; exact: bal_univ_sound. Qed.

End BalancedBinary.
