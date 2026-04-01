Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite gmap mapset.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import utils algebra pre_ka lang automata.

Section RepresentableRelations.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Implicit Types (e : ka_term (list T * list T)) (L : ka_term (list T)).
Implicit Types (s : list T).

Local Lemma list_mul_app (a b : list T) : a ⋅ b = a ++ b.
Proof. reflexivity. Qed.

Definition dpseudo_top : ka_term (list T * list T) :=
  ka_term_diag pseudo_top.

Definition mismatch : ka_term (list T * list T) :=
  let diffs :=
    filter (λ '(x, y), bool_decide (x ≠ y))
      (enum (T * T)) in
  join_list (λ '(x, y), Unit ([x], [y])) diffs.

(** Lemma 33 (normal form): If two lists diverge (share a common prefix
    then have different next characters), their pairing factors through diff. *)

Lemma dpseudo_top_absorb s : Unit (s, s) ⋅ dpseudo_top ⊑ dpseudo_top.
Proof.
have -> : Unit (s, s) ≡ ka_term_diag (Unit s) by [].
by rewrite -monoid_morphism_mul pseudo_top_absorb.
Qed.

Lemma dpseudo_top_absorb_list (σ : list (list T)) :
  (⨆ xs ∈ σ, Unit (xs, xs)) ⋅ dpseudo_top ⊑ dpseudo_top.
Proof.
rewrite /= join_list_left_dist join_list_sqsubseteq.
move=> xs xs_σ.
have -> : Unit (xs, xs) ≡ ka_term_diag (Unit xs)
  by [].
by rewrite -monoid_morphism_mul pseudo_top_absorb.
Qed.

Lemma unit_le_mismatch (x x' : T) :
  x ≠ x' → Unit ([x], [x']) ⊑ mismatch.
Proof.
move=> Hne. rewrite /mismatch.
have H : (x, x') ∈ filter
  (λ '(x, y), bool_decide (x ≠ y))
  (enum (T * T)).
{ apply/elem_of_list_filter; split;
    last exact: elem_of_enum.
  by apply/Is_true_true/bool_decide_eq_true. }
exact: sqsubseteq_join_list _ _ _ H.
Qed.

Lemma le_mismatch_conv s s' :
  Unit (s, s') ⊑ mismatch →
  ∃ x x', x ≠ x' ∧ s = [x] ∧ s' = [x'].
Proof.
move=> /l_alt.
rewrite /mismatch semi_lattice_morphism_join_list.
rewrite elem_of_lang_join_list.
case=> [[x y]] [Hf /= /leibniz_equiv_iff
  [-> ->]].
exists x, y; repeat split.
by move: Hf => /elem_of_list_filter
  [/Is_true_true /bool_decide_eq_true].
Qed.

Lemma sqsubseteq_dpseudo_top s s' :
  Unit (s, s') ⊑ dpseudo_top ↔ s = s'.
Proof.
rewrite /dpseudo_top ka_term_diag_spec; split.
- move=> [Heq _]; apply leibniz_equiv in Heq; exact Heq.
- move=> ->; split; first reflexivity.
  exact: unit_le_pseudo_top.
Qed.

Lemma mismatch_unit (x x' : T) :
  x ≠ x' → Unit ([x], [x']) ⊑ dpseudo_top ⋅ mismatch.
Proof.
move=> Hne.
rewrite -(left_id 1 (⋅) (Unit ([x], [x']))).
apply: pre_ka_mul_mono; last exact: unit_le_mismatch Hne.
have -> : (1 : ka_term _) ≡ ka_term_diag (1 : ka_term (list T)) by [].
rewrite -monoid_morphism_one.
exact: semi_lattice_morphism_sqsubseteq_proper (pre_ka_one_star _).
Qed.

(* TODO: Find better name *)
Lemma list_diverge s s' :
  ¬ (∃ t, s' = s ++ t) →
  ¬ (∃ t, s = s' ++ t) →
  Unit (s, s') ⊑ dpseudo_top ⋅ mismatch ⋅ pseudo_top.
Proof.
elim: s s' => [|x s IH] [|x' s'] Hns Hns'.
- exfalso. apply: Hns. by exists [].
- exfalso. apply: Hns. by exists (x' :: s').
- exfalso. apply: Hns'. by exists (x :: s).
- case: (decide (x = x')) Hns Hns' => [-> Hns Hns'|Hne Hns Hns'].
  + (* Same head: recurse *)
    have Hns1 : ¬ (∃ t, s' = s ++ t).
    { move=> [t Ht]; apply: Hns; exists t; rewrite /mul /= Ht //. }
    have Hns1' : ¬ (∃ t, s = s' ++ t).
    { move=> [t Ht]; apply: Hns'; exists t; rewrite /mul /= Ht //. }
    (* Unit(x::s, x::s') = Unit([x],[x]) ⋅ Unit(s, s') *)
    have Hsplit : Unit (x' :: s, x' :: s') ≡ Unit ([x'], [x']) ⋅ Unit (s, s').
    { have -> : (x' :: s, x' :: s') = ([x'], [x']) ⋅ (s, s') by done.
      by rewrite monoid_morphism_mul. }
    etransitivity.
    { rewrite Hsplit. reflexivity. }
    etransitivity.
    { apply: pre_ka_mul_mono; [reflexivity | exact: IH _ Hns1 Hns1']. }
    by rewrite !assoc dpseudo_top_absorb.
  + (* Different heads: divergence *)
    have Hsplit : Unit (x :: s, x' :: s') ≡ Unit ([x], [x']) ⋅ Unit (s, s').
    { have -> : (x :: s, x' :: s') = ([x], [x']) ⋅ (s, s') by done.
      by rewrite monoid_morphism_mul. }
    etransitivity.
    { rewrite Hsplit. reflexivity. }
    apply: pre_ka_mul_mono.
    * exact: mismatch_unit Hne.
    * exact: unit_le_pseudo_top.
Qed.

(** A pair (s, s ++ suffix) where s is a strict prefix
    cannot be in dpseudo_top ⋅ mismatch ⋅ pseudo_top:
    mismatch forces differing characters at the same
    position, but a prefix relation has none. *)

Lemma prefix_not_in_mismatch s suffix :
  suffix ≠ [] →
  ¬ Unit (s, s ++ suffix) ⊑ dpseudo_top ⋅ mismatch ⋅ pseudo_top.
Proof.
move=> Hne /l_alt /=.
case=> [[ab1 ab2] [[c1 c2]
  [Eabc [[[a1 a2] [[b1 b2] [Eab [Ha Hb]]]] _]]]].
change (l dpseudo_top (a1, a2)) in Ha.
change (l mismatch (b1, b2)) in Hb.
move: Eabc => /leibniz_equiv_iff [/= Esl Esr].
move: Eab => /leibniz_equiv_iff [/= Eab1 Eab2].
move: Ha => /l_alt /sqsubseteq_dpseudo_top ?; subst a2.
move: Hb => /l_alt /le_mismatch_conv
  [x [y [Hxy [? ?]]]]; subst b1 b2.
subst ab1 ab2; apply: Hxy.
rewrite !list_mul_app in Esl Esr |- *.
move: Esr; rewrite Esl.
by rewrite -!app_assoc /= app_inv_head_iff => -[].
Qed.

Lemma in_dpseudo_top_inj2 sl sr (e : ka_term (list T)) :
  Unit (sl, sr) ⊑ dpseudo_top ⋅ ka_term_inj2 e →
  ∃ suffix, sr = sl ++ suffix ∧ Unit suffix ⊑ e.
Proof.
move=> /l_alt /=.
case=> [[a1 a2] [[b1 b2] [Eabc [Ha Hb]]]].
change (l dpseudo_top (a1, a2)) in Ha.
change (l (ka_term_inj2 e) (b1, b2)) in Hb.
move: Eabc => /leibniz_equiv_iff [/= Esl Esr].
move: Ha => /l_alt /sqsubseteq_dpseudo_top ?; subst a2.
rewrite l_natural in Hb.
case: Hb => [t [/leibniz_equiv_iff [/= ? ?] /l_alt He]].
subst b1 b2.
rewrite !list_mul_app List.app_nil_r in Esl.
rewrite !list_mul_app in Esr.
by subst sl sr; exists t.
Qed.

(** Lifting a finite set of strings to a KA term. *)

Definition strings_r (σ : list (list T))
    : ka_term (list T * list T) :=
  ⨆ xs ∈ σ, Unit (1, xs).

Lemma strings_r_alt σ :
  strings_r σ ≡ ka_term_inj2 (join_list Unit σ).
Proof.
by rewrite semi_lattice_morphism_join_list.
Qed.

Local Lemma unit_le_join_cases
  (x : list T * list T) e1 e2 :
  Unit x ⊑ e1 ⊔ e2 →
  Unit x ⊑ e1 ∨ Unit x ⊑ e2.
Proof.
move=> Hle.
have /= [H|H] := proj2 (l_alt _ _) Hle;
  [left | right]; exact: proj1 (l_alt _ _) H.
Qed.

Lemma repr_rel_soundness xs ys L ρ :
  Unit (xs, xs ++ ys) ⊑
  dpseudo_top ⋅ ka_term_inj2 L ⊔ dpseudo_top ⋅ mismatch ⋅ ρ →
  Unit ys ⊑ L.
Proof.
move=> /unit_le_join_cases [H|H].
- case/in_dpseudo_top_inj2: H => suffix [Hsr Hle].
  have ? : ys = suffix by apply (app_inv_head xs); rewrite Hsr.
  by subst suffix.
- exfalso; move: H => /l_alt /=.
  case=> [[ab1 ab2] [[c1 c2]
    [Eabc [[[a1 a2] [[b1 b2]
      [Eab [Ha Hb]]]] _]]]].
  change (l dpseudo_top (a1, a2)) in Ha.
  change (l mismatch (b1, b2)) in Hb.
  move: Eabc =>
    /leibniz_equiv_iff [/= Esl Esr].
  move: Eab =>
    /leibniz_equiv_iff [/= Eab1 Eab2].
  move: Ha =>
    /l_alt /sqsubseteq_dpseudo_top ?; subst a2.
  move: Hb => /l_alt /le_mismatch_conv
    [x [y [Hxy [? ?]]]]; subst b1 b2.
  subst ab1 ab2; apply: Hxy.
  rewrite !list_mul_app in Esl Esr |- *.
  move: Esr; rewrite Esl.
  by rewrite -!app_assoc /= app_inv_head_iff
    => -[].
Qed.

Local Lemma rtc_prefix xs ys e :
  rtc (λ xs' ys', Unit (xs', ys') ⊑ e) xs ys →
  ∃ zs, Unit (zs, zs ++ ys) ⊑ Unit (1, xs) ⋅ star e.
Proof.
elim.
- move=> x; exists [].
  rewrite -{1}[Unit _](right_id 1).
  apply: pre_ka_mul_mono => //.
  exact: pre_ka_one_star.
- move=> z1 z2 z3 Hz12 _ [zs IH].
  exists (z1 ++ zs).
  have -> : (z1 ++ zs, (z1 ++ zs) ++ z3) =
    ((z1, z1) : list T * list T) ⋅ (zs, zs ++ z3).
  { change ((z1 ++ zs, (z1 ++ zs) ++ z3) =
      (z1 ⋅ zs, z1 ⋅ (zs ++ z3))).
    by rewrite !list_mul_app -app_assoc. }
  rewrite monoid_morphism_mul.
  etransitivity.
  { apply: pre_ka_mul_mono;
      [reflexivity | exact: IH]. }
  rewrite assoc -monoid_morphism_mul.
  have -> : (z1, z1) ⋅ (1, z2) =
    ((1, z1) : list T * list T) ⋅ (z1, z2).
  { change ((z1 ⋅ (1 : list T), z1 ⋅ z2) =
      ((1 : list T) ⋅ z1, z1 ⋅ z2)).
    by rewrite !list_mul_app app_nil_r. }
  rewrite monoid_morphism_mul -assoc.
  apply: pre_ka_mul_mono; first reflexivity.
  etransitivity.
  { apply: pre_ka_mul_mono;
      [exact: Hz12 | reflexivity]. }
  exact: pre_ka_mul_star.
Qed.

Lemma repr_rel_rtc_soundness xs ys e σ ρ :
  rtc (λ xs' ys', Unit (xs', ys') ⊑ e) xs ys →
  Unit (1, xs) ⋅ star e ⊑
  dpseudo_top ⋅ ka_term_inj2 σ ⊔ dpseudo_top ⋅ mismatch ⋅ ρ →
  Unit ys ⊑ σ.
Proof.
move=> /rtc_prefix [zs Hzs] Hle.
exact: repr_rel_soundness (transitivity Hzs Hle).
Qed.

Record repr_rel e L : Type := {
  repr_rel_dom : ka_term_proj1 e ⊑ L;
  repr_rel_cod : ka_term_proj2 e ⊑ L;
  next : list T → list (list T);
  next_spec : ∀ sl sr, sr ∈ next sl ↔ Unit (sl, sr) ⊑ e;
  residue : ka_term (list T * list T);
  expand_rel :
    ∀ xs : list T,
      Unit xs ⊑ L →
      Unit (1, xs) ⋅ e ⊑
        Unit (xs, xs) ⋅ strings_r (next xs)
        ⊔ dpseudo_top ⋅ mismatch ⋅ residue;
}.

(** Next function: image of a set of strings under a representable relation. *)

Section ReprRelIteration.

Variable e : ka_term (list T * list T).
Variable L : ka_term (list T).
Variable R : repr_rel e L.

Definition next_set (σ : list (list T)) : list (list T) :=
  flat_map (next R) σ.

Definition next_iter (n : nat) (σ : list (list T)) : list (list T) :=
  Nat.iter n next_set σ.

Fixpoint next_lt (n : nat) (σ : list (list T)) : list (list T) :=
  match n with
  | 0 => []
  | S n => next_lt n σ ++ next_iter n σ
  end.

Definition repr_rel_rtc_error : ka_term (list T * list T) :=
  dpseudo_top ⋅ mismatch ⋅ residue R ⋅ star e.

(** Helper: strings_r distributes over append. *)

Lemma strings_r_app (σ1 σ2 : list (list T)) :
  strings_r (σ1 ++ σ2) ≡
    strings_r σ1 ⊔ strings_r σ2.
Proof. by rewrite /strings_r join_list_app. Qed.

(** Helper: expand_rel summed over a list of strings. *)

Lemma expand_rel_sum (σ : list (list T)) :
  (∀ xs, xs ∈ σ → Unit xs ⊑ L) →
  strings_r σ ⋅ e ⊑
    (⨆ xs ∈ σ, Unit (xs, xs))
      ⋅ strings_r (next_set σ)
    ⊔ dpseudo_top ⋅ mismatch ⋅ residue R.
Proof.
move=> Hσ.
rewrite /strings_r join_list_left_dist.
apply/join_list_sqsubseteq => xs xs_σ /=.
etransitivity;
  first exact: expand_rel R xs (Hσ xs xs_σ).
apply: join_mono; last reflexivity.
apply: pre_ka_mul_mono.
- exact: sqsubseteq_join_list.
- apply/join_list_sqsubseteq => ys ys_next.
  apply: sqsubseteq_join_list.
  rewrite /next_set;
    apply/elem_of_list_In/in_flat_map.
  exists xs; split; exact/elem_of_list_In.
Qed.

(** Lemma 21: Iteration of a representable relation.
    For e : Rel(L), there exists ρ such that for every n and finite Σ ⊆ L:
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Next^n(Σ)_r · e* + Σ* · Σ≠ · ρ *)

(** Helper: next_lt (S n) σ is σ ++ next_lt n (next_set σ). *)

Local Lemma next_iter_succ (n : nat) (σ : list (list T)) :
  next_iter (S n) σ = next_iter n (next_set σ).
Proof. exact: Nat.iter_succ_r. Qed.

Lemma next_iter_nsteps n σ ys :
  ys ∈ next_iter n σ →
  ∃ xs, xs ∈ σ ∧
    nsteps (λ xs ys, Unit (xs, ys) ⊑ e) n xs ys.
Proof.
move: ys; elim: n σ => [|n IH] σ ys.
- move=> Hys. exists ys. split; first exact Hys.
  exact: nsteps_O.
- (* ys ∈ next_set (next_iter n σ) *)
  rewrite /next_set.
  move/elem_of_list_In/in_flat_map =>
    [zs [Hzs_in
      /elem_of_list_In /(next_spec R) Hstep]].
  move/elem_of_list_In: Hzs_in => Hzs_in.
  change (zs ∈ next_iter n σ) in Hzs_in.
  have [xs [Hxs Hn]] := IH _ _ Hzs_in.
  exists xs. split; first exact Hxs.
  exact: nsteps_r Hn Hstep.
Qed.

Lemma next_lt_succ (n : nat) (σ : list (list T)) :
  next_lt (S n) σ = σ ++ next_lt n (next_set σ).
Proof.
elim: n σ => [|n IHn] σ.
- by simpl; rewrite app_nil_r.
- change (next_lt (S n) σ ++ next_iter (S n) σ =
         σ ++ (next_lt n (next_set σ) ++ next_iter n (next_set σ))).
  by rewrite IHn app_assoc /next_iter Nat.iter_succ_r.
Qed.

Lemma next_lt_nsteps n σ ys :
  ys ∈ next_lt n σ →
  ∃ xs m, xs ∈ σ ∧ m < n ∧
    nsteps (λ xs ys, Unit (xs, ys) ⊑ e) m xs ys.
Proof.
elim: n σ => [|n IH] σ /=.
- by move/elem_of_nil.
- move/elem_of_app => [Hn|Hi].
  + have [xs [m [Hxs [Hm Hs]]]] := IH _ Hn.
    exists xs, m. split; first exact Hxs.
    split; [lia | exact Hs].
  + have [xs [Hxs Hs]] := next_iter_nsteps Hi.
    exists xs, n. split; first exact Hxs.
    split; [lia | exact Hs].
Qed.

(** Helper: ⨆ xs ∈ σ, Unit(xs,xs) ⊑ pseudo_top *)

Lemma diag_units_le_pseudo_top
    (σ : list (list T)) :
  (⨆ xs ∈ σ, Unit (xs, xs)) ⊑ pseudo_top.
Proof.
apply/join_list_sqsubseteq => xs _.
exact: unit_le_pseudo_top.
Qed.

Lemma repr_rel_iter (n : nat) (σ : list (list T)) :
  (∀ xs, xs ∈ σ → Unit xs ⊑ L) →
  strings_r σ ⋅ star e ⊑
    dpseudo_top ⋅ strings_r (next_lt n σ)
    ⊔ dpseudo_top ⋅ strings_r (next_iter n σ) ⋅ star e
    ⊔ repr_rel_rtc_error.
Proof.
elim: n σ => [|n IH] σ Hσ.
- (* Base case: x ⊑ pseudo_top ⋅ x since 1 ⊑ pseudo_top *)
  etransitivity; last (apply: sqsubseteq_join; left;
    apply: sqsubseteq_join; right; reflexivity).
  rewrite -assoc.
  etransitivity; last (apply: pre_ka_mul_mono;
    [exact: pre_ka_one_star | reflexivity]).
  by rewrite left_id.
- (* Inductive step: follow the paper's chain of 8 hops *)
  set σ' := next_set σ.
  set err_base := dpseudo_top ⋅ mismatch ⋅ residue R.

  (* next_set preserves membership in L *)
  have Hσ' : ∀ xs, xs ∈ σ' → Unit xs ⊑ L.
  { move=> xs /elem_of_list_In /in_flat_map [ys [_ /elem_of_list_In Hxs]].
    move: Hxs => /(next_spec R ys xs) Hle.
    etransitivity; last exact: repr_rel_cod R.
    exact:
      semi_lattice_morphism_sqsubseteq_proper
        Hle. }

  (* Hop 1: unfold star *)
  have hop1 : strings_r σ ⋅ star e ≡ strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e.
  { by rewrite {1}pre_ka_star_unfold pre_ka_right_dist right_id assoc. }

  (* Hop 2: apply expand_rel_sum *)
  have hop2 :
    strings_r σ ⊔ strings_r σ ⋅ e ⋅ star e ⊑
    strings_r σ
    ⊔ ((⨆ xs ∈ σ, Unit (xs, xs)) ⋅ strings_r σ' ⊔ err_base) ⋅ star e.
  { apply: join_mono; first reflexivity.
    apply: pre_ka_mul_mono; last reflexivity.
    exact: expand_rel_sum Hσ. }

  (* Hop 3: distribute · e* *)
  have hop3 :
    strings_r σ
    ⊔ ((⨆ xs ∈ σ, Unit (xs, xs)) ⋅ strings_r σ' ⊔ err_base) ⋅ star e
    ≡ strings_r σ ⊔
    (⨆ xs ∈ σ, Unit (xs, xs)) ⋅ strings_r σ' ⋅ star e ⊔ repr_rel_rtc_error.
  { by rewrite pre_ka_left_dist /repr_rel_rtc_error /err_base -!assoc. }

  (* Hop 4: apply IH to σ' *)
  have hop4 :
    strings_r σ
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs)) ⋅ strings_r σ' ⋅ star e ⊔ repr_rel_rtc_error
    ⊑ strings_r σ ⊔ (⨆ xs ∈ σ, Unit (xs, xs))
        ⋅ (dpseudo_top ⋅ strings_r (next_lt n σ')
           ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
           ⊔ repr_rel_rtc_error)
    ⊔ repr_rel_rtc_error.
  { apply: join_mono; last reflexivity.
    apply: join_mono; first reflexivity.
    rewrite -assoc; apply: pre_ka_mul_mono; first reflexivity.
    exact: IH _ Hσ'. }

  (* Hop 5: distribute ⨆diag(σ) over the 3 summands *)
  have hop5 :
    strings_r σ
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs))
      ⋅ (dpseudo_top ⋅ strings_r (next_lt n σ')
         ⊔ dpseudo_top
           ⋅ strings_r (next_iter n σ')
           ⋅ star e
         ⊔ repr_rel_rtc_error)
    ⊔ repr_rel_rtc_error
    ≡
    strings_r σ
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs))
      ⋅ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs))
      ⋅ dpseudo_top
      ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs)) ⋅ repr_rel_rtc_error
    ⊔ repr_rel_rtc_error.
  { by rewrite !pre_ka_right_dist -!assoc. }

  (* Hop 6: ⨆diag(σ) ⊑ pt, so ⨆diag(σ)·pt ⊑ pt *)
  have hop6 :
    strings_r σ
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs))
      ⋅ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs))
      ⋅ dpseudo_top
      ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ (⨆ xs ∈ σ, Unit (xs, xs)) ⋅ repr_rel_rtc_error
    ⊔ repr_rel_rtc_error
    ⊑
    dpseudo_top ⋅ strings_r σ
    ⊔ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ repr_rel_rtc_error.
  { have Hd := diag_units_le_pseudo_top σ.

    (* Each of the 5 LHS summands lands in the RHS *)
    rewrite !join_sqsubseteq; repeat split.
    (* strings_r σ ⊑ pseudo_top ⋅ strings_r σ ⊔ ... *)
    - etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_left.
      rewrite -{1}[strings_r σ](left_id 1).
      apply: pre_ka_mul_mono => //; exact: pre_ka_one_star.
    (* ⨆diag · pt · next_lt ⊑ pt · next_lt ⊔ ... *)
    - etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_right.
      apply: pre_ka_mul_mono => //; exact: dpseudo_top_absorb_list.
    (* ⨆diag · pt · next_iter · e* ⊑ pt · next_iter · e* ⊔ ... *)
    - etransitivity; last apply: sqsubseteq_join_left.
      etransitivity; last apply: sqsubseteq_join_right.
      apply: pre_ka_mul_mono; last reflexivity.
      apply: pre_ka_mul_mono => //; exact: dpseudo_top_absorb_list.
    (* ⨆diag · error ⊑ error *)
    - etransitivity; last apply: sqsubseteq_join_right.
      rewrite /repr_rel_rtc_error !assoc.
      apply: pre_ka_mul_mono; last reflexivity.
      apply: pre_ka_mul_mono; last reflexivity.
      apply: pre_ka_mul_mono; last reflexivity.
      exact: dpseudo_top_absorb_list.
    (* error ⊑ error *)
    - exact: sqsubseteq_join_right. }

  (* Hop 7: reassemble using next_lt_succ and next_iter_succ *)
  have hop7 :
    dpseudo_top ⋅ strings_r σ
    ⊔ dpseudo_top ⋅ strings_r (next_lt n σ')
    ⊔ dpseudo_top ⋅ strings_r (next_iter n σ') ⋅ star e
    ⊔ repr_rel_rtc_error
    ≡
    dpseudo_top ⋅ strings_r (next_lt (S n) σ)
    ⊔ dpseudo_top ⋅ strings_r (next_iter (S n) σ) ⋅ star e
    ⊔ repr_rel_rtc_error.
  { by rewrite next_lt_succ strings_r_app
      pre_ka_right_dist next_iter_succ -assoc. }

  (* Compose all hops *)
  rewrite hop1.
  etransitivity; first exact: hop2.
  rewrite hop3.
  etransitivity; first exact: hop4.
  rewrite hop5.
  etransitivity; first exact: hop6.
  by rewrite hop7.
Qed.

(** Theorem 22: If Next^n_e(Σ) = ∅, then
      Σ_r · e* ≤ Σ* · Next^{<n}(Σ)_r + Σ* · Σ≠ · ρ *)

Lemma repr_rel_iter_empty
  (n : nat) (σ : list (list T)) :
  (∀ xs, xs ∈ σ → Unit xs ⊑ L) →
  next_iter n σ = [] →
  strings_r σ ⋅ star e ⊑
    dpseudo_top ⋅ strings_r (next_lt n σ) ⊔ repr_rel_rtc_error.
Proof.
move=> Hσ Hempty.
etransitivity; first exact: repr_rel_iter n σ Hσ.
by rewrite Hempty /strings_r /= right_absorb left_absorb right_id.
Qed.

End ReprRelIteration.

End RepresentableRelations.

Arguments dpseudo_top {_ _ _}.
Arguments mismatch {_ _ _}.

Section Padding.

Variables T : setoid.
Context `{!LeibnizEquiv T, !EqDecision T, !Finite T}.
Implicit Types (e : ka_term (list T * list T)) (L : ka_term (list T)).
Implicit Types (ρ : ka_term (list (option T) * list (option T))).

Local Definition lift : list T → list (option T) := map Some.
Local Definition lift2 : list T * list T → list (option T) * list (option T) :=
  pair_mor (lift ∘ fst) (lift ∘ snd).

Definition pad_lang L := ka_term_map lift L ⋅ Unit [None].
Definition pad_rel e := ka_term_map lift2 e ⋅ Unit ([None], [None]).

Lemma sqsubseteq_pad_rel_1 p e :
  Unit p ⊑ e →
  Unit (lift2 p ⋅ ([None], [None])) ⊑ pad_rel e.
Proof.
rewrite monoid_morphism_mul /pad_rel => pe; apply: pre_ka_mul_mono => //.
by rewrite -l_alt l_natural; exists p; rewrite l_alt.
Qed.

Lemma sqsubseteq_pad_rel_2 p e :
  Unit p ⊑ pad_rel e →
  ∃ p', p = lift2 p' ⋅ ([None], [None]) ∧ Unit p' ⊑ e.
Proof.
rewrite /pad_rel -l_alt monoid_morphism_mul l_natural.
case=> /= p' [] _ [] /leibniz_equiv_iff -> [pP /leibniz_equiv_iff ->].
by case: pP => {}p' [] /leibniz_equiv_iff -> /l_alt ?; eauto.
Qed.

Lemma pad_rel_rtc_1 xs ys e :
  rtc (λ xs ys, Unit (xs, ys) ⊑ e) xs ys →
  rtc (λ xs ys, Unit (xs, ys) ⊑ pad_rel e)
    (lift xs ⋅ [None]) (lift ys ⋅ [None]).
Proof.
elim: xs ys / => // xs ys zs xs_ys _ IH.
move/sqsubseteq_pad_rel_1: xs_ys.
by etransitivity; last exact: IH; apply: rtc_once.
Qed.

Local Lemma lift_inj xs ys :
  lift xs = lift ys → xs = ys.
Proof.
rewrite /lift; move: ys;
  by elim: xs => [|x xs IH] [|y ys] //=
    [= -> /IH ->].
Qed.

Local Lemma lift_pad_inj xs ys :
  lift xs ⋅ [None] = lift ys ⋅ [None] → xs = ys.
Proof.
move=> /app_inv_tail /lift_inj //.
Qed.

Lemma pad_rel_rtc_2 xs ys e :
  rtc (λ xs ys, Unit (xs, ys) ⊑ pad_rel e)
    (lift xs ⋅ [None]) ys →
  ∃ ys', ys = lift ys' ⋅ [None] ∧
         rtc (λ xs ys, Unit (xs, ys) ⊑ e) xs ys'.
Proof.
move=> Hrtc.
have : ∃ xs', lift xs ⋅ [None] = lift xs' ⋅ [None]
  ∧ ∃ ys', ys = lift ys' ⋅ [None] ∧
    rtc (λ xs ys, Unit (xs, ys) ⊑ e) xs' ys'.
{ move: Hrtc.
  apply: (rtc_ind_r (λ z, _)).
  - exists xs. split; first done.
    exists xs. split; first done.
    exact: rtc_refl.
  - move=> z1 z2 _  Hstep
      [xs' [Hxs [z1' [Hz1 Hrtc']]]].
    subst z1.
    case/sqsubseteq_pad_rel_2: Hstep =>
      [[sl sr] [Hz /= Hstep]].
    have Esl : z1' = sl.
    { apply: lift_inj. apply: app_inv_tail.
      have := f_equal fst Hz.
      by rewrite /lift2 /lift /=
        /mul /prod_mul /list_mul. }
    subst sl. exists xs'. split; first done.
    exists sr. split.
    { have := f_equal snd Hz.
      by rewrite /lift2 /lift /=
        /mul /prod_mul /list_mul. }
    exact: rtc_r Hrtc' Hstep. }
move=> [xs' [Hxs [ys' [-> Hrtc']]]].
exists ys'. split; first done.
suff -> : xs = xs' by [].
apply: lift_inj. exact: app_inv_tail Hxs.
Qed.

Lemma pad_rel_nsteps_2 e m xs ys :
  nsteps (λ xs ys, Unit (xs, ys) ⊑ pad_rel e) m (lift xs ⋅ [None]) ys →
  ∃ ys', ys = lift ys' ⋅ [None] ∧ nsteps (λ xs ys, Unit (xs, ys) ⊑ e) m xs ys'.
Proof.
elim: m => [|m IH] in ys *.
- move=> /nsteps_0_inv <-; exists xs; split => //; constructor.
- case/nsteps_inv_r=> zs [] /IH [zs' [] -> xs_zs'].
  case/sqsubseteq_pad_rel_2=> [[_ ys'] [] [/lift_pad_inj <- ->] zs'_ys'].
  exists ys'; split => //.
  by apply: nsteps_r.
Qed.

Lemma pad_rel_nsteps_2' e m xs ys :
  nsteps (λ xs ys, Unit (xs, ys) ⊑ pad_rel e) m (lift xs ⋅ [None]) (lift ys ⋅ [None]) →
  nsteps (λ xs ys, Unit (xs, ys) ⊑ e) m xs ys.
Proof. by case/pad_rel_nsteps_2 => ys' [] /lift_pad_inj <-. Qed.

Lemma sqsubseteq_pad_lang_1 xs L :
  Unit xs ⊑ L →
  Unit (lift xs ⋅ [None]) ⊑ pad_lang L.
Proof.
move=> /l_alt Hle; apply/l_alt.
rewrite /pad_lang.
change ((l (ka_term_map (map Some (A := T)) L)
  ⋅ l (Unit (@nil (option T) ++ [None])))
  (map Some xs ++ [None])).
rewrite l_natural.
simpl lang_mul. simpl lang_car.
exists (map Some xs),
  ([None] : list (option T)).
split; first done.
split; last done.
simpl. exists xs; done.
Qed.

Lemma sqsubseteq_pad_lang_2 xs L :
  Unit xs ⊑ pad_lang L →
  ∃ xs', xs = lift xs' ⋅ [None] ∧ Unit xs' ⊑ L.
Proof.
rewrite /pad_lang => /l_alt Hle.
have Hle' : (lang_map (map Some (A := T)) (l L)
  ⋅ l (Unit [None])) xs.
{ rewrite -l_natural. exact Hle. }
simpl in Hle'.
move: Hle' => [a [b [/leibniz_equiv_iff /= Exs
  [[t [/leibniz_equiv_iff /= Ha /l_alt He]]
   /leibniz_equiv_iff /= Hb]]]].
subst b a.
by exists t; subst xs.
Qed.

Lemma pad_rel_pad_lang_1 e L :
  ka_term_proj1 e ⊑ L →
  ka_term_proj1 (pad_rel e) ⊑ pad_lang L.
Proof.
move=> e_L.
rewrite /pad_rel monoid_morphism_mul /=.
apply: pre_ka_mul_mono => //=.
rewrite /ka_term_proj1 ka_term_map_comp.
have ->: ka_term_map (fst ∘ lift2) e ≡ ka_term_map lift (ka_term_proj1 e).
  by rewrite ka_term_map_comp; apply: ka_term_ext; case.
by apply: semi_lattice_morphism_sqsubseteq_proper.
Qed.

Lemma pad_rel_pad_lang_2 e L :
  ka_term_proj2 e ⊑ L →
  ka_term_proj2 (pad_rel e) ⊑ pad_lang L.
Proof.
move=> e_L.
rewrite /pad_rel monoid_morphism_mul /=.
apply: pre_ka_mul_mono => //=.
rewrite /ka_term_proj2 ka_term_map_comp.
have ->: ka_term_map (snd ∘ lift2) e ≡ ka_term_map lift (ka_term_proj2 e).
  by rewrite ka_term_map_comp; apply: ka_term_ext; case.
by apply: semi_lattice_morphism_sqsubseteq_proper.
Qed.

Lemma repr_rel_rtc_soundness' e L ρ (xs ys : list T) :
  rtc (λ xs' ys', Unit (xs', ys') ⊑ e) xs ys →
  Unit (1, lift xs ⋅ [None]) ⋅ star (pad_rel e) ⊑
  dpseudo_top ⋅ ka_term_inj2 (pad_lang L) ⊔ dpseudo_top ⋅ mismatch ⋅ ρ →
  Unit ys ⊑ L.
Proof.
move=> /pad_rel_rtc_1 xs_ys xs_L.
have : Unit (lift ys ⋅ [None]) ⊑ pad_lang L.
  exact: repr_rel_rtc_soundness xs_ys xs_L.
case/sqsubseteq_pad_lang_2 => ys' [] e_ys' {xs_ys xs_L}.
suff -> : ys = ys' by [].
move: e_ys'; rewrite /lift /mul /list_mul.
move/app_inv_tail; move: ys ys'.
by elim=> [|y ys IH] [|y' ys'] //= [= -> /IH ->].
Qed.

Lemma finite_state_pad_rel e :
  finite_state (T + T) (Unit ∘ generator_interp) e →
  finite_state (option T + option T) (Unit ∘ generator_interp) (pad_rel e).
Proof.
move=> fin_e; apply: finite_state_mul; last exact: finite_state_Unit.
set t := ka_term_map _.
have {}fin_e: finite_state (T + T) (t ∘ Unit ∘ generator_interp) (t e).
  by apply: finite_state_algebra_change fin_e => //.
pose t' (x : T + T) :=
  match x with
  | inl x => inl (Some x)
  | inr x => inr (Some x)
  end.
pose s' (x : option T + option T) :=
  match x with
  | inl (Some x) => Some (inl x)
  | inr (Some x) => Some (inr x)
  | _ => None
  end.
apply: (finite_state_alphabet_change t' s') fin_e.
- by case.
- by case.
- by case=> [[?|]|[?|]] ? //= [<-].
Qed.

Lemma repr_rel_iter_empty' e L (xs : list T)
    (R : repr_rel (pad_rel e) (pad_lang L)) n :
  Unit xs ⊑ L →
  next_iter R n [lift xs ⋅ [None]] = [] →
  Unit (1, lift xs ⋅ [None]) ⋅ star (pad_rel e) ⊑
  dpseudo_top ⋅ strings_r (next_lt R n [lift xs ⋅ [None]])
  ⊔ repr_rel_rtc_error R.
Proof.
move=> xs_L next_done.
have {}xs_L: Unit (lift xs ⋅ [None]) ⊑ pad_lang L
  by exact: sqsubseteq_pad_lang_1.
have ->: Unit (1, lift xs ⋅ [None]) ≡ strings_r [lift xs ⋅ [None]].
  by rewrite strings_r_alt /= right_id.
apply: repr_rel_iter_empty next_done.
by move=> ? /elem_of_list_singleton ->.
Qed.

Lemma repr_rel_iter_final e C L (xs ys : list T)
    (R : repr_rel (pad_rel e) (pad_lang L)) :
  Unit xs ⊑ L →
  ka_term_proj1 e ⊑ C →
  (∀ xs ys1 ys2,
    Unit (xs, ys1) ⊑ e →
    Unit (xs, ys2) ⊑ e →
    ys1 = ys2) →
  (∀ ys', ¬ Unit (ys, ys') ⊑ e) →
  rtc (λ xs ys, Unit (xs, ys) ⊑ e) xs ys →
  Unit (1, lift xs ⋅ [None]) ⋅ star (pad_rel e) ⊑
    dpseudo_top ⋅
    ka_term_inj2 (pad_lang C ⊔ Unit (lift ys ⋅ [None]))
    ⊔ repr_rel_rtc_error R.
Proof.
move=> xs_L e_C det_e final_ys /rtc_nsteps [n xs_ys].
set ub := pad_lang C ⊔ _.
have <- : strings_r (next_lt R (S n) [lift xs ⋅ [None]]) ⊑ ka_term_inj2 ub.
{ rewrite strings_r_alt; f_equiv; rewrite join_list_sqsubseteq => zs.
  case/next_lt_nsteps=> _ [] m [] /elem_of_list_singleton -> [] m_n xs_zs.
  case/pad_rel_nsteps_2: xs_zs => {}zs [] -> xs_zs.
  move: xs_zs; have [->|{}m_n] : m = n ∨ n = S m + (n - S m) by lia.
    move=> xs_zs; have <-: ys = zs by apply: nsteps_det xs_ys xs_zs.
    by rewrite -l_alt; right => /=.
  rewrite m_n in xs_ys; case/nsteps_add_inv: xs_ys=> ys' [] xs_ys' ys'_ys xs_zs.
  case/nsteps_inv_r: xs_ys'=> zs' [] xs_zs' zs'_ys'.
  have {zs xs_zs} ->: zs = zs' by apply: nsteps_det xs_zs xs_zs'.
  have /l_alt ?: Unit (lift zs' ⋅ [None]) ⊑ pad_lang C; last first.
    by rewrite -l_alt; left.
  by apply: sqsubseteq_pad_lang_1; rewrite -e_C -zs'_ys'. }
apply: repr_rel_iter_empty' => //; apply: elem_of_nil_inv => zs.
case/next_iter_nsteps=> _ [] /elem_of_list_singleton -> xs_zs.
case/nsteps_inv_r: xs_zs=> ys' [] xs_ys' ys'_zs.
case/pad_rel_nsteps_2: xs_ys' => {}ys' [] -> xs_ys' in ys'_zs *.
have ys_ys': ys = ys' by exact: nsteps_det xs_ys xs_ys'.
rewrite -{}ys_ys' {xs_ys' ys'} in ys'_zs *.
case/sqsubseteq_pad_rel_2: ys'_zs => [[ys' zs']] [] [ey ez].
move/lift_pad_inj: ey => <- {ys'}; exact: final_ys.
Qed.

End Padding.
