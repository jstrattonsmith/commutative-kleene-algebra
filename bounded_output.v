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
From kacc Require Import repr_rel.

Section BoundedOutput.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Implicit Types (e : ka_term (list T * list T)) (L : ka_term (list T)).

(** Definition 28: Bounded-output terms.

    A term [e] over [Σ ⊕ Σ] (represented as [ka_term (list T * list T)]) has
    bounded output with fanout [k] if, for every string [s] in its language,
    the length of the right projection is bounded by [(|π_l(s)| + 1) * k].

    Intuitively, this means the term represents a relation that maps each
    input string to only finitely many output strings of bounded length. *)

Definition bounded_output_with (k : nat) (e : ka_term (list T * list T)) : Prop :=
  ∀ sl sr, Unit (sl, sr) ⊑ e → length sr ≤ (length sl + 1) * k.

Lemma bounded_output_with_mono k1 k2 e :
  k1 ≤ k2 → bounded_output_with k1 e → bounded_output_with k2 e.
Proof. move=> Hle H1 sl sr Hin. have := H1 _ _ Hin. nia. Qed.

Definition bounded_output (e : ka_term (list T * list T)) : Type :=
  {k | bounded_output_with k e}.

(** Lemma 29: If [e] has bounded output with fanout [k] and [Σ] is a finite
    set of strings, then [Next_e(Σ)] is finite.  More precisely, if
    [s ∈ Next_e(Σ)], then [|s| ≤ (m + 1) * k] where
    [m = max { |s'| | s' ∈ Σ }]. *)

Lemma bounded_output_next_bound k (e : ka_term (list T * list T)) sl sr sr' :
  bounded_output_with k e →
  Unit (sl ++ sr, sr') ⊑ e →
  length sr' ≤ (length sl + length sr + 1) * k.
Proof.
move=> Hbo Hin.
have := Hbo _ _ Hin.
by rewrite List.length_app.
Qed.

(** Lemma 30 (partial): Bounded-output is preserved by join. *)

Lemma bounded_output_with_bot k :
  bounded_output_with k (⊥ : ka_term (list T * list T)).
Proof.
move=> sl sr /l_alt.
by rewrite pre_ka_morphism_bottom.
Qed.

Lemma bounded_output_with_join k1 k2 e1 e2 :
  bounded_output_with k1 e1 →
  bounded_output_with k2 e2 →
  bounded_output_with (max k1 k2) (e1 ⊔ e2).
Proof.
move=> H1 H2 sl sr /l_alt.
rewrite semi_lattice_morphism_join.
case=> /l_alt Hin.
- have := H1 _ _ Hin.
  have : k1 ≤ max k1 k2 by lia.
  by nia.
- have := H2 _ _ Hin.
  have : k2 ≤ max k1 k2 by lia.
  by nia.
Qed.

Lemma bounded_output_join e1 e2 :
  bounded_output e1 →
  bounded_output e2 →
  bounded_output (e1 ⊔ e2).
Proof.
move=> [k1 H1] [k2 H2].
exists (max k1 k2).
exact: bounded_output_with_join.
Qed.

(** Lemma 30 (partial): Bounded-output is preserved by multiplication. *)

Lemma bounded_output_with_mul k1 k2 e1 e2 :
  bounded_output_with k1 e1 →
  bounded_output_with k2 e2 →
  bounded_output_with (k1 + k2) (e1 ⋅ e2).
Proof.
move=> H1 H2 sl sr /l_alt.
rewrite pre_ka_morphism_mul.
move=> [[sl1 sr1] [[sl2 sr2] [Heq [/l_alt H1' /l_alt H2']]]].
have := H1 _ _ H1'.
have := H2 _ _ H2'.
move: Heq => /leibniz_equiv_iff [/= esl esr].
rewrite esl esr !length_app. nia.
Qed.

Lemma bounded_output_mul e1 e2 :
  bounded_output e1 →
  bounded_output e2 →
  bounded_output (e1 ⋅ e2).
Proof.
move=> [k1 H1] [k2 H2].
exists (k1 + k2).
exact: bounded_output_with_mul.
Qed.

(** Lemma 30 (star case): Bounded-output is preserved by star,
    provided that [|π_l(s)| ≥ 1] for all strings [s ≤ e].
    Under this condition, [e*] has bounded output with fanout [2k]
    when [e] has fanout [k]. *)

Definition left_nonempty (e : ka_term (list T * list T)) : Prop :=
  ∀ sl sr, Unit (sl, sr) ⊑ e → length sl ≥ 1.

Definition left_has_emptyb (e : ka_term (list T * list T)) : bool :=
  has_one (ka_term_proj1 e).

Lemma left_has_emptyb_falseP e :
  left_has_emptyb e = false ↔ left_nonempty e.
Proof.
rewrite /left_has_emptyb /left_nonempty; split.
- move=> Hf sl sr Hin.
  destruct sl as [|x sl']; last by simpl; lia.
  exfalso.
  have : has_one (@ka_term_proj1 (list_monoid T) (list_monoid T) e) = true.
  { apply/has_oneP.
    rewrite -(@pre_ka_morphism_one _ _ (@ka_term_proj1 (list_monoid T) (list_monoid T)) _).
    exact: semi_lattice_morphism_sqsubseteq_proper Hin. }
  by rewrite Hf.
- move=> Hne.
  apply/Bool.not_true_iff_false. move=> /has_oneP /l_alt.
  rewrite l_natural => -[[sl sr] /= [/leibniz_equiv_iff Esl /l_alt Hin]].
  simpl in Esl. subst sl.
  have := Hne _ _ Hin. simpl. lia.
Qed.

Lemma bounded_output_with_star k e :
  bounded_output_with k e →
  left_nonempty e →
  bounded_output_with (2 * k) (star e).
Proof.
move=> Hbo Hne sl sr /l_alt.
rewrite pre_ka_morphism_star.
case=> n; revert sl sr; elim: n => [|n IH] sl sr /=.
- move=> [/leibniz_equiv_iff Esl /leibniz_equiv_iff Esr].
  simpl in Esl, Esr. subst. exact (Nat.le_0_l _).
- move=> [[sl1 sr1] [[sl2 sr2] [/leibniz_equiv_iff [/= esl esr] [/l_alt He Hrec]]]].
  have := Hbo _ _ He.
  have := Hne _ _ He.
  have := IH _ _ Hrec.
  rewrite esl esr !length_app. nia.
Qed.

Lemma bounded_output_star e :
  bounded_output e →
  left_nonempty e →
  bounded_output (star e).
Proof.
move=> [k Hk] Hne.
exists (2 * k).
exact: bounded_output_with_star.
Qed.

(** Bounded-output unit terms. *)

Lemma bounded_output_unit (s : list T * list T) :
  bounded_output (Unit s).
Proof.
destruct s as [s1 s2]; exists (length s2).
move=> sl sr /l_alt /= [/leibniz_equiv_iff Esl /leibniz_equiv_iff Esr].
simpl in Esl, Esr. subst. nia.
Qed.

(** Boolean check for bounded output: traverses the term and verifies
    that every starred subterm satisfies left_nonempty (via left_has_emptyb). *)

Fixpoint bounded_outputb (e : ka_term (list T * list T)) : bool :=
  match e with
  | Unit _ => true
  | ka_term_bottom => true
  | ka_term_join e1 e2 => bounded_outputb e1 && bounded_outputb e2
  | ka_term_mul e1 e2 => bounded_outputb e1 && bounded_outputb e2
  | ka_term_star e => negb (left_has_emptyb e) && bounded_outputb e
  end.

Lemma bounded_outputbP e :
  bounded_outputb e = true → bounded_output e.
Proof.
elim: e.
- move=> s _. exact: bounded_output_unit.
- move=> _. exists 0. exact: bounded_output_with_bot.
- move=> e1 IH1 e2 IH2 /andb_true_iff [/IH1 H1 /IH2 H2].
  exact: bounded_output_join.
- move=> e1 IH1 e2 IH2 /andb_true_iff [/IH1 H1 /IH2 H2].
  exact: bounded_output_mul.
- move=> e IH /andb_true_iff [/negb_true_iff /left_has_emptyb_falseP Hne /IH Hbo].
  exact: bounded_output_star.
Qed.

(** Definition 32: Prefix-free terms. A term [L] is prefix-free if for
    all strings [s1 ≤ L] and [s2 ≤ L], if [s1] is a prefix of [s2],
    then [s1 = s2]. *)

Definition prefix_free (L : ka_term (list T)) : Prop :=
  ∀ s1 s2, Unit s1 ⊑ L → Unit s2 ⊑ L →
    (∃ t, s2 = s1 ++ t) → s1 = s2.

(** Lemma 33 (normal form): If two lists diverge (share a common prefix
    then have different next characters), their pairing factors through diff. *)

Lemma diag_unit_absorb (s : list T) :
  Unit (s, s) ⋅ ka_term_diag pseudo_top ⊑ ka_term_diag pseudo_top.
Proof.
have -> : Unit (s, s) ≡ ka_term_diag (Unit s) by [].
by rewrite -monoid_morphism_mul pseudo_top_absorb.
Qed.

Lemma unit_le_diff (x x' : T) :
  x ≠ x' → Unit ([x], [x']) ⊑ @diff T _ _.
Proof.
move=> Hne. rewrite /diff.
apply: sqsubseteq_join_list; apply/elem_of_list_fmap.
exists (x, x'); split => //.
apply/elem_of_list_filter; split; last exact: elem_of_enum.
by apply/Is_true_true/bool_decide_eq_true.
Qed.

Lemma diff_unit (x x' : T) :
  x ≠ x' → Unit ([x], [x']) ⊑ ka_term_diag pseudo_top ⋅ @diff T _ _.
Proof.
move=> Hne.
rewrite -(left_id 1 (⋅) (Unit ([x], [x']))).
apply: pre_ka_mul_mono; last exact: unit_le_diff Hne.
have -> : (1 : ka_term _) ≡ ka_term_diag (1 : ka_term (list T)) by [].
rewrite -monoid_morphism_one.
exact: semi_lattice_morphism_sqsubseteq_proper (pre_ka_one_star _).
Qed.

Lemma list_diverge (s s' : list T) :
  ¬ (∃ t, s' = s ++ t) →
  ¬ (∃ t, s = s' ++ t) →
  Unit (s, s') ⊑ ka_term_diag pseudo_top ⋅ @diff T _ _ ⋅ pseudo_top.
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
    by rewrite !assoc diag_unit_absorb.
  + (* Different heads: divergence *)
    have Hsplit : Unit (x :: s, x' :: s') ≡ Unit ([x], [x']) ⋅ Unit (s, s').
    { have -> : (x :: s, x' :: s') = ([x], [x']) ⋅ (s, s') by done.
      by rewrite monoid_morphism_mul. }
    etransitivity.
    { rewrite Hsplit. reflexivity. }
    apply: pre_ka_mul_mono.
    * exact: diff_unit Hne.
    * exact: unit_le_pseudo_top.
Qed.

(** Construction of the next function for finite-state terms.

    For a finite-state term [e] over [list T * list T], the automaton [A]
    has generators [T + T] (left and right alphabet symbols).
    Given [sl : list T], we feed [map inl sl] to the automaton to reach
    a state, then enumerate all [sr] accepted from that state via
    [map inr sr]. The bounded-output property bounds the length of [sr]. *)

Section FSANext.

Variable A : fsa (T + T) (ka_term (list T * list T)) (Unit ∘ generator_interp).
Variable bo : bounded_output (fsa_elem A).

(** Interpret a string over T + T as a pair via generator_interp. *)
Definition interp_str (w : list (T + T)) : list T * list T :=
  ∏ (map generator_interp w).

(** The next function: enumerate all strings over T + T up to a bound,
    filter those accepted by A whose left projection equals sl,
    return their right projections. *)
Definition fsa_next (sl : list T) : list (list T) :=
  let k := proj1_sig bo in
  let bound := (length sl + 1) * k + length sl in
  map (λ w, snd (interp_str w))
    (filter (λ w, string_match A w && bool_decide (fst (interp_str w) = sl))
            (@enum_list_lt (T + T) _ _ (S bound))).

Lemma fsa_next_spec (sl sr : list T) :
  sr ∈ fsa_next sl ↔ Unit (sl, sr) ⊑ fsa_elem A.
Proof.
rewrite /fsa_next.
split.
- (* Forward: sr ∈ fsa_next sl → Unit (sl, sr) ⊑ fsa_elem A *)
  move/elem_of_list_fmap => [w [Esr Hw]].
  apply elem_of_list_filter in Hw.
  destruct Hw as [Hcond Hlen].
  move: Hcond => /andb_True [/Is_true_true Hmatch /Is_true_true /bool_decide_eq_true Hleft].
  have Hsound := string_match_sound Hmatch.
  rewrite Esr.
  etransitivity; last exact: Hsound.
  rewrite sqsubseteq_iff ka_of_string_Unit.
  have -> : (sl, snd (interp_str w)) = interp_str w.
  { by rewrite -Hleft -surjective_pairing. }
  by rewrite semi_lattice_idemp.
- (* Backward: Unit (sl, sr) ⊑ fsa_elem A → sr ∈ fsa_next sl *)
  move=> Hle.
  set s := generate (sl, sr).
  have Es := generateP (sl, sr).
  have Hkas : ka_of_string (Unit ∘ generator_interp) s ⊑ fsa_elem A.
  { etransitivity; last exact: Hle.
    rewrite sqsubseteq_iff ka_of_string_Unit Es semi_lattice_idemp //. }
  have [w [Hw Hmatch]] := string_match_complete_sized Hkas.
  apply/elem_of_list_fmap.
  exists w; split.
  + (* sr = snd (interp_str w) *)
    rewrite /interp_str.
    have /leibniz_equiv_iff Hw' := Hw.
    have Es' : (sl, sr) = ∏ (map generator_interp s) by apply leibniz_equiv_iff.
    by rewrite Hw' -Es'.
  + (* w ∈ filter ... (enum_list_lt ...) *)
    apply/elem_of_list_filter; split.
    * apply/andb_True; split.
      -- exact/Is_true_true.
      -- apply/Is_true_true/bool_decide_eq_true.
         rewrite /interp_str.
         have /leibniz_equiv_iff Hw' := Hw.
         have Es' : (sl, sr) = ∏ (map generator_interp s) by apply leibniz_equiv_iff.
         by rewrite Hw' -Es'.
    * apply/elem_of_enum_list_lt.
      destruct bo as [k Hk].
      have Hsr := Hk sl sr Hle.
      have /leibniz_equiv_iff Hw' := Hw.
      have Es' : (sl, sr) = ∏ (map generator_interp s) by apply leibniz_equiv_iff.
      (* length w = length sl + length sr *)
      have Hwlen : length w = length sl + length sr.
      { have Heqw : (sl, sr) ≡ ∏ (map generator_interp w).
        { by rewrite /interp_str Hw' -Es'. }
        rewrite (@sized_monoid _ _ _ _ w _ Heqw) /s /= length_app !length_fmap //. }
      have Hbound : length sl + length sr < S ((length sl + 1) * k + length sl) by nia.
      rewrite Hwlen. exact Hbound.
Qed.

End FSANext.

(** Lemma 31 (core): For a bounded-output term, if [Unit (sl, sr) ⋅ t ⊑ e]
    for some nonzero [t] with a witness of left-size [m], then
    [length sr ≤ (length sl + m + 1) * k]. *)

Lemma bounded_output_prefix k e (sl sr : list T) (t : ka_term _) :
  bounded_output_with k e →
  Unit (sl, sr) ⋅ t ⊑ e →
  ∀ tl tr, l t (tl, tr) →
  length sr ≤ (length sl + length tl + 1) * k.
Proof.
move=> Hk Hle tl tr Ht.
have Hprod : Unit ((sl, sr) ⋅ (tl, tr)) ⊑ e.
{ etransitivity; last exact: Hle.
  rewrite {1}monoid_morphism_mul.
  have /l_alt Ht' := Ht.
  etransitivity; last (apply: pre_ka_mul_mono; [reflexivity | exact: Ht']).
  rewrite sqsubseteq_iff semi_lattice_idemp //. }
have := Hk _ _ Hprod.
rewrite /= !length_app.
nia.
Qed.

(** Lemma 31 (full): For each state σ of A, pick a witness if
    fsa_interp σ ≢ ⊥, compute the max left-projection size m,
    and set the adjusted fanout k = (m + 1) * k₀. *)

Section Lemma31.

Variable A : fsa (T + T) (ka_term (list T * list T)) (Unit ∘ generator_interp).
Variable k0 : nat.
Variable Hbo : bounded_output_with k0 (fsa_elem A).

(** For each state, get a witness or a proof of emptiness. *)
Definition state_witness (σ : fsa_state A) :
  (fsa_interp σ ≡ ⊥) + {w : list T * list T | l (fsa_interp σ) w} :=
  either_empty_or_nonzero (fsa_interp σ).

(** Extract the left-projection size of the witness, or 0 if empty. *)
Definition witness_lsize (σ : fsa_state A) : nat :=
  match state_witness σ with
  | inl _ => 0
  | inr (exist _ (wl, _) _) => length wl
  end.

(** Maximum left-projection size across all states. *)
Definition max_witness_lsize : nat :=
  list_max (map witness_lsize (enum (fsa_state A))).

(** Adjusted fanout. *)
Definition adjusted_fanout : nat :=
  (max_witness_lsize + 1) * k0.

(** Lemma 31: In the decomposition, any prefix s with nonzero suffix
    satisfies the bounded-output constraint with adjusted_fanout. *)

Lemma lemma_31_bound (σ : fsa_state A) (s : list (T + T)) :
  fsa_interp (fsa_initial A) ≡ fsa_elem A →
  fsa_interp (fsa_trans_s s (fsa_initial A)) ≢ ⊥ →
  let p := ∏ (map generator_interp s) in
  length (snd p) ≤ (length (fst p) + 1) * adjusted_fanout.
Proof.
move=> Hinit Hne /=.
set σ' := fsa_trans_s s (fsa_initial A).
(* Get the witness and its properties *)
destruct (state_witness σ') as [Hbot | [[wl wr] Hw]] eqn:Hsw.
{ by exfalso; apply: Hne. }
set p := ∏ (map generator_interp s).
(* string_suffix_term_at is ka_of_string s ⋅ fsa_interp (fsa_trans_s s σ).
   By fsa_elem_k_decomp_gen, this ⊑ fsa_interp (fsa_initial A) = fsa_elem A. *)
have Hle : Unit p ⋅ fsa_interp σ' ⊑ fsa_elem A.
{ rewrite -Hinit.
  have Hdecomp := fsa_elem_k_decomp_gen (fsa_initial A) (length s).
  etransitivity; last (rewrite Hdecomp; exact: sqsubseteq_join_right).
  rewrite /sum_suffix_terms_k_at /string_suffix_term_at.
  etransitivity; last (apply: sqsubseteq_join_list; apply/elem_of_list_fmap;
    exists s; split => //; apply/elem_of_enum_list_eq => //).
  rewrite {1}(ka_of_string_Unit s) /p.
  rewrite sqsubseteq_iff semi_lattice_idemp //. }
have Hle' : Unit (fst p, snd p) ⋅ fsa_interp σ' ⊑ fsa_elem A.
{ by rewrite -surjective_pairing. }
have Hpf := bounded_output_prefix (sl := fst p) (sr := snd p) Hbo Hle' Hw.
(* Hpf : length (snd p) ≤ (length (fst p) + length wl + 1) * k0 *)
(* Need: length (snd p) ≤ (length (fst p) + 1) * adjusted_fanout *)
rewrite /adjusted_fanout.
have Hwl_bound : length wl ≤ max_witness_lsize.
{ rewrite /max_witness_lsize.
  have Hin : witness_lsize σ' ∈ map witness_lsize (enum (fsa_state A)).
  { apply/elem_of_list_fmap. exists σ'. split => //. exact: elem_of_enum. }
  have Hall : Forall (λ k, k ≤ max_witness_lsize)
                     (map witness_lsize (enum (fsa_state A))).
  { apply/list_max_le. done. }
  have Hwlb := proj1 (Forall_forall _ _) Hall _ Hin.
  rewrite /witness_lsize Hsw /= in Hwlb. exact Hwlb. }
(* Hpf : length p.2 ≤ (length p.1 + length wl + 1) * k0
   Hwl_bound : length wl ≤ max_witness_lsize
   Goal : length p.2 ≤ (length p.1 + 1) * adjusted_fanout *)
rewrite /adjusted_fanout Nat.mul_assoc.
etransitivity; first exact: Hpf.
apply: Nat.mul_le_mono_r.
move: Hwl_bound. set a := length (fst p). set b := length wl. set c := max_witness_lsize.
move=> Hbc. nia.
Qed.

(** Paper version of Lemma 31: decomposition with
    output-bounded suffix terms.

    For a bounded-output finite-state term, the
    expansion from Lemma 27 can be restricted to
    suffix terms whose right projection is bounded
    by [(|πl(s)| + 1) * k]. *)

(** Output bound predicate for generator strings. *)
Definition output_bounded
  (k : nat) (s : list (T + T)) : bool :=
  let p := ∏ (map generator_interp s) in
  Nat.leb
    (length (snd p))
    ((length (fst p) + 1) * k).

(** Bounded suffix sum: sums only over strings
    satisfying the output bound. *)
Definition bounded_suffix_sum_at
  (σ : fsa_state A) (n k : nat)
  : ka_term (list T * list T) :=
  ⨆ (map (string_suffix_term_at σ)
    (filter (output_bounded k)
      (@enum_list_eq (T + T) _ _ n))).

(** Helper: filtering out ⊥ terms from a join
    preserves the result. *)
Lemma join_list_filter_bot
  {B : Type}
  (g : B → ka_term (list T * list T))
  (P : B → bool) (xs : list B) :
  (∀ x, x ∈ xs → P x = false →
    g x ≡ ⊥) →
  ⨆ (map g xs) ≡
  ⨆ (map g (filter P xs)).
Proof.
move=> Hbot; apply (anti_symm (⊑)).
- apply/join_list_sqsubseteq =>
    _ /elem_of_list_fmap [x [-> Hx]].
  case Px : (P x).
  + apply: sqsubseteq_join_list.
    apply/elem_of_list_fmap.
    exists x; split => //.
    apply elem_of_list_filter.
    split; last done.
    exact/Is_true_true.
  + rewrite (Hbot x Hx Px).
    exact: bottom_sqsubseteq.
- apply/join_list_sqsubseteq =>
    _ /elem_of_list_fmap
      [x [-> Hx]].
  apply elem_of_list_filter in Hx
    as [_ Hx].
  apply: sqsubseteq_join_list.
  by apply/elem_of_list_fmap; exists x.
Qed.

(** Suffix terms for strings violating the output
    bound are ⊥. *)
Lemma suffix_bot_of_bound_violated
  (s : list (T + T)) :
  output_bounded adjusted_fanout s = false →
  string_suffix_term_at
    (fsa_initial A) s ≡ ⊥.
Proof.
rewrite /output_bounded
  /string_suffix_term_at
  => /Nat.leb_gt Hgt.
have Hbot : fsa_interp
  (fsa_trans_s s (fsa_initial A)) ≡ ⊥.
{ destruct (either_empty_or_nonzero
    (fsa_interp
      (fsa_trans_s s (fsa_initial A))))
    as [Hbot|[w Hw]]; first done.
  exfalso.
  have Hne : fsa_interp
      (fsa_trans_s s (fsa_initial A)) ≢ ⊥.
  { move=> Hbot. move: Hw.
    by rewrite Hbot
      pre_ka_morphism_bottom. }
  have /= Hle := @lemma_31_bound
    (fsa_initial A) s
    (fsa_interp_initial A) Hne.
  rewrite /= in Hgt. lia. }
by rewrite Hbot right_absorb.
Qed.

(** The adjusted fanout is a valid fanout for e. *)
Lemma adjusted_fanout_ge :
  k0 ≤ adjusted_fanout.
Proof.
rewrite /adjusted_fanout. nia.
Qed.

Lemma adjusted_fanout_bounded_output :
  bounded_output_with
    adjusted_fanout (fsa_elem A).
Proof.
exact: bounded_output_with_mono
  adjusted_fanout_ge Hbo.
Qed.

(** Lemma 31 (paper version): For a bounded-output
    finite-state term, there exists k such that e has
    fanout k and the expansion from Lemma 27 can
    be restricted to output-bounded suffix terms.

    Concretely, for every n:
    e ≡ Σ{s | s ≤ e, |s| < n}
      ⊔ Σ{s·e_s | |s| = n,
            |πr(s)| ≤ (|πl(s)|+1)·k}
    where k = adjusted_fanout. *)
Lemma lemma_31_paper (n : nat) :
  fsa_elem A ≡
    sum_terms_lt_k_at (fsa_initial A) n ⊔
    bounded_suffix_sum_at
      (fsa_initial A) n adjusted_fanout.
Proof.
rewrite -(fsa_interp_initial A)
  (fsa_elem_k_decomp_gen
    (fsa_initial A) n).
f_equiv.
rewrite /sum_suffix_terms_k_at
  /bounded_suffix_sum_at.
apply: join_list_filter_bot.
move=> s _ Hfalse.
exact: suffix_bot_of_bound_violated Hfalse.
Qed.

End Lemma31.

(** Lemma 34 (from paper): A finite-state, bounded-output term whose
    domain and codomain lie in a prefix-free language is representable. *)

Lemma bounded_output_repr_rel e L :
  finite_state e →
  bounded_output e →
  ka_term_proj1 e ⊑ L →
  ka_term_proj2 e ⊑ L →
  prefix_free L →
  repr_rel e L.
Proof.
move=> Hfs Hbo Hdom Hcod Hpf.
have [A EA] := finite_stateP Hfs.
have Hbo' : bounded_output (fsa_elem A).
{ destruct Hbo as [k Hk]. exists k. move=> sl sr Hin. apply: Hk.
  by rewrite EA. }
(* ρ_e: join of all state interpretations *)
set rho_e := ⨆ (map (λ σ : fsa_state A, fsa_interp σ)
                     (enum (fsa_state A))).
(* Residue per paper: Σ̈* · ρ_e *)
refine {|
  repr_rel_dom := Hdom;
  repr_rel_cod := Hcod;
  next := fsa_next Hbo';
  residue := pseudo_top ⋅ rho_e;
|}.
- (* next_spec *)
  move=> sl sr.
  rewrite fsa_next_spec. by rewrite EA.
- (* expand_rel *)
  move=> xs Hxs.
  rewrite {1}EA -(fsa_interp_initial A).
  (* ρ_e ≥ 1: the automaton has a final state *)
  have Hone_rho : 1 ⊑ rho_e.
  { admit. }
  (* e_{s'} ⊑ ρ_e for suffix states *)
  have Hstate_rho : ∀ σ : fsa_state A, fsa_interp σ ⊑ rho_e.
  { move=> σ. apply: sqsubseteq_join_list. apply/elem_of_list_fmap.
    exists σ; split => //. exact: elem_of_enum. }
  (* Choose k, p as in paper *)
  destruct Hbo' as [k0 Hk0].
  set n := length xs.
  set p := (k0 + 1) * (n + 1).
  (* Decompose fsa_elem A at level p+1.
     By paper: e = Σ{|s'|≤p} s' + Σ{s'∈Λ̈} s' · e_{s'} *)
  rewrite {1}(fsa_elem_k_decomp_gen (fsa_initial A) (S p)).
  rewrite pre_ka_right_dist join_sqsubseteq.
  split.
  + (* Matched strings (4)+(5) *)
    admit.
  + (* Suffix terms (6): For each s' ∈ Λ̈, show
       s_r · s' · e_{s'} ≤ Σ* · Σ≠ · ρ. If e_{s'} = 0, done.
       Otherwise find witness s'' ≤ e_{s'}, show |πl(s')| > n,
       factor through dpt · diff · pt, multiply by e_{s'} ≤ ρ_e.
       Paper eq (6): for each suffix s', either e_{s'} = 0 (done)
       or find witness, show |πl(s')| > n by bounded output
       contradiction, factor s_r·s' through dpt·diff·pt,
       multiply by e_{s'} ≤ ρ_e. *)
    admit.
Admitted.


End BoundedOutput.
