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

From kacc Require Import utils algebra pre_ka lang.

Section Automata.

Context (Σ : Type) `{!EqDecision Σ, !Finite Σ}.
Context (T : pre_ka) (f : Σ → T).

Record fsa := FSA {
  fsa_state : Type;
  fsa_elem : T;
  fsa_state_eq_dec : EqDecision fsa_state;
  fsa_state_finite : Finite fsa_state;
  fsa_initial : fsa_state;
  fsa_final : fsa_state → bool;
  fsa_interp : fsa_state → T;
  fsa_trans : Σ → fsa_state → fsa_state;
  fsa_interp_initial : fsa_interp fsa_initial ≡ fsa_elem;
  fsa_derivable : ∀ σ : fsa_state,
    fsa_interp σ ≡
    pre_ka_of_bool (fsa_final σ) ⊔
    ⨆ a ∈ enum Σ, f a ⋅ fsa_interp (fsa_trans a σ);
}.

Arguments fsa_trans {_}.

Global Existing Instance fsa_state_eq_dec.
Global Existing Instance fsa_state_finite.

Implicit Types (A B : fsa).

Program Definition fsa_bottom : fsa := {|
  fsa_state := unit;
  fsa_elem := ⊥;
  fsa_initial := tt;
  fsa_final _ := false;
  fsa_interp σ := ⊥;
  fsa_trans x σ := tt;
|}.

Next Obligation. by []. Qed.

Next Obligation.
move=> []; rewrite left_id join_list_bottom // => a.
by rewrite right_absorb.
Qed.

Program Definition fsa_join A B : fsa := {|
  fsa_state := fsa_state A * fsa_state B;
  fsa_elem := fsa_elem A ⊔ fsa_elem B;
  fsa_initial := (fsa_initial A, fsa_initial B);
  fsa_final := λ σ, fsa_final σ.1 || fsa_final σ.2;
  fsa_interp := λ σ, fsa_interp σ.1 ⊔ fsa_interp σ.2;
  fsa_trans := λ x σ, (fsa_trans x σ.1, fsa_trans x σ.2);
|}.

Next Obligation.
by move=> A B /=; rewrite !fsa_interp_initial.
Qed.

Next Obligation.
move=> A B [σA σB] /=.
rewrite (fsa_derivable σA) (fsa_derivable σB) pre_ka_of_bool_or.
set A1 := pre_ka_of_bool (fsa_final σA).
set B1 := pre_ka_of_bool (fsa_final σB).
rewrite assoc -[_ ⊔ _ ⊔ B1]assoc [_ ⊔ B1]comm assoc.
rewrite -[((A1 ⊔ B1) ⊔ _) ⊔ _]assoc.
rewrite -join_list_join; f_equiv.
apply join_list_ext => ? _.
by rewrite pre_ka_right_dist.
Qed.

Record nfa := NFA {
  nfa_state : semi_lattice;
  nfa_state_leibniz : LeibnizEquiv nfa_state;
  nfa_state_eq_dec : EqDecision nfa_state;
  nfa_state_finite : Finite nfa_state;
  nfa_elem : T;
  nfa_initial : nfa_state;
  nfa_final : nfa_state → bool;
  nfa_final_bottom : nfa_final ⊥ = false;
  nfa_final_join : ∀ σ₁ σ₂,
    nfa_final (σ₁ ⊔ σ₂) = nfa_final σ₁ || nfa_final σ₂;
  nfa_interp : nfa_state → T;
  nfa_interp_bottom : nfa_interp ⊥ ≡ ⊥;
  nfa_interp_join : ∀ σ₁ σ₂,
    nfa_interp (σ₁ ⊔ σ₂) ≡ nfa_interp σ₁ ⊔ nfa_interp σ₂;
  nfa_interp_initial : nfa_interp nfa_initial ≡ nfa_elem;
  nfa_trans : Σ → nfa_state → nfa_state;
  nfa_trans_bottom : ∀ x, nfa_trans x ⊥ = ⊥;
  nfa_trans_join : ∀ x σ₁ σ₂,
    nfa_trans x (σ₁ ⊔ σ₂) = nfa_trans x σ₁ ⊔ nfa_trans x σ₂;
  nfa_derivable : ∀ σ : nfa_state,
    nfa_interp σ ≡
    pre_ka_of_bool (nfa_final σ) ⊔
    ⨆ a ∈ enum Σ, f a ⋅ nfa_interp (nfa_trans a σ);
}.

Global Existing Instance nfa_state_leibniz.
Global Existing Instance nfa_state_eq_dec.
Global Existing Instance nfa_state_finite.

Program Definition fsa_to_nfa A : nfa := {|
  nfa_state := gset (fsa_state A);
  nfa_elem := fsa_elem A;
  nfa_initial := {[fsa_initial A]};
  nfa_final Σ := existsb (λ σ, fsa_final σ) (elements Σ);
  nfa_interp Σ := ⨆ σ ∈ elements Σ, fsa_interp σ;
  nfa_trans x Σ := list_to_set (map (fsa_trans x) (elements Σ));
|}.

Next Obligation.
by move=> A; rewrite /= elements_empty.
Qed.

Next Obligation.
move=> A σ₁ σ₂; apply: eq_bool_prop_intro.
rewrite orb_True !existb_True !Exists_exists; split.
- case=> a [] /elem_of_elements-/elem_of_union [] a_σ final_a.
  + by left; exists a; split; rewrite // elem_of_elements.
  + by right; exists a; split; rewrite // elem_of_elements.
- by case; case=> a [] /elem_of_elements a_σ final_a; exists a;
  rewrite elem_of_elements elem_of_union; eauto.
Qed.

Next Obligation.
by move=> A; rewrite /= elements_empty.
Qed.

Next Obligation.
move=> A Σ₁ Σ₂ /=; apply: (anti_symm _).
- rewrite join_list_sqsubseteq => σ.
  rewrite elem_of_elements elem_of_union; case=> σ_Σ.
  + etransitivity; last exact: sqsubseteq_join_left.
    apply: sqsubseteq_join_list.
    by rewrite elem_of_elements.
  + etransitivity; last exact: sqsubseteq_join_right.
    apply: sqsubseteq_join_list.
    by rewrite elem_of_elements.
- rewrite join_sqsubseteq; split.
  + rewrite join_list_sqsubseteq => σ.
    rewrite elem_of_elements => σ_Σ.
    apply: sqsubseteq_join_list.
    by rewrite elem_of_elements elem_of_union; eauto.
  + rewrite join_list_sqsubseteq => σ.
    rewrite elem_of_elements => σ_Σ.
    apply: sqsubseteq_join_list.
    by rewrite elem_of_elements elem_of_union; eauto.
Qed.

Next Obligation.
move=> A; rewrite /= elements_singleton /= right_id.
by rewrite fsa_interp_initial.
Qed.

Next Obligation.
by move=> A x /=; rewrite elements_empty /=.
Qed.

Next Obligation.
move=> X x /= σ₁ σ₂; apply sets.set_eq=> a.
rewrite elem_of_union !elem_of_list_to_set; split.
- case/elem_of_list_fmap=> b [] -> /elem_of_elements.
  case/elem_of_union=> b_σ.
  + left; apply/elem_of_list_fmap; exists b; rewrite elem_of_elements.
    by eauto.
  + right; apply/elem_of_list_fmap; exists b; rewrite elem_of_elements.
    by eauto.
- case; case/elem_of_list_fmap=> b [] -> /elem_of_elements b_σ.
  + apply/elem_of_list_fmap; exists b; split => //.
    by rewrite elem_of_elements elem_of_union; left.
  + apply/elem_of_list_fmap; exists b; split => //.
    by rewrite elem_of_elements elem_of_union; right.
Qed.

Next Obligation.
move=> A Σ' /=; apply: (anti_symm _).
- rewrite join_list_sqsubseteq => σ' σ'_Σ'.
  rewrite fsa_derivable; apply: join_mono.
  + case final_σ': (fsa_final σ');
      last exact: bottom_sqsubseteq.
    rewrite (_ : existsb _ _ = true) //.
    apply/existsb_exists; exists σ'; split => //.
    by rewrite -elem_of_list_In.
  + rewrite join_list_sqsubseteq => a _.
    transitivity
      (f a ⋅ ⨆ σ ∈ elements
        (list_to_set (map (fsa_trans a)
          (elements Σ')) : gset _),
        fsa_interp σ).
    * apply: pre_ka_mul_mono=> //=.
      apply: sqsubseteq_join_list.
      rewrite elem_of_elements elem_of_list_to_set.
      by apply/elem_of_list_fmap; eexists _; split.
    * apply: (sqsubseteq_join_list
        (λ a, f a ⋅ _)).
      exact: elem_of_enum.
- rewrite join_sqsubseteq; split.
  + case e: existsb; last exact: bottom_sqsubseteq.
    case/existsb_exists: e =>
      σ [] /elem_of_list_In σ_Σ' final_σ.
    transitivity (fsa_interp σ).
    * rewrite fsa_derivable final_σ.
      exact: sqsubseteq_join_left.
    * exact: sqsubseteq_join_list.
  + rewrite join_list_sqsubseteq => a _.
    rewrite join_list_right_dist
      join_list_sqsubseteq => σ.
    rewrite elem_of_elements elem_of_list_to_set.
    case/elem_of_list_fmap=> σ' [] -> σ'_Σ'.
    transitivity (fsa_interp σ').
    * rewrite (fsa_derivable σ').
      etransitivity;
        last exact: sqsubseteq_join_right.
      apply: (sqsubseteq_join_list
        (λ a, f a ⋅ _)).
      exact: elem_of_enum.
    * exact: sqsubseteq_join_list.
Qed.

Section FSAMul.

Variables (A : fsa) (B : nfa).

Implicit Types (σ : fsa_state A * nfa_state B).
Implicit Types (σA : fsa_state A) (σB : nfa_state B).

Let saturate σ :=
  (σ.1, σ.2 ⊔ if fsa_final σ.1 then nfa_initial B else ⊥).

Let final σ := nfa_final (saturate σ).2.

Let interp σ := fsa_interp σ.1 ⋅ nfa_elem B ⊔ nfa_interp σ.2.

Let trans x σ := (fsa_trans x σ.1, nfa_trans x σ.2).

Lemma mul_interp_trans_saturate x σ :
  interp (trans x (saturate σ)) ≡
  fsa_interp (fsa_trans x σ.1) ⋅ nfa_elem B ⊔
  nfa_interp (nfa_trans x σ.2) ⊔
  pre_ka_of_bool (fsa_final σ.1) ⋅ nfa_interp (nfa_trans x (nfa_initial B)).
Proof.
rewrite /interp /trans /saturate /=.
rewrite nfa_trans_join nfa_interp_join assoc.
case: fsa_final; rewrite //= ?left_id // left_absorb.
by rewrite nfa_trans_bottom nfa_interp_bottom.
Qed.

Lemma mul_derive_trans_saturate σ :
  (⨆ a ∈ enum Σ,
    f a ⋅ interp (trans a (saturate σ))) ≡
  (⨆ a ∈ enum Σ,
    f a ⋅ fsa_interp (fsa_trans a σ.1))
    ⋅ nfa_elem B ⊔
  (⨆ a ∈ enum Σ,
    f a ⋅ nfa_interp (nfa_trans a σ.2)) ⊔
  pre_ka_of_bool (fsa_final σ.1) ⋅
    (⨆ a ∈ enum Σ,
      f a ⋅ nfa_interp (nfa_trans a (nfa_initial B))).
Proof.
rewrite join_list_right_dist join_list_left_dist.
rewrite -!join_list_join.
apply join_list_ext => a _.
rewrite mul_interp_trans_saturate
  !pre_ka_right_dist !assoc.
by case: fsa_final;
  rewrite /= ?(left_id, right_id,
    left_absorb, right_absorb).
Qed.

Lemma pre_ka_of_bool_final σ :
  @pre_ka_of_bool T (final σ) ≡
  pre_ka_of_bool (fsa_final σ.1) ⋅
    pre_ka_of_bool (nfa_final (nfa_initial B)) ⊔
  pre_ka_of_bool (nfa_final σ.2).
Proof.
rewrite /final /saturate /= nfa_final_join pre_ka_of_bool_or.
rewrite comm; apply: semi_lattice_proper => //.
case: fsa_final; rewrite /= ?nfa_final_bottom ?left_absorb //.
by rewrite left_id.
Qed.

Program Definition fsa_mul : fsa := {|
  fsa_state := fsa_state A * nfa_state B;
  fsa_elem := fsa_elem A ⋅ nfa_elem B;
  fsa_initial := (fsa_initial A, ⊥);
  fsa_final := final;
  fsa_interp := interp;
  fsa_trans x σ := trans x (saturate σ);
|}.

Next Obligation.
by rewrite /interp /= nfa_interp_bottom right_id fsa_interp_initial.
Qed.

Next Obligation.
move=> σ.
rewrite mul_derive_trans_saturate /interp.
rewrite pre_ka_of_bool_final.
rewrite [_ ⊔ pre_ka_of_bool (fsa_final σ.1) ⋅ _]comm assoc.
rewrite -[pre_ka_of_bool _ ⋅ _ ⊔ _ ⊔ _]assoc.
rewrite [_ ⊔ pre_ka_of_bool (fsa_final σ.1) ⋅ _]comm assoc.
rewrite -pre_ka_right_dist -nfa_derivable nfa_interp_initial !assoc.
rewrite -[_ ⋅ nfa_elem B ⊔ _ ⊔ _]assoc [_ ⊔ _ ⋅ nfa_elem B]comm assoc.
by rewrite -pre_ka_left_dist -fsa_derivable -assoc -nfa_derivable.
Qed.

End FSAMul.

Definition fsa_mul' (A B : fsa) : fsa :=
  fsa_mul A (fsa_to_nfa B).

Section FSAStar.

Variables (A : nfa).
Implicit Types (x : Σ) (σ : option (nfa_state A)).

Let interp σ :=
  pre_ka_of_bool (negb (nfa_final (nfa_initial A))) ⋅
  match σ with
  | Some σA => nfa_interp σA
  | None => 1
  end ⋅ star (nfa_elem A).

Let final σ :=
  negb (nfa_final (nfa_initial A)) &&
  match σ with
  | Some σA => nfa_final σA
  | None => true
  end.

Let elem :=
  pre_ka_of_bool (negb (nfa_final (nfa_initial A))) ⋅
  star (nfa_elem A).

Let trans x σ :=
  Some (nfa_trans x
          match σ with
          | Some σA =>
            (if nfa_final σA then nfa_initial A else ⊥) ⊔ σA
          | None =>
            nfa_initial A
          end).

Lemma star_interp_trans x σ :
  interp (trans x σ) ≡
  if nfa_final (nfa_initial A) then ⊥
  else
    pre_ka_of_bool (match σ with Some σA => nfa_final σA | None => true end) ⋅
    nfa_interp (nfa_trans x (nfa_initial A)) ⋅
    star (nfa_elem A) ⊔
    nfa_interp (nfa_trans x (match σ with Some σA => σA | None => ⊥ end)) ⋅
    star (nfa_elem A).
Proof.
rewrite /interp; case: (nfa_final _); rewrite /= ?left_absorb //.
rewrite left_id; case: σ => [σA|] /=; last first.
  by rewrite left_id nfa_trans_bottom nfa_interp_bottom left_absorb right_id.
case: nfa_final => /=.
- by rewrite nfa_trans_join nfa_interp_join pre_ka_left_dist left_id.
- rewrite nfa_trans_join nfa_trans_bottom nfa_interp_join nfa_interp_bottom.
  by rewrite left_id !left_absorb left_id.
Qed.

Lemma star_derive_trans σ :
  ⨆ a ∈ enum Σ, f a ⋅ interp (trans a σ) ≡
  if nfa_final (nfa_initial A) then ⊥
  else match σ with
  | Some σA =>
    if nfa_final σA then
      (⨆ a ∈ enum Σ,
        f a ⋅ nfa_interp
          (nfa_trans a (nfa_initial A))) ⋅
      star (nfa_elem A) ⊔
      (⨆ a ∈ enum Σ,
        f a ⋅ nfa_interp (nfa_trans a σA)) ⋅
      star (nfa_elem A)
    else
      (⨆ a ∈ enum Σ,
        f a ⋅ nfa_interp (nfa_trans a σA)) ⋅
      star (nfa_elem A)
  | None =>
    (⨆ a ∈ enum Σ,
      f a ⋅ nfa_interp
        (nfa_trans a (nfa_initial A))) ⋅
    star (nfa_elem A)
  end.
Proof.
case final_A: nfa_final.
  rewrite join_list_bottom // => a.
  by rewrite star_interp_trans final_A
    right_absorb.
case: σ => [σA|] /=; last first.
  rewrite join_list_left_dist.
  apply join_list_ext => a _.
  rewrite star_interp_trans final_A /=.
  rewrite nfa_trans_bottom nfa_interp_bottom.
  by rewrite left_absorb right_id left_id assoc.
case final_σA: nfa_final; last first.
  rewrite join_list_left_dist.
  apply join_list_ext => a _.
  by rewrite star_interp_trans final_A final_σA
    /= !left_absorb left_id assoc.
rewrite -pre_ka_left_dist -join_list_join
  join_list_left_dist.
apply join_list_ext => a _.
rewrite star_interp_trans /= final_A /=
  final_σA left_id pre_ka_left_dist.
by rewrite pre_ka_right_dist !assoc.
Qed.

Program Definition fsa_star : fsa := {|
  fsa_state := option (nfa_state A);
  fsa_elem := elem;
  fsa_initial := None;
  fsa_final := final;
  fsa_interp := interp;
  fsa_trans := trans;
|}.

Next Obligation.
by rewrite /elem /interp /= right_id.
Qed.

Next Obligation.
move=> σ; rewrite star_derive_trans /final {1}/interp.
case final_A: nfa_final; rewrite /= ?left_absorb ?left_id //.
case: σ=> [σA|] /=; last first.
  rewrite left_id {1}pre_ka_star_unfold -{1}nfa_interp_initial.
  by rewrite nfa_derivable final_A /= left_id.
rewrite nfa_derivable pre_ka_left_dist {1}pre_ka_star_unfold.
rewrite pre_ka_right_dist right_id -!assoc.
apply: semi_lattice_proper => //.
case final_σA: nfa_final; rewrite //= ?left_absorb ?left_id //.
apply: semi_lattice_proper => //.
by rewrite -{1}nfa_interp_initial nfa_derivable final_A left_id.
Qed.

End FSAStar.

Definition fsa_star' A : fsa := fsa_star (fsa_to_nfa A).

Lemma fsa_elem_star' A :
  fsa_final (fsa_initial A) = false →
  fsa_elem (fsa_star' A) ≡ star (fsa_elem A).
Proof.
by move=> final_A; rewrite /= elements_singleton /= final_A /= left_id.
Qed.

Program Definition fsa_singleton x : fsa := {|
  fsa_state := option bool;
  fsa_elem := f x;
  fsa_initial := None;
  fsa_final σ :=
    match σ return bool with
    | Some b => b
    | _ => false
    end;
  fsa_interp σ :=
    match σ return T with
    | Some b => pre_ka_of_bool b
    | None => f x
    end;
  fsa_trans y σ :=
    match σ return option bool with
    | Some _ => Some false
    | None => Some (bool_decide (x = y))
    end;
|}.

Next Obligation. by rewrite /=. Qed.

Next Obligation.
move=> x [[]|] /=.
- rewrite join_list_bottom ?right_id // => a.
  by rewrite right_absorb.
- rewrite join_list_bottom ?right_id // => a.
  by rewrite right_absorb.
- rewrite left_id.
  have <-: f x ⋅ 1 ≡ f x by exact: right_id.
  apply (anti_symm _).
  + have -> : (1 : T) ≡
      pre_ka_of_bool (bool_decide (x = x)).
    { by rewrite bool_decide_eq_true_2. }
    exact: sqsubseteq_join_list _ _ _
      (elem_of_enum x).
  + apply/join_list_sqsubseteq => y _.
    rewrite /=.
    case: bool_decide_reflect => [<- //|ne].
    rewrite right_absorb /=.
    exact: bottom_sqsubseteq.
Qed.

Definition fsa_one :=
  fsa_star (fsa_to_nfa fsa_bottom).

Lemma fsa_elem_one : fsa_elem fsa_one ≡ 1.
Proof. by rewrite /= elements_singleton /= star_bottom left_id. Qed.

Definition fsa_mul_list (As : list fsa) : fsa :=
  foldr fsa_mul' fsa_one As.

Lemma fsa_elem_mul_list As :
  fsa_elem (fsa_mul_list As) ≡
  ∏ a ∈ As, fsa_elem a.
Proof.
by elim: As => /= [|A As ->];
  rewrite // -fsa_elem_one.
Qed.


Definition fsa_trans_s (A : fsa) (s : list Σ) (σ : fsa_state A) :=
  foldl (flip fsa_trans) σ s.

Lemma fsa_trans_s_cons (A : fsa) (x : Σ) (s : list Σ) (σ : fsa_state A) :
  fsa_interp (fsa_trans_s (x :: s) σ) ≡
  fsa_interp (fsa_trans_s s (fsa_trans x σ)).
Proof.
  rewrite //=.
Qed.

Lemma fsa_trans_s_app (A : fsa) (x : Σ) (s : list Σ) (σ : fsa_state A) :
  fsa_interp (fsa_trans_s (s ++ [x]) σ) ≡
  fsa_interp
    (fsa_trans x (fsa_trans_s s σ)).
Proof.
elim: s σ => [// | /= x' s' IH σ].
by rewrite IH.
Qed.


Definition string_match_at A (σ : fsa_state A) s :=
  fsa_final (fsa_trans_s s σ).

Definition string_match (A : fsa) (s : list Σ) :=
  string_match_at (fsa_initial A) s.

Definition ka_of_string s := ∏ a ∈ s, f a.

Lemma ka_of_string_concat_l ys (y : Σ) :
  ka_of_string ys ⋅ f y ≡ ka_of_string (ys ++ [y]).
Proof.
rewrite /ka_of_string;
elim: ys => /= [|y' ys IHys]; first by rewrite ?right_id ?left_id.
by rewrite -assoc; rewrite IHys.
Qed.

Lemma ka_of_string_concat_r ys (y : Σ) :
  f y ⋅ ka_of_string ys ≡ ka_of_string (y :: ys).
Proof. rewrite //=. Qed.

Definition sum_terms_lt_k_at A (σ : fsa_state A) k :=
  ⨆ s ∈ filter (string_match_at σ) (enum_list_lt k),
    ka_of_string s.

Definition sum_terms_lt_k A k :=
  sum_terms_lt_k_at (fsa_initial A) k.


Definition sum_terms_eq_k_at A (σ : fsa_state A) k :=
  ⨆ s ∈ filter (string_match_at σ) (enum_list_eq k),
    ka_of_string s.

Definition sum_terms_eq_k A k := sum_terms_eq_k_at (fsa_initial A) k.

Definition string_suffix_at A (σ : fsa_state A) s :=
  fsa_interp (fsa_trans_s s σ).

Definition string_suffix A s :=
  string_suffix_at (fsa_initial A) s.

Definition string_suffix_term_at A (σ : fsa_state A) s :=
  (ka_of_string s) ⋅ fsa_interp (fsa_trans_s s σ).

Definition sum_suffix_terms_k_at A (σ : fsa_state A) k :=
  ⨆ s ∈ enum_list_eq k, string_suffix_term_at σ s.

Lemma join_map_mul_dist {B : Type} (t1 t2 t3 : B -> T) (ls : list B) :
  ⨆ s ∈ ls, t1 s ⋅ (t2 s ⊔ t3 s)
  ≡ (⨆ s ∈ ls, t1 s ⋅ t2 s) ⊔ (⨆ s ∈ ls, t1 s ⋅ t3 s).
Proof.
have G : (⨆ s ∈ ls, t1 s ⋅ (t2 s ⊔ t3 s)) ≡
  (⨆ s ∈ ls, (t1 s ⋅ t2 s) ⊔ t1 s ⋅ t3 s).
{ apply join_list_ext => a _; by rewrite pre_ka_right_dist. }
rewrite {}G; exact: join_list_join.
Qed.

Lemma string_derive_one_more_at
    A (σ : fsa_state A) k :
  (⨆ s ∈ enum_list_eq k,
    ka_of_string s ⋅ fsa_interp (fsa_trans_s s σ))
  ≡ (⨆ s ∈ enum_list_eq k,
      ka_of_string s ⋅ (
        pre_ka_of_bool (fsa_final (fsa_trans_s s σ))
        ⊔ ⨆ a ∈ enum Σ,
            f a ⋅ fsa_interp
              (fsa_trans a (fsa_trans_s s σ)))).
Proof.
apply join_list_ext => ? _.
by rewrite fsa_derivable.
Qed.

Lemma sum_terms_lt_S_k_at A (σ : fsa_state A) k :
sum_terms_lt_k_at σ (S k) ≡ sum_terms_lt_k_at σ k ⊔ sum_terms_eq_k_at σ k.
Proof.
rewrite /sum_terms_lt_k_at /sum_terms_eq_k_at {1}/enum_list_lt.
replace (S k) with (k + 1); last by lia.
(* QUEST: there are some annoying rewrites/unfolds here...is this ok? *)
by rewrite /string_match seq_app //= flat_map_app
           filter_app flat_map_enum_list_eq_id
           join_list_app /enum_list_lt.
Qed.

Lemma sum_terms_lt_k__to__S_k_at
    A (σ : fsa_state A) k :
  sum_terms_lt_k_at σ k ⊔
  (⨆ s ∈ enum_list_eq k,
    ka_of_string s ⋅
      pre_ka_of_bool
        (fsa_final (fsa_trans_s s σ)))
  ≡ sum_terms_lt_k_at σ (S k).
Proof.
rewrite sum_terms_lt_S_k_at; f_equiv.
rewrite /sum_terms_eq_k_at /string_match_at.
elim: (enum_list_eq k) => [| en1 en' IHen]; first rewrite //=.
rewrite /=; case en1Final: (fsa_final (fsa_trans_s en1 σ));
rewrite filter_cons en1Final /ka_of_string.
- by rewrite ?right_id /=; f_equiv.
- rewrite ?right_absorb ?left_id //=.
Qed.


Lemma fsa_elem_k_decomp_gen A (σ : fsa_state A) (k : nat):
  fsa_interp σ ≡ sum_terms_lt_k_at σ k ⊔ sum_suffix_terms_k_at σ k.
Proof.
elim: k => [| k IHk] /=;
first by rewrite /sum_terms_lt_k_at /sum_suffix_terms_k_at
             /string_suffix_term_at /ka_of_string /= ?left_id ?right_id.
rewrite {}IHk {1}/sum_suffix_terms_k_at /string_suffix_at.
rewrite string_derive_one_more_at join_map_mul_dist
        assoc sum_terms_lt_k__to__S_k_at; f_equiv.
rewrite /sum_suffix_terms_k_at
  /string_suffix_term_at.
apply (anti_symm _); apply join_list_sqsubseteq;
move=> xs Hxs.
- rewrite join_list_right_dist.
  apply join_list_sqsubseteq => a a_enum.
  rewrite assoc ka_of_string_concat_l
    -fsa_trans_s_app.
  move: Hxs => /elem_of_enum_list_eq.
  have {a a_enum xs} [x [xs' [-> ->]]] :=
    destruct_list_app_len a xs.
  move=> /elem_of_enum_list_eq Hxs'.
  have Hmem : (x :: xs') ∈
    enum_list_eq (S k).
  { rewrite enum_list_eq_Sn.
    apply/elem_of_list_fmap.
    exists (x, xs'); split; first done.
    apply elem_of_concat.
    exists (map (pair x)
      (enum_list_eq k)).
    split; apply elem_of_list_fmap.
    + exists x; split;
        [done | exact: elem_of_enum].
    + exists xs'; done. }
  exact: sqsubseteq_join_list
    _ _ _ Hmem.
- have Hxs' := Hxs.
  rewrite enum_list_eq_Sn in Hxs'.
  move: Hxs' => /elem_of_list_fmap
    [xpair [-> Hxpair]].
  move: Hxpair; rewrite /all_pairs =>
    {xpair}
    /elem_of_concat [_ [
      /elem_of_list_fmap [x [-> Hxenum]]
      /elem_of_list_fmap [xs' [-> Hxs']]
    ]].
  move: Hxs' => /elem_of_enum_list_eq.
  have {x xs' xs Hxs Hxenum}
    [x [xs' [-> ->]]] :=
    destruct_list_cons_len x xs'.
  move=> /elem_of_enum_list_eq Hxs'.
  rewrite /= -ka_of_string_concat_l -assoc
    fsa_trans_s_app.
  etransitivity; last
    exact: sqsubseteq_join_list _ _ _ Hxs'.
  rewrite join_list_right_dist.
  have Hx : x ∈ enum Σ by exact: elem_of_enum.
  exact: sqsubseteq_join_list _ _ _ Hx.
Qed.


(** Connection between string_match and fsa_interp / fsa_elem. *)

Lemma string_match_at_sound A (σ : fsa_state A) (s : list Σ) :
  string_match_at σ s = true →
  ka_of_string s ⊑ fsa_interp σ.
Proof.
move=> Hmatch.
have Hdecomp := fsa_elem_k_decomp_gen σ (S (length s)).
have Hlt : ka_of_string s ⊑ sum_terms_lt_k_at σ (S (length s)).
{ rewrite /sum_terms_lt_k_at.
  apply: sqsubseteq_join_list.
  rewrite elem_of_list_filter elem_of_enum_list_lt
    /= Hmatch. split => //. lia. }
etransitivity; first exact: Hlt.
rewrite sqsubseteq_iff Hdecomp assoc semi_lattice_idemp //.
Qed.

Lemma string_match_sound A (s : list Σ) :
  string_match A s = true →
  ka_of_string s ⊑ fsa_elem A.
Proof.
rewrite /string_match => Hmatch.
have H := string_match_at_sound Hmatch.
etransitivity; first exact: H.
rewrite sqsubseteq_iff fsa_interp_initial semi_lattice_idemp //.
Qed.

End Automata.

Global Arguments fsa_one {Σ _ _ _ _}.
Global Arguments fsa_singleton {Σ _ _ _ _}.
Global Arguments fsa Σ {_ _} T.
Global Arguments fsa_mul' {Σ _ _ _ _}.
Global Arguments nfa Σ {_ _} T.


Section AlphabetChange.

Context `{!EqDecision Σ, !Finite Σ, !EqDecision Σ', !Finite Σ'}.
Context {T : pre_ka}.

Variables (f : Σ → T) (f' : Σ' → T) (t : Σ → Σ') (s : Σ' → option Σ).

Hypothesis f_f' : ∀ x, f' (t x) ≡ f x.
Hypothesis tK : ∀ x, s (t x) = Some x.

Program Definition nfa_alphabet_change (A : nfa Σ T f) : fsa Σ' T f' := {|
  fsa_state := nfa_state A;
  fsa_elem := nfa_elem A;
  fsa_initial := nfa_initial A;
  fsa_final σ := @nfa_final _ _ _ _ _ A σ;
  fsa_interp σ := nfa_interp σ;
  fsa_trans y σ :=
    match s y return nfa_state A with
    | Some x => nfa_trans x σ
    | None => ⊥
    end;
|}.

Next Obligation. move=> A; exact: nfa_interp_initial. Qed.

Next Obligation. Admitted.

Definition fsa_alphabet_change (A : fsa Σ T f) : fsa Σ' T f' :=
  nfa_alphabet_change (fsa_to_nfa A).

Lemma fsa_alphabet_change_elem A :
  fsa_elem (fsa_alphabet_change A) = fsa_elem A.
Proof. by []. Qed.

End AlphabetChange.

Section AlgebraChange.

Context `{!EqDecision Σ, !Finite Σ}.
Context `{T : pre_ka, T' : pre_ka, t : T → T', !PreKAMorphism t}.
Context (f : Σ → T).

Program Definition fsa_algebra_change (A : fsa Σ T f) : fsa Σ T' (t ∘ f) := {|
  fsa_state := fsa_state A;
  fsa_elem := t (fsa_elem A);
  fsa_initial := fsa_initial A;
  fsa_final σ := fsa_final σ;
  fsa_interp σ := t (fsa_interp σ);
  fsa_trans y σ := fsa_trans y σ;
|}.

Next Obligation.
by move=> A; rewrite /= fsa_interp_initial.
Qed.

Next Obligation.
move=> A σ; rewrite /= fsa_derivable semi_lattice_morphism_join.
rewrite pre_ka_morphism_of_bool; f_equiv.
rewrite semi_lattice_morphism_join_list; f_equiv.
by move=> x _ <-; rewrite /= monoid_morphism_mul.
Qed.

Lemma fsa_algebra_change_elem A :
  fsa_elem (fsa_algebra_change A) = t (fsa_elem A).
Proof. by []. Qed.

End AlgebraChange.

Section StringMatchComplete.

Context {M : monoid} {G : Type} `{!EqDecision G, !Finite G}.
Context `{!MonoidGen G M, !SizedMonoid G M}.

Let T := ka_term M.
Let f : G → T := Unit ∘ generator_interp.

(** ka_of_string f s ≡ Unit (∏ a ∈ s, gen a) *)

Lemma ka_of_string_Unit (s : list G) :
  ka_of_string f s ≡
  Unit (∏ a ∈ s, generator_interp a).
Proof.
rewrite /ka_of_string /f
  monoid_morphism_mul_list //.
Qed.

(** msize of the monoid element encoded by s is length s *)

Lemma ka_of_string_msize (s : list G) :
  msize (∏ a ∈ s, generator_interp a) = length s.
Proof. symmetry. exact: sized_monoid. Qed.

(** Two ka_of_string are ≡ only if they have the same length *)

Lemma ka_of_string_sized (s1 s2 : list G) :
  ka_of_string f s1 ≡ ka_of_string f s2 → length s1 = length s2.
Proof.
rewrite !ka_of_string_Unit => /Unit_inj Heq.
by rewrite -!ka_of_string_msize (msize_proper Heq).
Qed.

(** A product x ⋅ y with msize x >= 1 cannot be
    ≡ to something of smaller msize *)

Lemma msize_mul_ge (x y : M) :
  msize (x ⋅ y) ≥ msize x.
Proof. rewrite msize_mul. lia. Qed.

Lemma unit_le_sum_terms_lt_k (A : fsa G T f) (σ : fsa_state A) k (m : M) :
  Unit m ⊑ sum_terms_lt_k_at σ k → msize m < k.
Proof.
move/l_alt => Hle.
rewrite /sum_terms_lt_k_at
  semi_lattice_morphism_join_list in Hle.
apply elem_of_lang_join_list in Hle.
destruct Hle as [s'' [Hs'' Hm]].
apply elem_of_list_filter in Hs''.
destruct Hs'' as [_ Hlen].
apply elem_of_enum_list_lt in Hlen.
have Hm' : Unit m ⊑ ka_of_string f s''
  by apply/l_alt.
have Hm'' :
  Unit m ⊑ Unit (∏ a ∈ s'', generator_interp a).
{ etransitivity; first exact: Hm'.
  rewrite sqsubseteq_iff ka_of_string_Unit
    semi_lattice_idemp //. }
move/l_alt: Hm'' => /= Heq.
by rewrite (msize_proper Heq) ka_of_string_msize.
Qed.

Lemma unit_le_sum_suffix_terms_k
    (A : fsa G T f)
    (σ : fsa_state A) k (m : M) :
  Unit m ⊑ sum_suffix_terms_k_at σ k →
  msize m ≥ k.
Proof.
move/l_alt => Hle.
rewrite /sum_suffix_terms_k_at
  /string_suffix_term_at
  semi_lattice_morphism_join_list in Hle.
apply elem_of_lang_join_list in Hle.
destruct Hle as [s'' [Hs'' Hm]].
apply elem_of_enum_list_eq in Hs''.
simpl in Hm.
destruct Hm as [m1 [m2 [Heq [Hm1 Hm2]]]].
have Hm1' : Unit m1 ⊑ ka_of_string f s''
  by apply/l_alt.
have Hm1'' :
  Unit m1 ⊑ Unit (∏ a ∈ s'', generator_interp a).
{ etransitivity; first exact: Hm1'.
  rewrite sqsubseteq_iff ka_of_string_Unit
    semi_lattice_idemp //. }
move/l_alt: Hm1'' => /= Heq1.
rewrite (msize_proper Heq) msize_mul
  (msize_proper Heq1) ka_of_string_msize Hs''.
lia.
Qed.

Lemma string_match_at_complete_sized
    (A : fsa G T f)
    (σ : fsa_state A) (s : list G) :
  ka_of_string f s ⊑ fsa_interp σ →
  ∃ s',
    (∏ a ∈ s', generator_interp a) ≡
    (∏ a ∈ s, generator_interp a) ∧
    string_match_at σ s' = true.
Proof.
move=> Hle.
set m := ∏ a ∈ s, generator_interp a.
have Hle' : Unit m ⊑ fsa_interp σ.
{ etransitivity; last exact: Hle.
  rewrite sqsubseteq_iff ka_of_string_Unit
    semi_lattice_idemp //. }
move/l_alt: Hle' => Hle'.
have Hdecomp :=
  fsa_elem_k_decomp_gen σ (S (length s)).
rewrite Hdecomp semi_lattice_morphism_join
  in Hle'.
case: Hle' => Hle'.
- rewrite /sum_terms_lt_k_at
    semi_lattice_morphism_join_list in Hle'.
  case/elem_of_lang_join_list: Hle' =>
    s' [] /elem_of_list_filter [σs' _].
  rewrite /= ka_of_string_Unit /= => s's.
  exists s'; split => //; exact/Is_true_true.
- exfalso.
  have Hge : msize m ≥ S (length s).
  { apply: unit_le_sum_suffix_terms_k.
    apply/l_alt. exact: Hle'. }
  have Hms : msize m = length s
    by exact: ka_of_string_msize.
  lia.
Qed.

Lemma string_match_complete_sized
    (A : fsa G T f) (s : list G) :
  ka_of_string f s ⊑ fsa_elem A →
  ∃ s',
    (∏ a ∈ s', generator_interp a) ≡
    (∏ a ∈ s, generator_interp a) ∧
    string_match A s' = true.
Proof.
rewrite -fsa_interp_initial; exact: string_match_at_complete_sized.
Qed.

End StringMatchComplete.

Section FSAKATerm.

Context `{!MonoidGen G T, !EqDecision G, !Finite G, !IsOne T}.

Fixpoint finite_state (e : ka_term T) : bool :=
  match e with
  | Unit _ => true
  | ka_term_join e1 e2 => finite_state e1 && finite_state e2
  | ka_term_bottom => true
  | ka_term_mul e1 e2 => finite_state e1 && finite_state e2
  | ka_term_star e => negb (has_one e) && finite_state e
  end.

Lemma finite_stateP e :
  finite_state e →
  {A : fsa G (ka_term T) (λ x, Unit (generator_interp x)) |
    e ≡ fsa_elem A}.
Proof.
elim: e => /=.
- move=> s _.
  exists (fsa_mul_list
    (map fsa_singleton (generate s))).
  rewrite fsa_elem_mul_list mul_list_map /=
    {1}(generateP s).
  by rewrite monoid_morphism_mul_list.
- move=> _. by exists (fsa_bottom _) => /=.
- move=> e1 IH1 e2 IH2 /andb_True [H1 H2].
  have [A1 E1] := IH1 H1.
  have [A2 E2] := IH2 H2.
  exists (fsa_join A1 A2). by rewrite /= -E1 -E2.
- move=> e1 IH1 e2 IH2 /andb_True [H1 H2].
  have [A1 E1] := IH1 H1.
  have [A2 E2] := IH2 H2.
  exists (fsa_mul A1 (fsa_to_nfa A2)).
  by rewrite /= -E1 -E2.
- move=> e1 IH1 /andb_True [/negb_True /Is_true_false H1 H2].
  have {IH1 H2} [A1 E1] := IH1 H2; exists (fsa_star' A1).
  rewrite fsa_elem_star' -?E1 //; case E: fsa_final => //.
  have ?: has_one e1 = true; last by congruence.
  apply/has_oneP; rewrite E1 -fsa_interp_initial.
  rewrite fsa_derivable E /=; exact: sqsubseteq_join_left.
Qed.

End FSAKATerm.
