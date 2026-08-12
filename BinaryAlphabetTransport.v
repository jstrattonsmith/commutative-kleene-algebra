(* Route 2 for closing Arthur's comment 2 (see project memory /
   binary_alphabet_sketch.md scratch note): rather than reprove the
   ~800-line bounded_output.v finite-state/bounded-output argument a
   second time at the binary-alphabet level, this file develops a
   GENERIC transport theorem -- repr_rel (Definition 20/repr_rel.v)
   transports along a fixed-length injective symbol encoding -- so that
   ANY existing repr_rel instance (in particular repr_rel_mm2_R, Encoding.v)
   can be pushed forward to the canonical Sigma={0,1} carrier the
   source paper's own Theorem 18/19 use, without redoing the underlying
   finite-state/bounded-output work.

   GENERIC / reusable throughout: everything in this file is stated for
   an arbitrary finite alphabet T, not specific to mm_sym or this
   project's own encoding. CKA-specific instantiation (applying this to
   Encoding.v's repr_rel_mm2_R and composing with Theorem19_Full.v's
   KA_ineq_m_complete) is deliberately NOT in this file -- that belongs
   in a follow-up file once this transport theorem itself is fully
   discharged.

   STATUS: repr_rel_transport is fully assembled and everything is
   proven EXCEPT ONE genuine open gap, dpseudo_top_mismatch_transport,
   confirmed isolated via `Print Assumptions repr_rel_transport` (no
   stray axioms). next_spec' (the language-level pushforward argument,
   via l_alt/l_natural + decode's two-sidedness on enc_word's image)
   and repr_rel_dom'/repr_rel_cod' (free from naturality +
   monotonicity) are fully proven, axiom-free.

   The one remaining gap is NOT mechanical: it needs
   Proper((⊑)==>(⊑)) star (star-monotonicity), which this pre-KA
   deliberately does not axiomatize (PreKAMixin has only the unfold
   equation + Properness w.r.t. ≡, no induction/least-fixpoint axiom --
   see CLAUDE.md). See dpseudo_top_mismatch_transport's own comment for
   the full argument for why this can't be sidestepped by decomposing
   differently. This is a real mathematical question to raise with
   Jeremy/Arthur, not a proof-engineering task. *)

From Stdlib Require Import Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list finite.
From kacc Require Import utils algebra pre_ka lang repr_rel.

Section BinaryEncoding.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

(* --- 1. A fixed-length injective encoding always exists, via a
   one-hot vector over T's own (finite, NoDup) enumeration. Simpler to
   formalize than a tight binary/log2 encoding, and the encoding length
   is irrelevant to everything downstream -- only fixed-length +
   injective matter. *)

Definition enc_onehot (x : T) : list bool :=
  (λ y, bool_decide (y = x)) <$> enum T.

Lemma enc_onehot_length x : length (enc_onehot x) = length (enum T).
Proof. by rewrite /enc_onehot length_fmap. Qed.

(* Two positions in a NoDup list agree on "is this position x" for
   every position iff they hold the same element, since a NoDup list's
   own membership test is a genuine characteristic function of
   position. *)

Lemma enc_onehot_inj' x y : enc_onehot x = enc_onehot y -> x = y.
Proof.
rewrite /enc_onehot => Heq.
have Hx := @elem_of_enum T EqDecision0 Finite0 x.
have Hxx : bool_decide (x = x) = true by apply/bool_decide_eq_true.
have Hstep : (λ z, bool_decide (z = x)) x = (λ z, bool_decide (z = y)) x.
{ have [i Hi] := elem_of_list_lookup_1 (enum T) x Hx.
  have Hlx : ((λ z, bool_decide (z = x)) <$> enum T) !! i
             = Some ((λ z, bool_decide (z = x)) x).
  { by rewrite list_lookup_fmap Hi. }
  have Hly : ((λ z, bool_decide (z = y)) <$> enum T) !! i
             = Some ((λ z, bool_decide (z = y)) x).
  { by rewrite list_lookup_fmap Hi. }
  rewrite Heq in Hlx.
  rewrite Hly in Hlx.
  by injection Hlx. }
move: Hstep. rewrite /= Hxx => Heq2.
symmetry in Heq2.
by move: Heq2 => /bool_decide_eq_true.
Qed.

Lemma finite_binary_encoding :
  ∃ (k : nat) (enc : T → list bool),
    (∀ x y, enc x = enc y → x = y) ∧
    (∀ x, length (enc x) = k).
Proof.
exists (length (enum T)), enc_onehot.
split; [exact: enc_onehot_inj' | exact: enc_onehot_length].
Qed.

End BinaryEncoding.

(* --- 2. mul_list is a MonoidMorphism for an ARBITRARY f into a monoid,
   not just f = id (algebra.v's mul_list_monoid_morphism is only stated
   for id). The natural generalization -- needs f Proper, since
   MonoidMorphism's own first field is Properness and there is no way
   around that hypothesis (flagged by the critique pass on the earlier
   sketch as a real, if minor, correction). *)

Section MulListMorphism.

Context {A : setoid} {S : monoid} (f : A → S) `{!Proper ((≡) ==> (≡)) f}.

Global Instance mul_list_monoid_morphism_gen : MonoidMorphism (mul_list f).
Proof.
have Hpt : ∀ xs, mul_list f xs = mul_list id (f <$> xs).
{ move=> xs. by rewrite (mul_list_map id f xs). }
split.
- move=> xs ys /list_equiv_Forall2.
  elim=> [//| x y xs' ys' Hxy' Hrest IH /=].
  by rewrite IH Hxy'.
- by rewrite Hpt.
- move=> xs ys.
  rewrite !Hpt fmap_app.
  exact: (monoid_morphism_mul (f := mul_list id)).
Qed.

End MulListMorphism.

(* --- 3. The induced word- and pair-level embeddings, and their basic
   naturality properties. Fully generic over the alphabet T and the
   target alphabet S (S := bool for our eventual use, but nothing here
   is specific to bool). *)

Section Embedding.

Context {T : setoid} `{!LeibnizEquiv T, !EqDecision T, !Finite T}.
Context {S : setoid} (enc : T → list S) `{!Inj (=) (=) enc}
  (k : nat) (enc_len : ∀ x, length (enc x) = k).

Definition enc_word : list T → list S := mul_list enc.

Instance enc_proper : Proper ((≡) ==> (≡)) enc.
Proof. by move=> x y /leibniz_equiv_iff ->. Qed.

Global Instance enc_word_monoid_morphism : MonoidMorphism enc_word :=
  mul_list_monoid_morphism_gen enc.

Definition Embed_pair_fn : list T * list T → list S * list S :=
  pair_mor (enc_word ∘ fst) (enc_word ∘ snd).

Global Instance Embed_pair_fn_morphism : MonoidMorphism Embed_pair_fn.
Proof.
apply: pair_mor_morphism; apply: compose_monoid_morphism; apply: _.
Qed.

Definition Embed_word : ka_term (list T) → ka_term (list S) :=
  ka_term_map enc_word.

Definition Embed_pair : ka_term (list T * list T) → ka_term (list S * list S) :=
  ka_term_map Embed_pair_fn.

(* proj1/proj2 naturality: confirmed by hand in the scratch sketch via
   ka_term_map_comp twice plus a definitional computation of
   fst ∘ Embed_pair_fn; spelled out here. *)

Lemma Embed_pair_fn_fst x : fst (Embed_pair_fn x) = enc_word (fst x).
Proof. by case: x. Qed.

Lemma Embed_pair_fn_snd x : snd (Embed_pair_fn x) = enc_word (snd x).
Proof. by case: x. Qed.

(* ka_term_map is a bare Coq function of its function-argument -- there
   is no ka_term_map-is-Proper-in-that-argument lemma to rewrite with
   directly, so a pointwise-≡ of two functions doesn't turn into a ≡ of
   the two ka_term_maps by `rewrite` alone. Route through ka_term_ext
   (the eliminator's uniqueness half, pre_ka.v line 611) instead: both
   sides are PreKAMorphisms (ka_term_map of a MonoidMorphism, via
   ka_term_map_morphism), so it suffices to check they agree on Unit. *)

Lemma Embed_proj1_natural e :
  ka_term_proj1 (Embed_pair e) ≡ Embed_word (ka_term_proj1 e).
Proof.
rewrite /ka_term_proj1 /Embed_pair /Embed_word.
rewrite (ka_term_map_comp e Embed_pair_fn_morphism (fst_monoid_morphism (list S) (list S)))
        (ka_term_map_comp e (fst_monoid_morphism (list T) (list T)) enc_word_monoid_morphism).
apply ka_term_ext; [ exact: ka_term_map_morphism | exact: ka_term_map_morphism | ].
move=>?. rewrite /ka_term_map //=.
Qed.

Lemma Embed_proj2_natural e :
  ka_term_proj2 (Embed_pair e) ≡ Embed_word (ka_term_proj2 e).
Proof.
rewrite /ka_term_proj2 /Embed_pair /Embed_word.
rewrite (ka_term_map_comp e
           Embed_pair_fn_morphism (snd_monoid_morphism (list S) (list S))).
rewrite (ka_term_map_comp e
           (snd_monoid_morphism (list T) (list T)) enc_word_monoid_morphism).
apply ka_term_ext; [ exact: ka_term_map_morphism | exact: ka_term_map_morphism |].
move=> ?. rewrite /ka_term_map //=.
Qed.

(* --- 4. The repr_rel transport theorem itself (route 2's core
   deliverable). Needs the target alphabet S to carry the same
   LeibnizEquiv/EqDecision/Finite structure as T -- exactly what
   repr_rel.v's own section requires, so every repr_rel-level notion
   (dpseudo_top, mismatch, pseudo_top, strings_r, list_diverge,
   repr_rel itself) is already available at S once these hold; in the
   eventual CKA instantiation S := bool, which trivially satisfies all
   three. *)

Context `{!LeibnizEquiv S, !EqDecision S, !Finite S}.

Section Transport.

Context (e : ka_term (list T * list T)) (L : ka_term (list T)).
Context (R : repr_rel e L).

(* A concrete (if naive) decoder: chunk an S-word into fixed-length
   blocks, then look each block up against T's own finite enumeration
   via enc's injectivity. Total on the whole of `list S`; only ever
   used, per next_spec' below, on words that actually arise as
   `enc_word xs` for some `xs`, where it is a genuine two-sided
   inverse. Fuelled by the input's own length so it terminates
   regardless of k (in particular even if k = 0, though that case
   cannot arise once T has more than one element, as enc's injectivity
   then forces k > 0). *)

(* NB: matches on l FIRST, then fuel -- this makes `chunk_fuel _ []`
   reduce to `[]` by cbn/simpl regardless of fuel's shape, avoiding any
   dependence on how a simultaneous "match fuel, l with" would actually
   get compiled. Also pattern-matches fuel's successor via the
   qualified Datatypes.S, not the bare constructor name, since S is
   this section's own target-alphabet variable, shadowing it. *)
Fixpoint chunk_fuel (fuel : nat) (l : list S) : list (list S) :=
  match l with
  | [] => []
  | _ =>
    match fuel with
    | 0 => []
    | Datatypes.S fuel' => take k l :: chunk_fuel fuel' (drop k l)
    end
  end.

Definition chunk (l : list S) : list (list S) := chunk_fuel (length l) l.

Definition decode1 (block : list S) : option T :=
  List.find (λ x, bool_decide (enc x = block)) (enum T).

Fixpoint decode_blocks (blocks : list (list S)) : option (list T) :=
  match blocks with
  | [] => Some []
  | b :: bs =>
    match decode1 b, decode_blocks bs with
    | Some x, Some xs => Some (x :: xs)
    | _, _ => None
    end
  end.

Definition decode (sl : list S) : option (list T) := decode_blocks (chunk sl).

Definition next' (sl : list S) : list (list S) :=
  match decode sl with
  | Some xs => enc_word <$> next R xs
  | None => []
  end.

Context (k_pos : 0 < k).

(* concat-recovery: unconditional in k, needs only enough fuel. *)
Lemma chunk_fuel_concat fuel l :
  length l ≤ fuel → concat (chunk_fuel fuel l) = l.
Proof.
elim: fuel l => [| fuel' IH] l Hfuel.
- have -> : l = [] by destruct l; [done | simpl in Hfuel; lia].
  done.
- destruct l as [|x l']; first done.
  rewrite /=.
  have Hle : length (drop k (x :: l')) ≤ fuel'.
  { rewrite length_drop /=. simpl in Hfuel. lia. }
  by rewrite (IH _ Hle) take_drop.
Qed.

Lemma chunk_concat l : concat (chunk l) = l.
Proof. exact: chunk_fuel_concat (length l) l (le_n _). Qed.

(* block-alignment: given a properly length-k-blocked prefix, chunking
   peels off exactly that block. *)
Lemma chunk_fuel_app fuel' b l :
  length b = k → chunk_fuel (Datatypes.S fuel') (b ++ l) = b :: chunk_fuel fuel' l.
Proof.
move=> Hlen.
destruct b as [|b0 bs]; first (simpl in Hlen; lia).
rewrite /=.
rewrite (take_app_length' (b0 :: bs) l k (eq_sym Hlen)).
rewrite (drop_app_length' (b0 :: bs) l k (eq_sym Hlen)).
done.
Qed.

Lemma chunk_fuel_enc_word fuel xs :
  length xs ≤ fuel → chunk_fuel fuel (enc_word xs) = enc <$> xs.
Proof.
elim: xs fuel => [| x xs' IH] fuel Hfuel.
- have -> : enc_word ([] : list T) = [] by [].
  by destruct fuel.
- have -> : enc_word (x :: xs') = enc x ++ enc_word xs' by [].
  destruct fuel as [|fuel']; first (simpl in Hfuel; lia).
  rewrite (chunk_fuel_app fuel' (enc x) (enc_word xs') (enc_len x)).
  rewrite IH //.
  simpl in Hfuel. lia.
Qed.

Lemma chunk_enc_word xs : chunk (enc_word xs) = enc <$> xs.
Proof.
apply: chunk_fuel_enc_word.
rewrite /enc_word /mul_list.
elim: xs => [| x xs' IH] //=.
rewrite length_app enc_len. lia.
Qed.

Lemma enc_word_concat_map xs : enc_word xs = concat (enc <$> xs).
Proof. elim: xs => [| x xs' IH] //=; by rewrite IH. Qed.

Lemma decode1_sound b x : decode1 b = Some x → enc x = b.
Proof.
rewrite /decode1 => Hfind.
have [_ Hpx] := List.find_some _ _ Hfind.
by move: Hpx => /bool_decide_eq_true.
Qed.

Lemma decode1_correct x : decode1 (enc x) = Some x.
Proof.
rewrite /decode1.
destruct (List.find (λ y, bool_decide (enc y = enc x)) (enum T))
  as [y|] eqn:Hfind.
- have Exy : enc y = enc x.
  { have [_ Hpy] := List.find_some _ _ Hfind.
    by move: Hpy => /bool_decide_eq_true. }
  by have -> : y = x by exact: (Inj0 y x Exy).
- exfalso.
  have Hin : List.In x (enum T).
  { apply/elem_of_list_In. exact: elem_of_enum. }
  have Hfalse := List.find_none _ _ Hfind x Hin.
  move: Hfalse => /bool_decide_eq_false. exact.
Qed.

Lemma decode_blocks_sound bs xs :
  decode_blocks bs = Some xs → enc <$> xs = bs.
Proof.
elim: bs xs => [| b bs' IH] xs /=.
- by move=> [<-].
- destruct (decode1 b) as [x|] eqn:Hb; last done.
  destruct (decode_blocks bs') as [xs0|] eqn:Hbs'; last done.
  move=> [<-].
  simpl.
  f_equal.
  + exact: decode1_sound b x Hb.
  + exact: IH xs0 eq_refl.
Qed.

Lemma decode_blocks_complete xs :
  decode_blocks (enc <$> xs) = Some xs.
Proof.
by elim: xs => [| x xs' IH] //=; rewrite decode1_correct IH.
Qed.

Lemma decode_sound sl xs : decode sl = Some xs → sl = enc_word xs.
Proof.
rewrite /decode => Hdec.
rewrite enc_word_concat_map (decode_blocks_sound (chunk sl) xs Hdec).
exact: (eq_sym (chunk_concat sl)).
Qed.

Lemma decode_enc_word xs : decode (enc_word xs) = Some xs.
Proof. by rewrite /decode chunk_enc_word decode_blocks_complete. Qed.

(* THE two hard obligations, per the scratch sketch's route-2 writeup
   (binary_alphabet_sketch.md, section 6): next_spec' needs the
   language-level pushforward argument (l_alt + l_natural + decode's
   two-sidedness on enc_word's image); expand_rel' needs the
   list_diverge-based mismatch-transport argument
   (Embed_pair(mismatch) ⊑ dpseudo_top' ⋅ mismatch' ⋅ pseudo_top',
   which is exactly why residue' below carries an extra pseudo_top
   factor that residue R alone does not need). Left admitted per
   strategy-bottom-up-admit: the skeleton's SHAPE (this section
   compiling end to end) is the thing being validated first. *)

Lemma next_spec' sl sr : sr ∈ next' sl ↔ Unit (sl, sr) ⊑ Embed_pair e.
Proof.
rewrite -(l_alt (Embed_pair e) (sl, sr)) /Embed_pair
  (l_natural (f := Embed_pair_fn) e) /=.
split.
- rewrite /next'.
  destruct (decode sl) as [xs|] eqn:Hdec; last by move=> /elem_of_nil.
  move=> /elem_of_list_fmap [b [Hsr_eq Hb_in]].
  exists (xs, b); split.
  + by rewrite Hsr_eq (decode_sound sl xs Hdec).
  + apply/l_alt. exact: (proj1 (next_spec R xs b) Hb_in).
- move=> [[a b] [Heq Hl]].
  move: Heq => /leibniz_equiv_iff Heq.
  injection Heq as Hsl Hsr; subst sl sr.
  rewrite /next' (decode_enc_word a).
  apply/elem_of_list_fmap.
  exists b; split; first done.
  apply: (proj2 (next_spec R a b)).
  apply/l_alt. exact: Hl.
Qed.

Definition residue' : ka_term (list S * list S) :=
  pseudo_top ⋅ Embed_pair (residue R).

Lemma Embed_word_L_inv xs :
  Unit xs ⊑ Embed_word L → ∃ ys, xs = enc_word ys ∧ Unit ys ⊑ L.
Proof.
rewrite -(l_alt (Embed_word L) xs) /Embed_word (l_natural (f := enc_word) L) /=.
move=> [ys [Heq Hys]].
move: Heq => /leibniz_equiv_iff ->.
exists ys; split; first done.
apply/l_alt. exact: Hys.
Qed.

Lemma enc_word_single x : enc_word [x] = enc x.
Proof.
rewrite /enc_word /mul_list /=.
change (enc x ++ [] = enc x).
by rewrite app_nil_r.
Qed.

Lemma strings_r_natural σ : Embed_pair (strings_r σ) ≡ strings_r (enc_word <$> σ).
Proof.
rewrite /strings_r /Embed_pair.
elim: σ => [| xs σ' IH].
- by rewrite /= pre_ka_morphism_bottom.
- rewrite /= pre_ka_morphism_join IH.
  by f_equiv.
Qed.

Lemma mismatch_transport : Embed_pair mismatch ⊑ dpseudo_top ⋅ mismatch ⋅ pseudo_top.
Proof.
rewrite /mismatch /Embed_pair.
rewrite (semi_lattice_morphism_join_list (f := ka_term_map Embed_pair_fn)).
apply/join_list_sqsubseteq => -[x y] Hxy.
have Hne : x ≠ y.
{ move: Hxy => /elem_of_list_filter [Hb _].
  by move: Hb => /Is_true_true /bool_decide_eq_true. }
rewrite /= /ka_term_map /=.
have -> : Embed_pair_fn ([x], [y]) = (enc x, enc y).
{ rewrite /Embed_pair_fn /pair_mor /=.
  change ((enc x ++ [], enc y ++ []) = (enc x, enc y)).
  by rewrite !app_nil_r. }
apply: list_diverge.
- move=> [t Ht].
  have Hlen : length (enc y) = length (enc x) + length t
    by rewrite Ht length_app.
  rewrite !enc_len in Hlen.
  have Ht0 : t = [] by destruct t; [done | simpl in Hlen; lia].
  subst t.
  rewrite app_nil_r in Ht.
  exact: Hne (eq_sym (Inj0 y x Ht)).
- move=> [t Ht].
  have Hlen : length (enc x) = length (enc y) + length t
    by rewrite Ht length_app.
  rewrite !enc_len in Hlen.
  have Ht0 : t = [] by destruct t; [done | simpl in Hlen; lia].
  subst t.
  rewrite app_nil_r in Ht.
  exact: Hne (Inj0 x y Ht).
Qed.

(* GENUINE OPEN GAP, not a Coq-mechanics issue. Stated as ONE combined
   fact (rather than separately bounding Embed_pair dpseudo_top and
   relying on mismatch_transport) specifically to avoid a redundant
   double dpseudo_top factor in the final assembly below -- splitting
   this into "Embed_pair dpseudo_top ⊑ dpseudo_top" (proved separately)
   composed with mismatch_transport would need
   "dpseudo_top ⋅ dpseudo_top ⊑ dpseudo_top" downstream, which is
   EXACTLY as hard (same missing induction step, see below) -- so
   nothing is gained by decomposing, and the combined form is honest
   about being one single gap, not two.

   The actual missing ingredient: "the star of a sub-generator-set is
   <= the star of the full generator set", i.e.
   Proper ((⊑) ==> (⊑)) star (star-monotonicity). This pre-KA
   framework deliberately does NOT axiomatize this: PreKAMixin only
   provides the single unfold equation (star x ≡ 1 ⊔ x⋅star x) plus
   Properness w.r.t. ≡, with no induction/least-fixpoint axiom (see
   CLAUDE.md: "pre-KA exists precisely because induction is missing").
   Confirmed: no Proper((⊑)==>(⊑)) star instance exists anywhere in
   pre_ka.v/algebra.v/repr_rel.v. pseudo_top_absorb's own technique
   (finite decomposition via generate + repeated pre_ka_mul_star) shows
   EACH generator of Embed_pair(dpseudo_top)'s image absorbs into
   dpseudo_top (via dpseudo_top_absorb, already proven), but lifting
   "each generator absorbs" to "the whole star is dominated" is
   exactly the missing induction step (equivalently: this would need
   "H ⋅ X ⊑ X -> star H ⋅ X ⊑ X" for H := the finite generator join,
   X := dpseudo_top⋅mismatch⋅pseudo_top -- the star-induction rule,
   confirmed absent). Left admitted; this is the one real open item to
   raise with Jeremy, not a mechanical gap. *)
Lemma dpseudo_top_mismatch_transport :
  Embed_pair dpseudo_top ⋅ Embed_pair mismatch ⊑ dpseudo_top ⋅ mismatch ⋅ pseudo_top.
Admitted.

Lemma expand_rel' (xs : list S) :
  Unit xs ⊑ Embed_word L →
  Unit (1, xs) ⋅ Embed_pair e ⊑
    Unit (xs, xs) ⋅ strings_r (next' xs)
    ⊔ dpseudo_top ⋅ mismatch ⋅ residue'.
Proof.
move=> Hxs.
have [ys [Hys_eq Hys]] := Embed_word_L_inv xs Hxs.
subst xs.
have Hexp := expand_rel R Hys.
have Hemb : Embed_pair (Unit (1, ys) ⋅ e) ⊑
    Embed_pair (Unit (ys, ys) ⋅ strings_r (next R ys)
                  ⊔ dpseudo_top ⋅ mismatch ⋅ residue R).
{ apply: semi_lattice_morphism_sqsubseteq_proper. exact: Hexp. }
move: Hemb.
rewrite !pre_ka_morphism_mul !pre_ka_morphism_join !pre_ka_morphism_mul.
have -> : Embed_pair (Unit (1, ys)) = Unit (1, enc_word ys) by [].
have -> : Embed_pair (Unit (ys, ys)) = Unit (enc_word ys, enc_word ys) by [].
rewrite (strings_r_natural (next R ys)).
rewrite /next' (decode_enc_word ys).
move=> H.
have H2 :
  Unit (enc_word ys, enc_word ys) ⋅ strings_r (enc_word <$> next R ys)
    ⊔ Embed_pair dpseudo_top ⋅ Embed_pair mismatch ⋅ Embed_pair (residue R)
  ⊑ Unit (enc_word ys, enc_word ys) ⋅ strings_r (enc_word <$> next R ys)
    ⊔ dpseudo_top ⋅ mismatch ⋅ residue'.
{ apply: join_mono; first reflexivity.
  rewrite /residue' assoc.
  apply: pre_ka_mul_mono; last reflexivity.
  exact: dpseudo_top_mismatch_transport. }
exact: (transitivity H H2).
Qed.

Lemma repr_rel_dom' : ka_term_proj1 (Embed_pair e) ⊑ Embed_word L.
Proof.
rewrite Embed_proj1_natural.
apply: semi_lattice_morphism_sqsubseteq_proper.
exact: repr_rel_dom R.
Qed.

Lemma repr_rel_cod' : ka_term_proj2 (Embed_pair e) ⊑ Embed_word L.
Proof.
rewrite Embed_proj2_natural.
apply: semi_lattice_morphism_sqsubseteq_proper.
exact: repr_rel_cod R.
Qed.

Definition repr_rel_transport : repr_rel (Embed_pair e) (Embed_word L) := {|
  repr_rel_dom := repr_rel_dom';
  repr_rel_cod := repr_rel_cod';
  next := next';
  next_spec := next_spec';
  residue := residue';
  expand_rel := expand_rel';
|}.

End Transport.

End Embedding.
