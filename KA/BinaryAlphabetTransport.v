(* Encoding infrastructure for the binary-alphabet embedding used to
   close the source paper's Theorem 18/19 over its own canonical
   2-symbol alphabet: `finite_binary_encoding` shows a fixed-length
   injective encoding into `list bool` always exists for a finite
   alphabet `T`, and `Embed_word`/`Embed_pair` lift it to KA terms, with
   naturality lemmas `Embed_proj1_natural`/`Embed_proj2_natural`. Fully
   axiom-free and generic over an arbitrary finite alphabet, not
   specific to this project's own `mm_sym` alphabet.
   KA/BoundedOutputTransport.v uses this encoding directly to transport
   KA/bounded_output.v's representable-relation construction to the
   binary alphabet, which CKAUndec/BinaryAlphabet.v then applies to the
   MM2 encoding. *)

From Stdlib Require Import Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list finite.
From kacc Require Import KA.utils KA.algebra KA.pre_ka.

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

End Embedding.
