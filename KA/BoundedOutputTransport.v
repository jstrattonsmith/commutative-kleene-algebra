(* Route 1 for closing the canonical-alphabet requirement (binary-alphabet
   embedding), picked back up after route 2 (BinaryAlphabetTransport.v, committed
   c25780b) hit a genuine gap needing star-monotonicity, which this
   project's pre-KA does not axiomatize.

   Route 1 does NOT reprove bounded_output.v: that file's Lemma 34
   (bounded_output_repr_rel) is already generic over an arbitrary
   finite alphabet T, and its own star case avoids algebraic star
   reasoning entirely by working through actual strings (via l_alt),
   which is exactly why route 1 sidesteps route 2's wall. So this file
   applies bounded_output_repr_rel DIRECTLY to (Embed_pair e,
   Embed_word L) -- reusing BinaryAlphabetTransport.v's Embed_pair/
   Embed_word -- by proving that its four hypotheses transport under
   the embedding:

     finite_stateb e = true  -- DONE, finite_state_transport (revised
                                 hypothesis, see its own comment: an
                                 explicit automaton-refinement
                                 construction turned out unnecessary)
     bounded_output e        -- DONE, bounded_output_transport
     proj1/proj2 e ⊑ L        -- DONE, free from Embed_proj{1,2}_natural
     prefix_free L            -- DONE, prefix_free_transport

   STATUS: repr_rel_via_bounded_output is fully proven, axiom-free --
   `Print Assumptions` confirms no admits anywhere in this file. The
   hypothesis is finite_stateb e = true rather than the fully abstract
   finite_state e (a purely syntactic, decidable check on e's own
   constructor shape, from automata.v) -- strictly stronger, but
   exactly what Encoding.v's own construction of its transition term
   provides at the leaf level (Encoding.v:1319-1320, via
   finite_state_join_list + finite_stateP per instruction), so this
   loses no real generality for the actual application. *)

From Stdlib Require Import Unicode.Utf8.
Require Import ssreflect.
From stdpp Require Import base list finite.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.automata
  KA.repr_rel KA.bounded_output.
From kacc Require Import KA.BinaryAlphabetTransport.

Section BoundedOutputTransport.

Context (T : setoid) `{!LeibnizEquiv T, !EqDecision T, !Finite T}.
Context (S : setoid) `{!LeibnizEquiv S, !EqDecision S, !Finite S}.
Context (enc : T → list S) `{!Inj (=) (=) enc}
  (k : nat) (enc_len : ∀ x, length (enc x) = k) (k_pos : 0 < k).

(* --- Reusable pushforward-extraction lemmas. Same l_alt/l_natural
   recipe already used (twice) in BinaryAlphabetTransport.v, rederived
   here rather than imported since there they live inside a section
   parametrized by a fixed (e, L, R) that these don't actually depend
   on. *)

Lemma Embed_word_inv (L : ka_term (list T)) xs' :
  Unit xs' ⊑ Embed_word enc L → ∃ xs, xs' = enc_word enc xs ∧ Unit xs ⊑ L.
Proof.
rewrite -(l_alt (Embed_word enc L) xs') /Embed_word
  (l_natural (f := enc_word enc) L) /=.
move=> [xs [Heq Hxs]].
move: Heq => /leibniz_equiv_iff ->.
exists xs; split; first done.
apply/l_alt. exact: Hxs.
Qed.

Lemma Embed_pair_inv (e : ka_term (list T * list T)) sl' sr' :
  Unit (sl', sr') ⊑ Embed_pair enc e →
  ∃ sl sr, sl' = enc_word enc sl ∧ sr' = enc_word enc sr ∧ Unit (sl, sr) ⊑ e.
Proof.
rewrite -(l_alt (Embed_pair enc e) (sl', sr')) /Embed_pair
  (l_natural (f := Embed_pair_fn enc) e) /=.
move=> [[sl sr] [Heq Hin]].
move: Heq => /leibniz_equiv_iff Heq.
injection Heq as Hsl Hsr; subst sl' sr'.
exists sl, sr; split; first done; split; first done.
apply/l_alt. exact: Hin.
Qed.

Lemma enc_word_length xs : length (enc_word enc xs) = k * length xs.
Proof.
elim: xs => [| x xs IH] //=.
change (length (enc x ++ enc_word enc xs) = k * Datatypes.S (length xs)).
by rewrite length_app enc_len IH; lia.
Qed.

Lemma enc_word_app xs ys :
  enc_word enc (xs ++ ys) = enc_word enc xs ++ enc_word enc ys.
Proof.
elim: xs ys => [| x xs IH] ys //=.
change (enc x ++ enc_word enc (xs ++ ys) = (enc x ++ enc_word enc xs) ++ enc_word enc ys).
by rewrite IH app_assoc.
Qed.

(* enc_word is injective: a fixed-length-block decoder in disguise,
   but derived here via plain list induction + app_inj_1 rather than
   an actual decode function (unlike BinaryAlphabetTransport.v's
   next'/decode, nothing downstream needs enc_word's inverse to be
   COMPUTABLE, only that it exists as a bare implication). *)
Lemma enc_word_inj xs1 xs2 : enc_word enc xs1 = enc_word enc xs2 → xs1 = xs2.
Proof.
elim: xs1 xs2 => [| x1 xs1' IH] [| x2 xs2'] Heq //=.
- exfalso.
  have := enc_word_length (x2 :: xs2').
  rewrite -Heq /=. lia.
- exfalso.
  have := enc_word_length (x1 :: xs1').
  rewrite Heq /=. lia.
- move: Heq.
  change (enc x1 ++ enc_word enc xs1' = enc x2 ++ enc_word enc xs2' → x1 :: xs1' = x2 :: xs2').
  move=> Heq.
  have Hlen12 : length (enc x1) = length (enc x2) by rewrite !enc_len.
  have [Ex Ee] := app_inj_1 (enc x1) (enc x2) (enc_word enc xs1') (enc_word enc xs2')
    Hlen12 Heq.
  have -> : x1 = x2 by exact: (Inj0 x1 x2 Ex).
  by rewrite (IH xs2' Ee).
Qed.

(* --- Piece 1: bounded_output is preserved (arithmetic only, no star
   reasoning). *)

Lemma bounded_output_with_transport k0 (e : ka_term (list T * list T)) :
  bounded_output_with k0 e →
  bounded_output_with (k * k0) (Embed_pair enc e).
Proof.
move=> Hbo sl' sr' Hle.
have [sl [sr [-> [-> Hin]]]] := Embed_pair_inv e sl' sr' Hle.
have Hb := Hbo sl sr Hin.
rewrite !enc_word_length.
nia.
Qed.

Lemma bounded_output_transport (e : ka_term (list T * list T)) :
  bounded_output e → bounded_output (Embed_pair enc e).
Proof.
move=> [k0 Hk0]. exists (k * k0). exact: bounded_output_with_transport.
Qed.

(* --- Piece 2: prefix_free is preserved, via enc_word's own
   concatenativity (a monoid morphism) plus left-cancellation of app --
   no decoder needed. *)

Lemma prefix_free_transport (L : ka_term (list T)) :
  prefix_free L → prefix_free (Embed_word enc L).
Proof.
move=> Hpf s1' s2' H1' H2' [t Ht].
have [ys1 [Heq1 Hys1]] := Embed_word_inv L s1' H1'.
have [ys2 [Heq2 Hys2]] := Embed_word_inv L s2' H2'.
subst s1' s2'.
have Hlen_le : length ys1 ≤ length ys2.
{ have Hl := f_equal (@length S) Heq2.
  rewrite length_app !enc_word_length in Hl. nia. }
have Hsplit : enc_word enc (take (length ys1) ys2)
                ++ enc_word enc (drop (length ys1) ys2)
            = enc_word enc ys1 ++ t.
{ by rewrite -enc_word_app take_drop -Heq2. }
have Hlen_eq :
  length (enc_word enc (take (length ys1) ys2)) = length (enc_word enc ys1).
{ rewrite !enc_word_length length_take. nia. }
have [Ea _] := app_inj_1 _ _ _ _ Hlen_eq Hsplit.
have Htake : take (length ys1) ys2 = ys1 := enc_word_inj _ _ Ea.
have Hpfx : ys1 = ys2.
{ apply: (Hpf _ _ Hys1 Hys2).
  exists (drop (length ys1) ys2).
  by rewrite -{1}Htake take_drop. }
by rewrite Heq2 Hpfx.
Qed.

(* --- Piece 3, REVISED: the originally-planned automaton-refinement
   construction (state space fsa_state A * bit-position tracker) turns
   out to be unnecessary. automata.v provides finite_stateb -- a
   purely SYNTACTIC, decidable check on a ka_term's own constructor
   shape (Unit/join/mul/star/bottom) -- plus finite_stateP :
   finite_stateb e = true -> finite_state e (automata.v:1032-1060).
   Encoding.v's own construction of its transition term goes through EXACTLY
   this route (finite_state_join_list + finite_stateP per instruction,
   Encoding.v:1319-1320), not an ad-hoc automaton -- so proving finite_stateb
   is preserved under Embed_pair is both sufficient for the actual use
   case AND much simpler than automaton refinement: ka_term_map (what
   Embed_pair is) preserves every constructor DEFINITIONALLY
   (pre_ka.v:569-576's ka_term_elim is a direct Fixpoint on the term's
   shape), so finite_stateb's own structural recursion proceeds in
   lockstep on e and Embed_pair e; the only place they could actually
   differ is has_one at a star node, which transports via
   Embed_pair_inv (has_one e = true <-> 1 ⊑ e <-> 1 ⊑ Embed_pair e,
   using that Embed_pair_fn maps 1 to 1 and reflects it, since
   enc_word's fixed block length forces the T-level witness back to
   [],[] whenever the S-level pair is 1,1). *)

Lemma one_le_transport (e : ka_term (list T * list T)) :
  (1 : ka_term (list T * list T)) ⊑ e
  ↔ (1 : ka_term (list S * list S)) ⊑ Embed_pair enc e.
Proof.
change (Unit (([] : list T), ([] : list T)) ⊑ e
        ↔ Unit (([] : list S), ([] : list S)) ⊑ Embed_pair enc e).
split.
- move=> H.
  have -> : Unit (([] : list S), ([] : list S)) = Embed_pair enc (Unit ([], [])) by [].
  apply: semi_lattice_morphism_sqsubseteq_proper. exact: H.
- move=> H.
  have [a [b [Ha [Hb Hab]]]] := Embed_pair_inv e [] [] H.
  have Ea : a = [].
  { have Hlen : length (enc_word enc a) = 0 by rewrite -Ha.
    rewrite enc_word_length in Hlen.
    destruct a; [done | simpl in Hlen; nia]. }
  have Eb : b = [].
  { have Hlen : length (enc_word enc b) = 0 by rewrite -Hb.
    rewrite enc_word_length in Hlen.
    destruct b; [done | simpl in Hlen; nia]. }
  by subst a b.
Qed.

Lemma has_one_transport (e : ka_term (list T * list T)) :
  has_one e = has_one (Embed_pair enc e).
Proof.
apply: eq_true_iff_eq.
split.
- move=> H.
  apply: (proj2 (has_oneP (Embed_pair enc e))).
  apply/one_le_transport.
  exact: (proj1 (has_oneP e) H).
- move=> H.
  apply: (proj2 (has_oneP e)).
  apply/one_le_transport.
  exact: (proj1 (has_oneP (Embed_pair enc e)) H).
Qed.

Lemma finite_stateb_transport (e : ka_term (list T * list T)) :
  finite_stateb e = finite_stateb (Embed_pair enc e).
Proof.
elim: e => //=.
- move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
- move=> e1 IH1 e2 IH2. by rewrite IH1 IH2.
- move=> e1 IH1. by rewrite IH1 (has_one_transport e1).
Qed.

Lemma finite_state_transport (e : ka_term (list T * list T)) :
  finite_stateb e = true →
  finite_state (S + S) (Unit ∘ generator_interp) (Embed_pair enc e).
Proof.
move=> Hb. apply: finite_stateP.
- done.
- rewrite -finite_stateb_transport. apply/Is_true_true. exact: Hb.
Qed.

(* --- Final assembly: given the source hypotheses at the T level,
   get a genuine repr_rel at the S level, via bounded_output.v's own
   Lemma 34 -- no algebraic transport of an EXISTING repr_rel, a fresh
   one built directly for the embedded term. Hypothesis is
   finite_stateb e = true rather than the abstract finite_state e --
   strictly stronger, but exactly what Encoding.v's own construction
   provides at the leaf level (see the comment above), and what makes
   piece 3 tractable at all. *)

Theorem repr_rel_via_bounded_output
    (e : ka_term (list T * list T)) (L : ka_term (list T)) :
  finite_stateb e = true →
  bounded_output e →
  ka_term_proj1 e ⊑ L →
  ka_term_proj2 e ⊑ L →
  prefix_free L →
  repr_rel (Embed_pair enc e) (Embed_word enc L).
Proof.
move=> Hfs Hbo Hdom Hcod Hpf.
apply: bounded_output_repr_rel.
- exact: finite_state_transport.
- exact: bounded_output_transport.
- rewrite Embed_proj1_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: Hdom.
- rewrite Embed_proj2_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: Hcod.
- exact: prefix_free_transport.
Qed.

End BoundedOutputTransport.
