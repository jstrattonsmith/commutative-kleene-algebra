(* Undecidability of pre-KA term equality, by a direct reduction from MM2
   halting: no effective inseparability, no CT_L, no MP.

   The problem is PreKA_EQ: given two pre-KA terms over the fixed carrier
   list nat * list nat (two free monoids over nat, multiplied componentwise,
   i.e. a commutative product of free monoids), are they equal modulo the
   pre-KA axioms? Terms over a machine-dependent finite alphabet are moved to
   this fixed carrier along an injective letter encoding, which preserves and
   reflects pre-KA equality (the decoding is a left inverse monoid morphism).

   The reduction mm2_to_eq sends a machine instance x = (P, a, b) to the
   pair (red_lb ⊔ red_ub, red_ub), so that the instance holds iff
   red_lb ⊑ red_ub. By DirectUndec/NonHalting.v:

     MM2_HALTS_ON_ZERO x  ->  PreKA_EQ (mm2_to_eq x)             (reduction_yes)
     ~ MM2_HALTS_ON_ZERO x  ->  ~ PreKA_EQ (mm2_to_eq x)          (reduction_no)

   Classically this is a many-one reduction. Constructively the converse of
   the first line would need Markov's principle, but the two lines are
   exactly what the library's notion of undecidability needs:
   a decider for PreKA_EQ decides the complement of MM2_HALTS_ON_ZERO, hence
   (along the library's reduction chain from SBTM_HALT) the complement of
   SBTM_HALT, which complement_SBTM_HALT_undec turns into co-enumerability
   of SBTM_HALT. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite countable.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang.
From kacc Require Import CKAUndec.Encoding DirectUndec.NonHalting.
From Undecidability.Synthetic Require Import Definitions ReducibilityFacts.
From Undecidability.MinskyMachines Require Import MM2.
Require Undecidability.Synthetic.Undecidability.
Require Undecidability.TM.SBTM_undec.
Require Undecidability.StackMachines.Reductions.SBTM_HALT_to_HaltBSM.
Require Undecidability.StackMachines.Util.BSM_sss.
Require Undecidability.MinskyMachines.Reductions.BSM_MM.
Require Undecidability.FRACTRAN.Reductions.MM_FRACTRAN.
Require Undecidability.MinskyMachines.Reductions.FRACTRAN_to_MMA2.
Require Undecidability.MinskyMachines.Reductions.MMA2_to_MM2.

(** * The problem *)

Definition natS : setoid := eq_setoid nat.

Global Instance natS_leibniz : LeibnizEquiv natS.
Proof. by move=> x y. Qed.

Definition Mnat : monoid := prod_monoid (list_monoid natS) (list_monoid natS).

Definition PreKA_EQ (p : ka_term Mnat * ka_term Mnat) : Prop := p.1 ≡ p.2.

(** * Moving terms to the fixed carrier *)

Section Transport.

Context {A : setoid} `{!LeibnizEquiv A, !EqDecision A, !Countable A}.

Let Mon := prod_monoid (list_monoid A) (list_monoid A).

Definition enc_pair (p : Mon) : Mnat :=
  (map encode_nat p.1, map encode_nat p.2).

Definition dec_pair (p : Mnat) : Mon :=
  (omap decode_nat p.1, omap decode_nat p.2).

Global Instance enc_pair_morphism : MonoidMorphism enc_pair.
Proof.
split.
- by move=> p q /leibniz_equiv_iff ->.
- by [].
- by move=> p q; rewrite /enc_pair /mul /= !map_app.
Qed.

Global Instance dec_pair_morphism : MonoidMorphism dec_pair.
Proof.
split.
- by move=> p q /leibniz_equiv_iff ->.
- by [].
- by move=> p q; rewrite /dec_pair /mul /= !omap_app.
Qed.

Lemma omap_decode_encode (l : list A) :
  omap decode_nat (map encode_nat l) = l.
Proof. by elim: l => //= x l IH; rewrite decode_encode_nat; f_equal. Qed.

Lemma dec_enc_pair p : dec_pair (enc_pair p) = p.
Proof.
by case: p => u v; rewrite /dec_pair /enc_pair /= !omap_decode_encode.
Qed.

Lemma ka_term_map_id_ext {T : monoid} (f : T → T) `{!MonoidMorphism f} :
  (∀ x, f x ≡ x) → ∀ e, ka_term_map f e ≡ e.
Proof.
move=> hf e; rewrite /ka_term_map; elim: e => /=.
- by move=> x; rewrite /compose hf.
- by [].
- by move=> e1 IH1 e2 IH2; rewrite /= IH1 IH2.
- by move=> e1 IH1 e2 IH2; rewrite /= IH1 IH2.
- by move=> e IH; rewrite /= IH.
Qed.

Lemma enc_term_reflect (e1 e2 : ka_term Mon) :
  ka_term_map enc_pair e1 ≡ ka_term_map enc_pair e2 → e1 ≡ e2.
Proof.
move=> /(pre_ka_morphism_proper (f := ka_term_map dec_pair)) e.
rewrite !ka_term_map_comp in e.
by rewrite !ka_term_map_id_ext // in e => x /=; rewrite dec_enc_pair.
Qed.

End Transport.

(** * The reduction *)

Global Instance mm_sym_countable n : Countable (mm_sym (fin n)) :=
  finite_countable.

Global Instance mmA_eq_dec n :
  EqDecision (option_setoid (@mm_sym_setoid (fin n))) :=
  _ : EqDecision (option (mm_sym (fin n))).

Global Instance mmA_countable n :
  Countable (option_setoid (@mm_sym_setoid (fin n))) :=
  _ : Countable (option (mm_sym (fin n))).

Global Instance mmA_leibniz n :
  LeibnizEquiv (option_setoid (@mm_sym_setoid (fin n))) :=
  _ : LeibnizEquiv (option (mm_sym (fin n))).

Definition mm2_to_eq (x : MM2_PROBLEM) : ka_term Mnat * ka_term Mnat :=
  match x with
  | (P, a, b) =>
      (ka_term_map enc_pair (red_lb P (1%nat, (a, b)) ⊔ red_ub P),
       ka_term_map enc_pair (red_ub P))
  end.

Lemma reduction_yes x : MM2_HALTS_ON_ZERO x → PreKA_EQ (mm2_to_eq x).
Proof.
case: x => [[P a] b] /= /red_leq_complete /sqsubseteq_iff e.
rewrite /PreKA_EQ /=.
exact: (pre_ka_morphism_proper (f := ka_term_map enc_pair)) e.
Qed.

Lemma reduction_no x : ¬ MM2_HALTS_ON_ZERO x → ¬ PreKA_EQ (mm2_to_eq x).
Proof.
case: x => [[P a] b] /= /red_leq_sound nle.
rewrite /PreKA_EQ /= => /enc_term_reflect e.
by apply: nle; apply/sqsubseteq_iff.
Qed.

(** * Undecidability *)

Lemma SBTM_HALT_to_MM2_HALTS_ON_ZERO :
  SBTM.SBTM_HALT ⪯ MM2_HALTS_ON_ZERO.
Proof.
eapply reduces_transitive; first exact SBTM_HALT_to_HaltBSM.reduction.
eapply reduces_transitive.
  by exists id => x; symmetry; apply: BSM_sss.Halt_BSM_iff.
eapply reduces_transitive; first exact BSM_MM.BSM_MM_HALTING.
eapply reduces_transitive; first exact MM_FRACTRAN.MM_FRACTRAN_REG_HALTING.
eapply reduces_transitive.
  exact FRACTRAN_to_MMA2.FRACTRAN_REG_MMA2_HALTS_ON_ZERO.
exact MMA2_to_MM2.MMA2_MM2_HALTS_ON_ZERO.
Qed.

Theorem PreKA_EQ_undec : Undecidability.undecidable PreKA_EQ.
Proof.
move=> [d hd].
apply: SBTM_undec.complement_SBTM_HALT_undec.
apply: (dec_red (reduces_complement SBTM_HALT_to_MM2_HALTS_ON_ZERO)).
exists (λ x, negb (d (mm2_to_eq x))) => x.
rewrite /reflects /complement; split.
- move=> nh; case e: (d (mm2_to_eq x)) => //.
  by exfalso; apply: (reduction_no nh); apply/hd.
- case e: (d (mm2_to_eq x)) => //= _ h.
  by move: e; have /hd -> := reduction_yes h.
Qed.

(** The two halves of the reduction, packaged: on the instances where the
    machine halts it lands in PreKA_EQ, on the others outside it. *)

Theorem PreKA_EQ_reduction :
  ∃ f : MM2_PROBLEM → ka_term Mnat * ka_term Mnat,
    ∀ x, (MM2_HALTS_ON_ZERO x → PreKA_EQ (f x)) ∧
         (¬ MM2_HALTS_ON_ZERO x → ¬ PreKA_EQ (f x)).
Proof.
exists mm2_to_eq => x; split; [exact: reduction_yes|exact: reduction_no].
Qed.
