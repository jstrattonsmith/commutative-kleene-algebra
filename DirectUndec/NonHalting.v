(* The missing direction of CKAUndec/Encoding.v's characterization: if the
   MM2 program P does not terminate from s1, then red_lb P s1 ⋢ red_ub P in
   pre-KA. Together with mm2_R_completeness and mm2_R_soundness this gives

     red_leq P s1  is equivalent to  "P reaches (0,(0,0)) from s1"

   in the form red_leq_complete/red_leq_sound below, and constructively in
   the form red_leq_reach (red_leq → reaches (0,(0,0)), no Markov's
   principle), via the finite-witness version chain_le_stuck.

   The refutation is model-theoretic: the language model cannot tell the
   two terms apart (every finite prefix of the infinite run is covered by
   the "partially accepted" part of red_ub), so we use the omega-token model
   of DirectUndec/OmegaModel.v, instantiated with the steps of the run. The
   token for the infinite run belongs to red_lb, whose run word pairs agree
   letter by letter (the right component is the left one plus one
   configuration), while every token of red_ub is "bad": it comes after an
   explicit mismatch. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite relations.
From Stdlib Require Import Lia Relation_Operators Operators_Properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.repr_rel.
From kacc Require Import CKAUndec.Encoding CKAUndec.Glue.RtcBridge.
From kacc Require Import DirectUndec.OmegaModel.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

(** * Infinite runs *)

Section Run.

Variable P : list mm2_instr.

Definition next_or_self (s : mm2_state) : mm2_state :=
  match mm2_step_fun P s with
  | Some s' => s'
  | None => s
  end.

Definition run (s : mm2_state) (j : nat) : mm2_state :=
  Nat.iter j next_or_self s.

Lemma run_step s :
  ¬ mm2_terminates P s →
  ∀ j, clos_refl_trans _ (mm2_step P) s (run s j) ∧
       mm2_step P (run s j) (run s (S j)).
Proof.
move=> nt; elim=> [|j [reach step]].
- split; first exact: rt_refl.
  rewrite /run /= /next_or_self.
  case e: (mm2_step_fun P s) => [s'|]; first by apply/mm2_step_fun_spec.
  exfalso; apply: nt; exists s; split; first exact: rt_refl.
  by move=> s' /mm2_step_fun_spec; rewrite e.
- have reach' : clos_refl_trans _ (mm2_step P) s (run s (S j)).
  { apply: rt_trans reach _; exact: rt_step. }
  split => //.
  rewrite [run s (S (S j))]/run /= -/(run s (S j)) /next_or_self.
  case e: (mm2_step_fun P (run s (S j))) => [s'|].
  + by apply/mm2_step_fun_spec.
  + exfalso; apply: nt; exists (run s (S j)); split => //.
    by move=> s' /mm2_step_fun_spec; rewrite e.
Qed.

(** Reaching a stopped state is witnessed by a decidable search over the
    run, which is what Markov's principle needs. *)

Lemma run_reach s j : clos_refl_trans _ (mm2_step P) s (run s j).
Proof.
elim: j => [|j IH]; first exact: rt_refl.
apply: rt_trans IH _; rewrite [run s (S j)]/run /= -/(run s j) /next_or_self.
case e: (mm2_step_fun P (run s j)) => [s'|]; last exact: rt_refl.
by apply: rt_step; apply/mm2_step_fun_spec.
Qed.

Lemma reach_run s s' :
  clos_refl_trans _ (mm2_step P) s s' → mm2_stop P s' → ∃ j, run s j = s'.
Proof.
move=> /clos_rt_rt1n_iff reach stop; elim: reach stop => [x|x y z xy _ IH] stop.
- by exists 0.
- case: (IH stop) => j e; exists (S j).
  have nxy : next_or_self x = y.
  { by rewrite /next_or_self; move/mm2_step_fun_spec: xy => ->. }
  by rewrite /run Nat.iter_succ_r nxy.
Qed.

End Run.

(** * The generic refutation

    For any padded relation [pad_rel e] with a representation [R], and any
    infinite e-chain of non-empty words c 0, c 1, ..., the term
    Unit (1, c 0 #) ⋅ (pad_rel e)* is not below
    dpseudo_top ⋅ inj2 (pad_lang PA) ⊔ (the error term of R), whatever PA
    is. Both CKAUndec/Encoding.v's red_lb/red_ub and the binary-alphabet
    red_lb'/red_ub' of CKAUndec/BinaryAlphabet.v have this shape.

    The section proves a constructive strengthening (chain_le_stuck): the
    chain may get stuck (ok j = false: no e-step from c j), and an
    inequality yields a stuck position. The model's sequence repeats the
    first step after a stuck position (idx), so the token of the lower
    bound always exists; the badness of upper-bound tokens is witnessed at
    a finite position, so a bounded search finds the stuck step. *)

Section Generic.

Variable T : setoid.
Context `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Variables (e : ka_term (list T * list T)) (L PA : ka_term (list T)).
Variable R : repr_rel (pad_rel e) (pad_lang L).

Variable c : nat → list T.
Variable ok : nat → bool.
Hypothesis c_step : ∀ j, ok j = true → Unit (c j, c (S j)) ⊑ e.
Hypothesis ok0 : ok 0 = true.
Hypothesis c_ne : ∀ j, c j ≠ [].

Let A := option_setoid T.
Let Mon := prod_monoid (list_monoid A) (list_monoid A).

(** The padded words of the chain, and its steps as elements of the
    carrier monoid. *)

Definition w j : list A := map Some (c j) ⋅ [None].

Definition idx j : nat := if ok j then j else 0.

Lemma ok_idx j : ok (idx j) = true.
Proof. by rewrite /idx; case e': (ok j). Qed.

Definition rr j : Mon := (w (idx j), w (S (idx j))).

Lemma rr_le j : Unit (rr j) ⊑ pad_rel e.
Proof. exact: (sqsubseteq_pad_rel_1 (c_step (ok_idx j))). Qed.

(** Two components that disagree at some position. *)

Definition Bad (p : Mon) : Prop :=
  ∃ i x y, p.1 !! i = Some x ∧ p.2 !! i = Some y ∧ x ≠ y.

Global Instance Bad_proper : Proper ((≡) ==> iff) Bad.
Proof. by move=> p q /leibniz_equiv_iff ->. Qed.

Lemma Bad_mul p q : Bad p → Bad (p ⋅ q).
Proof.
case=> i [x [y [hx [hy xy]]]]; exists i, x, y; split; last split => //.
- exact: lookup_app_l_Some.
- exact: lookup_app_l_Some.
Qed.

Lemma not_Bad_prefix (u v : list A) : ¬ Bad (u, u ⋅ v).
Proof.
case=> i [x [y [/= hx [hy xy]]]]; apply: xy.
have := lookup_app_l_Some u v i x hx.
by rewrite /mul /= hy => - [].
Qed.

Lemma rseg_prefix (u : list A) k n :
  (∀ j, j < k + n → ok j = true) →
  ∃ W, ((u, u ⋅ w k) : Mon) ⋅ rseg rr k n ≡ (W, W ⋅ w (k + n)).
Proof.
elim: n u k => [|n IH] u k /= hok.
- by exists u; rewrite right_id Nat.add_0_r.
- case: (IH (u ⋅ w k) (S k)) => [j hj|W e']; first by apply: hok; lia.
  exists W; rewrite assoc.
  have -> : k + S n = S k + n by lia.
  rewrite /rr /idx (hok k ltac:(lia)); exact: e'.
Qed.

Lemma ok_upto n : (∀ j, j < n → ok j = true) ∨ ∃ j, ok j = false.
Proof.
elim: n => [|n [IH|IH]]; [by left => ??; lia| |by right].
case e': (ok n); last by right; exists n.
left => j hj.
have [?|->] : j < n ∨ j = n by lia.
- exact: IH.
- exact: e'.
Qed.

(** The token of the infinite chain lies in the lower bound and is not
    bad. *)

Definition chain_lb := Unit ((1, w 0) : Mon) ⋅ star (pad_rel e).

Definition chain_ub :=
  dpseudo_top ⋅ ka_term_inj2 (pad_lang PA) ⊔ repr_rel_rtc_error R.

Definition t0 : Mon := ((1, w 0) : Mon) ⋅ 1.

Lemma chain_lb_tok : om_tok (den rr chain_lb) t0 0.
Proof.
apply: den_tok_unit_mul; apply: den_tok_star => j _.
exact: rr_le.
Qed.

Lemma t0_good : tbad rr Bad t0 0 → ∃ j, ok j = false.
Proof.
case=> n hb; case: (ok_upto n) => [hok|//]; exfalso.
case: (@rseg_prefix [] 0 n hok) => W e'; move: hb.
have -> : t0 ⋅ rseg rr 0 n ≡ (W, W ⋅ w (0 + n)).
{ rewrite -e' /t0 right_id; reflexivity. }
exact: not_Bad_prefix.
Qed.

(** Every token of the upper bound is bad. *)

Lemma length_w j : 2 ≤ length (w j).
Proof.
rewrite /w /mul /= length_app length_map /=.
by have := @c_ne j; case: (c j) => //= *; lia.
Qed.

Lemma tokfree_dpseudo_top : tokfree (den rr (@dpseudo_top A _ _)).
Proof.
rewrite /dpseudo_top /ka_term_diag /pseudo_top.
apply: tokfree_map_star; apply: tokfree_star.
- apply: tokfree_proper; first by symmetry; apply:
    (semi_lattice_morphism_join_list (f := ka_term_map (pair_mor id id))).
  by apply: tokfree_join_list => g ?? [].
- move=> j /den_fin_unit /ka_term_diag_spec [_].
  rewrite -l_alt semi_lattice_morphism_join_list elem_of_lang_join_list.
  case=> g [_ /= /leibniz_equiv_iff e'].
  by have := length_w (idx j); rewrite e' /=; lia.
Qed.

Lemma tokfree_mismatch : tokfree (den rr (@mismatch A _ _)).
Proof. by apply: tokfree_join_list => - [??] ?? []. Qed.

Lemma Bad_dpseudo_top_mismatch x :
  om_fin (den rr (@dpseudo_top A _ _ ⋅ mismatch)) x → Bad x.
Proof.
rewrite (den_fin _ _ x).
case=> x1 [x2 [ex [h1 h2]]]; rewrite ex {ex x}.
have {}h1 : Unit x1 ⊑ @dpseudo_top A _ _ by apply/l_alt.
have {}h2 : Unit x2 ⊑ @mismatch A _ _ by apply/l_alt.
case: x1 h1 => s s' /sqsubseteq_dpseudo_top <-.
case: x2 h2 => m m' /le_mismatch_conv [a [b [ab [-> ->]]]].
exists (length s), a, b; split; last split => //.
- by rewrite /mul /= list_lookup_middle.
- by rewrite /mul /= list_lookup_middle.
Qed.

Lemma chain_ub_tok_bad t k : om_tok (den rr chain_ub) t k → tbad rr Bad t k.
Proof.
rewrite /chain_ub den_join; case.
- move=> h; exfalso; move: h.
  apply: tokfree_mul; first exact: tokfree_dpseudo_top.
  apply: (tokfree_map (r := rr)
            (g := @prod_inj2 (list_monoid A) (list_monoid A))
            (e := pad_lang PA)).
  move=> s j /leibniz_equiv_iff [e' _].
  by have := length_w (idx j); rewrite -e' /=; lia.
- rewrite /repr_rel_rtc_error !den_mul.
  apply: (tbad_mul_tok (Bad := Bad) Bad_mul).
  + move=> t' k'; apply: (tbad_mul_tok (Bad := Bad) Bad_mul).
    * move=> t'' k'' h; exfalso; move: h.
      apply: tokfree_mul; first exact: tokfree_dpseudo_top.
      exact: tokfree_mismatch.
    * exact: Bad_dpseudo_top_mismatch.
  + move=> x; apply: (bad_mul_fin (Bad := Bad) Bad_mul).
    exact: Bad_dpseudo_top_mismatch.
Qed.

Theorem chain_le_stuck : chain_lb ⊑ chain_ub → ∃ j, ok j = false.
Proof.
move=> le; apply: t0_good; apply: chain_ub_tok_bad.
exact: den_tok_le le chain_lb_tok.
Qed.

End Generic.

(** The non-constructive-looking special case: an infinite chain. *)

Section Infinite.

Variable T : setoid.
Context `{!LeibnizEquiv T, !EqDecision T, !Finite T}.

Variables (e : ka_term (list T * list T)) (L PA : ka_term (list T)).
Variable R : repr_rel (pad_rel e) (pad_lang L).

Variable c : nat → list T.
Hypothesis c_step : ∀ j, Unit (c j, c (S j)) ⊑ e.
Hypothesis c_ne : ∀ j, c j ≠ [].

Theorem chain_lb_not_le_chain_ub : ¬ chain_lb e c ⊑ chain_ub PA R.
Proof.
move=> /(chain_le_stuck (ok := λ _, true)) [|//|//|_ //].
by move=> j _; exact: c_step.
Qed.

End Infinite.

(** * Refuting red_lb ⊑ red_ub for non-terminating runs *)

Lemma mm2_config_ne P s : mm2_config P s ≠ [].
Proof.
rewrite /mm2_config /config_word => /(f_equal length).
by rewrite !length_app /=; lia.
Qed.

Theorem red_lb_not_le_red_ub P s1 :
  ¬ mm2_terminates P s1 → ¬ red_lb P s1 ⊑ red_ub P.
Proof.
move=> nt.
apply: (chain_lb_not_le_chain_ub (R := repr_rel_mm2_R P)
          (c := λ j, mm2_config P (run P s1 j))).
- by move=> j; have [_ step] := run_step nt j; exact: encoding_complete step.
- move=> j; exact: mm2_config_ne.
Qed.

(** * The characterization *)

Theorem red_leq_not_terminates P s1 :
  ¬ mm2_terminates P s1 → ¬ red_leq P s1.
Proof. exact: red_lb_not_le_red_ub. Qed.

(** If P does not reach (0,(0,0)) from s1, then red_leq fails: a run
    halting elsewhere is excluded by mm2_R_soundness, and a non-terminating
    run by the omega-token model. *)

Theorem red_leq_sound P s1 :
  ¬ clos_refl_trans _ (mm2_step P) s1 (0,(0,0)) → ¬ red_leq P s1.
Proof.
move=> nreach hle.
have nterm : ¬ mm2_terminates P s1.
{ case=> s2 [reach stop]; apply: nreach.
  by rewrite -(mm2_R_soundness (crt_to_rtc _ _ _ reach) stop hle). }
exact: (red_leq_not_terminates nterm hle).
Qed.

Theorem red_leq_complete P s1 :
  clos_refl_trans _ (mm2_step P) s1 (0,(0,0)) → red_leq P s1.
Proof. move=> reach; exact: mm2_R_completeness (crt_to_rtc _ _ _ reach). Qed.

(** * Constructively: an inequality yields a terminating run

    The stronger form of red_lb_not_le_red_ub, via chain_le_stuck: no
    Markov's principle is needed to get termination out of red_lb ⊑ red_ub,
    because the badness of red_ub's tokens is witnessed at a finite
    position of the run. *)

Definition step_ok P s : bool :=
  if mm2_step_fun P s is Some _ then true else false.

Lemma step_ok_step P s : step_ok P s = true → mm2_step P s (next_or_self P s).
Proof.
rewrite /step_ok /next_or_self.
by case e: (mm2_step_fun P s) => [s'|] // _; apply/mm2_step_fun_spec.
Qed.

Lemma step_ok_stop P s : step_ok P s = false → mm2_stop P s.
Proof.
rewrite /step_ok; case e: (mm2_step_fun P s) => [//|] _ s'.
by move/mm2_step_fun_spec; rewrite e.
Qed.

Theorem red_lb_le_terminates P s1 :
  red_lb P s1 ⊑ red_ub P → mm2_terminates P s1.
Proof.
move=> le.
case ok0: (step_ok P s1); last first.
{ exists s1; split; [exact: rt_refl|exact: step_ok_stop]. }
have [j stuck] := chain_le_stuck (R := repr_rel_mm2_R P)
  (c := λ j, mm2_config P (run P s1 j)) (ok := λ j, step_ok P (run P s1 j))
  (λ j h, encoding_complete (step_ok_step h)) ok0
  (λ j, @mm2_config_ne P (run P s1 j)) le.
exists (run P s1 j); split; [exact: run_reach|exact: step_ok_stop].
Qed.

Theorem red_leq_reach P s1 :
  red_leq P s1 → clos_refl_trans _ (mm2_step P) s1 (0,(0,0)).
Proof.
move=> hle; case: (red_lb_le_terminates hle) => s2 [reach stop].
by rewrite -(mm2_R_soundness (crt_to_rtc _ _ _ reach) stop hle).
Qed.
