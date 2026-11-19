(* Why DirectUndec/NonHalting.v does not carry over to KA.

   In the free KA (Kozen's star induction on top of the pre-KA axioms),
   red_lb P s1 ⊑ red_ub P holds whenever the configurations reachable from s1
   form a finite set that is closed under steps and contains no halting
   configuration other than (0,(0,0)) (fka_red_leq_closed). The proof is
   ordinary invariant reasoning: star induction with the invariant
   "the right component has advanced to one of finitely many configurations,
   or there was a mismatch".

   In particular KA proves the inequality for the two-instruction machine
   loop_prog, which never halts from (1,(0,0)) (loop_not_terminates,
   fka_red_leq_loop). So over the free KA the set of machines satisfying the
   inequality lies strictly between "halts at (0,(0,0))" and "does not halt
   elsewhere", and no direct reduction from halting can be built on this
   encoding: the omega-token model of DirectUndec/OmegaModel.v is not a
   Kleene algebra, and no model can refute an inequality that KA proves. *)

Require Import Stdlib.Classes.Morphisms.
Require Import Stdlib.Unicode.Utf8.
Require Import ssreflect.
Require Import Stdlib.Setoids.Setoid.
From stdpp Require Import base list finite relations.
From Stdlib Require Import Lia Relation_Operators Operators_Properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.ka.
From kacc Require Import KA.repr_rel CKAUndec.Encoding.
From kacc Require Import DirectUndec.NonHalting.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

Section Closed.

Variable P : list mm2_instr.
Variable s1 : mm2_state.
Variable Sset : list mm2_state.

Hypothesis s1_S : s1 ∈ Sset.
Hypothesis S_ok : ∀ s, s ∈ Sset → s = (0,(0,0)) ∨ 0 < s.1 ≤ length P.
Hypothesis S_closed : ∀ s s', s ∈ Sset → mm2_step P s s' → s' ∈ Sset.

Let Q := fin (S (S (length P))).
Let A := option_setoid (@mm_sym_setoid Q).
Let Mon := prod_monoid (list_monoid A) (list_monoid A).

Definition wS (s : mm2_state) : list A := map Some (mm2_config P s) ⋅ [None].

Definition SW : list (list A) := map wS Sset.

Let R := pad_rel (mm2_R P).
Let RR := repr_rel_mm2_R P.

Lemma map_Some_pad_inj (u v : list (mm_sym Q)) :
  (map Some u ⋅ [None] : list A) = map Some v ⋅ [None] → u = v.
Proof.
move=> e; have [{}e _] := app_inj_tail _ _ _ _ e; move: e.
by elim: u v => [|x u IH] [|y v] //= [-> /IH ->].
Qed.

(** One step from a configuration of S: either the next configuration,
    again in S, or a mismatch. *)

Lemma strings_r_SW_step :
  strings_r SW ⋅ R ⊑ dpseudo_top ⋅ strings_r SW ⊔
                     dpseudo_top ⋅ mismatch ⋅ residue RR.
Proof.
rewrite /strings_r join_list_left_dist join_list_sqsubseteq => w.
case/elem_of_list_fmap => s [-> sS].
etransitivity.
  apply: (expand_rel RR); apply: sqsubseteq_pad_lang_1; exact: elem_of_T.
apply: join_mono => //.
apply: pre_ka_mul_mono; first by apply/sqsubseteq_dpseudo_top.
apply/join_list_sqsubseteq => ys /(next_spec RR) /sqsubseteq_pad_rel_2.
case=> - [u v] [[e1 e2]] /= le.
move/map_Some_pad_inj: e1 => e1; rewrite -e1 in le.
case/encoding_sound: le => s2 [ev step].
rewrite e2 /= ev; apply: sqsubseteq_join_list.
apply/elem_of_list_fmap; exists s2; split => //.
exact: S_closed step.
Qed.

Lemma strings_r_SW_ub :
  strings_r SW ⊑ ka_term_inj2 (pad_lang (partially_accepted P)).
Proof.
rewrite /strings_r join_list_sqsubseteq => w.
case/elem_of_list_fmap => s [-> sS].
change (Unit (1, wS s)) with (ka_term_inj2 (T := list_monoid A) (Unit (wS s))).
apply: semi_lattice_morphism_sqsubseteq_proper.
apply: sqsubseteq_pad_lang_1.
case: (S_ok sS) => [->|act].
- exact: sqsubseteq_join_right.
- etransitivity; last exact: sqsubseteq_join_left.
  by apply/elem_of_C.
Qed.

Lemma one_le_dpseudo_top : (1 : ka_term Mon) ⊑ dpseudo_top.
Proof. by apply/sqsubseteq_dpseudo_top. Qed.

(** KA facts about the diagonal pseudo-top and the star of R. *)

Let D : fka Mon := FKA dpseudo_top.

Lemma D_mul_D : D ⋅ D ⊑ D.
Proof.
rewrite /D /dpseudo_top /ka_term_diag /pseudo_top.
set b := join_list _ _.
change (star (FKA (ka_term_map (pair_mor id id) b)) ⋅
        star (FKA (ka_term_map (pair_mor id id) b)) ⊑
        star (FKA (ka_term_map (pair_mor id id) b))).
by rewrite ka_star_mul_star.
Qed.

Lemma star_mul_self (x : fka Mon) : star x ⋅ x ⊑ star x.
Proof.
by rewrite (ka_star_comm (x := x) (y := x)) //; exact: pre_ka_mul_star.
Qed.

Lemma lb_start : Unit (1, wS s1) ⊑ dpseudo_top ⋅ strings_r SW.
Proof.
rewrite -[Unit _](left_id 1 (⋅)).
apply: pre_ka_mul_mono; first exact: one_le_dpseudo_top.
apply: sqsubseteq_join_list; apply/elem_of_list_fmap; by exists s1.
Qed.

Theorem fka_red_leq_closed : FKA (red_lb P s1) ⊑ FKA (red_ub P).
Proof.
set SWt : fka Mon := FKA (strings_r SW).
set Mt : fka Mon := FKA mismatch.
set Pt : fka Mon := FKA (residue RR).
set Rt : fka Mon := FKA R.
set inv : fka Mon := D ⋅ SWt ⊔ D ⋅ Mt ⋅ Pt ⋅ star Rt.
have step : SWt ⋅ Rt ⊑ D ⋅ SWt ⊔ D ⋅ Mt ⋅ Pt.
{ exact: (fka_le_of_pre strings_r_SW_step). }
have start : FKA (Unit (1, wS s1)) ⊑ D ⋅ SWt.
{ exact: (fka_le_of_pre lb_start). }
have inv_ub : inv ⊑ FKA (red_ub P).
{ change (FKA (dpseudo_top ⋅ strings_r SW) ⊔
          FKA (dpseudo_top ⋅ mismatch ⋅ residue RR ⋅ star R) ⊑
          FKA (dpseudo_top ⋅ ka_term_inj2 (pad_lang (partially_accepted P))) ⊔
          FKA (repr_rel_rtc_error RR)).
  apply: join_mono; last reflexivity.
  apply: fka_le_of_pre; apply: pre_ka_mul_mono => //.
  exact: strings_r_SW_ub. }
etransitivity; last exact: inv_ub.
change (FKA (Unit (1, wS s1)) ⋅ star Rt ⊑ inv).
apply: ka_star_ind_r; apply/join_sqsubseteq; split.
- by etransitivity; [exact: start|exact: sqsubseteq_join_left].
- rewrite /inv pre_ka_left_dist; apply/join_sqsubseteq; split.
  + etransitivity.
      rewrite -assoc; apply: pre_ka_mul_mono; [reflexivity|exact: step].
    rewrite pre_ka_right_dist !assoc.
    apply: join_mono.
    * by apply: pre_ka_mul_mono; [exact: D_mul_D|].
    * rewrite -[X in X ⊑ _](right_id 1 (⋅)).
      apply: pre_ka_mul_mono; last exact: pre_ka_one_star.
      apply: pre_ka_mul_mono => //.
      by apply: pre_ka_mul_mono; [exact: D_mul_D|].
  + etransitivity; last exact: sqsubseteq_join_right.
    rewrite -[X in X ⊑ _]assoc.
    by apply: pre_ka_mul_mono; [|exact: star_mul_self].
Qed.

End Closed.

(** * A non-terminating machine for which KA proves the inequality *)

Local Close Scope ka_scope.

Definition loop_prog : list mm2_instr := [mm2_inc_a; mm2_dec_a 1].

Lemma loop_step1 : mm2_step loop_prog (1,(0,0)) (2,(1,0)).
Proof. by apply/mm2_step_fun_spec. Qed.

Lemma loop_step2 : mm2_step loop_prog (2,(1,0)) (1,(0,0)).
Proof. by apply/mm2_step_fun_spec. Qed.

Lemma loop_closed s s' :
  s ∈ [(1,(0,0)); (2,(1,0))] → mm2_step loop_prog s s' →
  s' ∈ [(1,(0,0)); (2,(1,0))].
Proof.
move=> /elem_of_list_In [<-|[<-|[]]] /mm2_step_fun_spec /= [<-];
  by apply/elem_of_list_In; simpl; auto.
Qed.

Lemma loop_reach x y :
  clos_refl_trans _ (mm2_step loop_prog) x y →
  x ∈ [(1,(0,0)); (2,(1,0))] → y ∈ [(1,(0,0)); (2,(1,0))].
Proof.
elim=> [x' y' st|x'|x' y' z' _ IH1 _ IH2] hx.
- exact: loop_closed hx st.
- done.
- exact: IH2 (IH1 hx).
Qed.

Lemma loop_not_terminates : ¬ mm2_terminates loop_prog (1,(0,0)).
Proof.
case=> s [reach stop].
have := loop_reach reach (ltac:(by apply/elem_of_list_In; left)).
move=> /elem_of_list_In [e|[e|[]]]; rewrite -e in stop.
- exact: stop _ loop_step1.
- exact: stop _ loop_step2.
Qed.

Theorem fka_red_leq_loop :
  FKA (red_lb loop_prog (1,(0,0))) ⊑ FKA (red_ub loop_prog).
Proof.
apply: (fka_red_leq_closed (Sset := [(1,(0,0)); (2,(1,0))])).
- by apply/elem_of_list_In; left.
- move=> s /elem_of_list_In [<-|[<-|[]]]; right => /=; lia.
- exact: loop_closed.
Qed.

(** The KA analogue of NonHalting.v's red_leq_not_terminates is false. *)

Corollary fka_red_leq_not_terminates_fails :
  ¬ (∀ P s1, ¬ mm2_terminates P s1 →
             ¬ FKA (red_lb P s1) ⊑ FKA (red_ub P)).
Proof.
move=> H; exact: H _ _ loop_not_terminates fka_red_leq_loop.
Qed.
