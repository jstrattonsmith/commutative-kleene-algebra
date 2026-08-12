(* CKA-specific wiring closing Arthur's comment 2 for real: applies
   BoundedOutputTransport.v's route-1 machinery to mm.v's own mm2_R/T
   (the transition relation and configuration set for a FIXED program
   Prog := progOf c), and re-runs mm.v's own soundness/completeness
   argument (mm2_R_completeness/mm2_R_soundness) at the embedded level
   to get order-REFLECTION for red_lb/red_ub, which is what actually
   closes the gap -- having a repr_rel for the embedded term alone is
   not enough; Arthur's point was specifically that inequality needs
   to be shown m-complete over the CANONICAL 2-symbol alphabet, which
   needs reflection (Embed_pair(red_lb) ⊑ Embed_pair(red_ub) -> red_lb
   ⊑ red_ub), not just preservation (the free direction).

   Key simplification found while wiring this up: bounded_output_repr_rel'
   (bounded_output.v:801) already handles ALL of the pad_rel/pad_lang
   lifting internally (finite_state_pad_rel, bounded_output_pad_rel,
   pad_rel_pad_lang_1/2, prefix_free_pad_lang) -- so there is no need
   for a separate "primed" version of repr_rel_via_bounded_output. We
   embed mm2_R/T at the UNPADDED mm_sym QF level directly (reusing
   BoundedOutputTransport.v's transport lemmas, which are generic over
   any finite alphabet), then hand the embedded, still-unpadded terms
   straight to the EXISTING bounded_output_repr_rel', exactly mirroring
   how mm.v itself builds repr_rel_mm2_R (mm.v:1316-1325). *)

From Stdlib Require Import Unicode.Utf8 Arith Lia Bool.
Require Import ssreflect.
From stdpp Require Import base list finite relations.
From kacc Require Import utils algebra pre_ka lang automata repr_rel
  bounded_output.
From kacc Require Import BinaryAlphabetTransport BoundedOutputTransport.
From Undecidability.MinskyMachines Require Import MM2.
Require Import SyntheticComputability.Shared.partial.
Require kacc.mm.
From kacc Require Import EffectiveInseparability_MM2.
From kacc Require Import Theorem17_KATerm K_Enumerable.
From kacc Require Import Theorem19_MComplete Theorem19_Full.

Section BinaryAlphabet.

Variable c : nat.
Notation Prog := (progOf c).
Let QF : Type := fin (S (S (length Prog))).

Instance QF_eqdec' : EqDecision QF.
Proof. apply _. Defined.

Instance QF_finite' : Finite QF.
Proof. apply _. Defined.

(* The source alphabet for the embedding: mm.v's own mm_sym QF, exactly
   as it appears (unpadded) in mm2_R/T/C. *)

Notation TAlph := (@mm.mm_sym_setoid QF).

Lemma binary_encoding_exists :
  ∃ (k : nat) (enc : mm.mm_sym QF → list bool),
    (∀ x y, enc x = enc y → x = y) ∧ (∀ x, length (enc x) = k) ∧ 0 < k.
Proof.
have [k [enc [Henc Hlen]]] := finite_binary_encoding TAlph.
exists k, enc; do 2 (split; first done).
destruct k as [|k]; last lia.
exfalso.
have Ha : enc (@mm.mm_a QF) = [] by apply/length_zero_iff_nil; exact: Hlen.
have Hb : enc (@mm.mm_b QF) = [] by apply/length_zero_iff_nil; exact: Hlen.
have Eab : enc (@mm.mm_a QF) = enc (@mm.mm_b QF) by rewrite Ha Hb.
have := Henc _ _ Eab.
discriminate.
Qed.

Section WithEncoding.

Context (k : nat) (enc : setoid_car (@mm.mm_sym_setoid QF) → list bool).
Context (Henc : ∀ x y, enc x = enc y → x = y).
Context (Hlen : ∀ x, length (enc x) = k).
Context (Hk_pos : 0 < k).

Instance enc_inj : Inj (=) (=) enc.
Proof. exact: Henc. Qed.

(* mm2_R's type is the bare product `list (mm_sym QF) * list (mm_sym QF)`,
   which does not syntactically unify with `monoid_car ?T` during
   typeclass search without help (same issue flagged in
   EffectiveInseparability_MM2.v's own comment on red_leq) -- name the
   monoid explicitly, mirroring K_Enumerable.v's TmMonoid but WITHOUT
   the option-padding (mm2_R itself is unpadded). *)
Definition Mm2RMonoid : monoid :=
  prod_monoid (list_monoid (@mm.mm_sym_setoid QF))
              (list_monoid (@mm.mm_sym_setoid QF)).

(* Boolean (decidable, syntactic) analogue of automata.v's
   finite_state_join_list -- needed since BoundedOutputTransport.v's
   finite_stateb_transport operates on the syntactic finite_stateb
   check, not the abstract finite_state notion mm.v itself uses to
   establish finite_state (mm2_R Prog). bounded_output, by contrast,
   is transported abstractly (bounded_output_transport takes the
   abstract Sigma-type witness directly), so bounded_output_join_list
   (already generic, bounded_output.v:94-101) is reused as-is below
   with no boolean intermediate needed. *)
Lemma finite_stateb_join_list {T : monoid} `{!IsOne T} {I}
    (P : I → ka_term (monoid_car T)) (xs : list I) :
  (∀ x, x ∈ xs → finite_stateb (P x) = true) →
  finite_stateb (join_list P xs) = true.
Proof.
elim: xs => [|x xs IH] //= H.
apply/andb_true_iff; split.
- apply: H. exact: elem_of_list_here.
- apply: IH => y Hy. apply: H. exact: elem_of_list_further.
Qed.

Lemma finite_stateb_mm2_R : @finite_stateb Mm2RMonoid _ (mm.mm2_R Prog) = true.
Proof.
apply: finite_stateb_join_list => q Hq.
by case: (mm.mm2_prog q).
Qed.

Lemma bounded_output_mm2_R : bounded_output (T := @mm.mm_sym_setoid QF) (mm.mm2_R Prog).
Proof.
apply: bounded_output_join_list => q Hq.
by case: (mm.mm2_prog q) => *; apply: bounded_outputbP.
Qed.

Lemma repr_rel_embedded :
  repr_rel (pad_rel (Embed_pair enc (mm.mm2_R Prog)))
           (pad_lang (Embed_word enc (mm.T Prog))).
Proof.
apply: bounded_output_repr_rel'.
- apply: finite_stateP.
  + done.
  + rewrite -(finite_stateb_transport (@mm.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
    apply/Is_true_true. exact: finite_stateb_mm2_R.
- exact: bounded_output_transport bounded_output_mm2_R.
- rewrite Embed_proj1_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: mm.mm2_R_ub1' Prog.
- rewrite Embed_proj2_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: mm.mm2_R_ub2 Prog.
Qed.

(* --- Re-running mm.v's own soundness/completeness argument at the
   embedded level, using repr_rel_embedded as the witness, mirroring
   mm2_R_completeness/mm2_R_soundness (mm.v:1391-1410,1365-1374)
   exactly -- the generic lemmas they build on (repr_rel_iter_final,
   repr_rel_rtc_soundness') take an arbitrary repr_rel witness, so
   nothing about their OWN proofs needs re-deriving, only the
   surrounding argument (pushing rtc/determinism/no-step-from-halt
   through the embedding) needs restating. *)

Lemma step_embed (x y : list (setoid_car (@mm.mm_sym_setoid QF))) :
  Unit (x, y) ⊑ mm.mm2_R Prog →
  Unit (enc_word enc x, enc_word enc y) ⊑ Embed_pair enc (mm.mm2_R Prog).
Proof.
move=> Hxy.
have -> : Unit (enc_word enc x, enc_word enc y)
        = Embed_pair enc (Unit (x, y)) by [].
apply: semi_lattice_morphism_sqsubseteq_proper. exact: Hxy.
Qed.

Lemma rtc_embed (x y : list (setoid_car (@mm.mm_sym_setoid QF))) :
  rtc (λ xs ys : list (setoid_car (@mm.mm_sym_setoid QF)),
        Unit (xs, ys) ⊑ mm.mm2_R Prog) x y →
  rtc (λ xs ys, Unit (xs, ys) ⊑ Embed_pair enc (mm.mm2_R Prog))
    (enc_word enc x) (enc_word enc y).
Proof.
elim=> // x0 y0 z0 xy0 _ IH.
apply: rtc_l IH. exact: step_embed xy0.
Qed.

Lemma mm2_R_completeness' (s1 : nat * (nat * nat)) :
  rtc (mm2_step Prog) s1 (0, (0, 0)) →
  Unit (1, (Some <$> enc_word enc (mm.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (mm.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (mm.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded.
Proof.
move=> /mm.encoding_rtc_complete /rtc_embed xs_ys.
change (Unit (1, (Some <$> enc_word enc (mm.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (mm.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2
      (pad_lang (Embed_word enc (mm.C Prog)
                   ⊔ Unit (enc_word enc (mm.mm2_config Prog (0, (0, 0))))))
    ⊔ repr_rel_rtc_error repr_rel_embedded).
rewrite pad_lang_join.
have -> : pad_lang (Unit (enc_word enc (mm.mm2_config Prog (0, (0, 0)))))
        ≡ Unit ((Some <$> enc_word enc (mm.mm2_config Prog (0, (0, 0)))) ⋅ [None]).
{ by rewrite /pad_lang /ka_term_map /repr_rel.lift /=
    (monoid_morphism_mul (f := Unit)). }
apply: repr_rel_iter_final xs_ys.
- have := mm.elem_of_T Prog s1.
  have -> : Unit (enc_word enc (mm.mm2_config Prog s1))
          = Embed_word enc (Unit (mm.mm2_config Prog s1)) by [].
  apply: semi_lattice_morphism_sqsubseteq_proper.
- rewrite Embed_proj1_natural.
  apply: semi_lattice_morphism_sqsubseteq_proper. exact: mm.mm2_R_ub1 Prog.
- move=> xs ys1 ys2 xs_ys1 xs_ys2.
  have [x1 [y1 [Ex1 [Ey1 Hin1]]]] :=
    Embed_pair_inv (@mm.mm_sym_setoid QF) bool_setoid enc (mm.mm2_R Prog) xs ys1 xs_ys1.
  have [x2 [y2 [Ex2 [Ey2 Hin2]]]] :=
    Embed_pair_inv (@mm.mm_sym_setoid QF) bool_setoid enc (mm.mm2_R Prog) xs ys2 xs_ys2.
  have Ex : x1 = x2.
  { apply: (enc_word_inj (@mm.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
    rewrite -Ex1 -Ex2. done. }
  subst x2.
  have Hpx1 : Unit x1
      ⊑ @ka_term_proj1 (list_monoid TAlph) (list_monoid TAlph) (mm.mm2_R Prog)
    by rewrite -Hin1.
  rewrite (mm.mm2_R_ub1 Prog) (mm.C_T Prog) in Hpx1.
  case/mm.elem_of_T_inv: Hpx1 => s x1_s.
  rewrite x1_s in Hin1 Hin2.
  case/mm.encoding_sound: Hin1 => s1' [] y1_s1' s_s1'.
  case/mm.encoding_sound: Hin2 => s2' [] y2_s2' s_s2'.
  have Es : s1' = s2' by exact: mm.mm2_step_det s_s1' s_s2'.
  by rewrite Ey1 Ey2 y1_s1' y2_s2' Es.
- move=> ys' Hys'.
  have [x0 [y0 [Ex0 [Ey0 Hin0]]]] :=
    Embed_pair_inv (@mm.mm_sym_setoid QF) bool_setoid enc (mm.mm2_R Prog) _ _ Hys'.
  have Ex0' : mm.mm2_config Prog (0, (0, 0)) = x0.
  { apply: (enc_word_inj (@mm.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
    exact: Ex0. }
  rewrite -Ex0' in Hin0.
  exact: mm.no_step_from_halt Hin0.
Qed.

Lemma mm2_R_soundness_aux' (s1 s2 : nat * (nat * nat)) :
  rtc (mm2_step Prog) s1 s2 →
  Unit (1, (Some <$> enc_word enc (mm.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (mm.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (mm.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded →
  s2 = (0, (0, 0)) ∨ 0 < s2.1 ≤ length Prog.
Proof.
move=> /mm.encoding_rtc_complete /rtc_embed s1_s2.
rewrite /repr_rel_rtc_error -assoc => ub.
have pa : Unit (enc_word enc (mm.mm2_config Prog s2))
        ⊑ Embed_word enc (mm.partially_accepted Prog).
{ exact: repr_rel_rtc_soundness' s1_s2 ub. }
have [w [Ew Hw]] :=
  Embed_word_inv (@mm.mm_sym_setoid QF) bool_setoid enc
    (mm.partially_accepted Prog) _ pa.
have Ew' : mm.mm2_config Prog s2 = w.
{ apply: (enc_word_inj (@mm.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
  exact: Ew. }
have pa0 : @sqsubseteq (ka_term (list TAlph)) _
             (Unit (mm.mm2_config Prog s2)) (mm.partially_accepted Prog).
{ rewrite Ew'. exact: Hw. }
have pa1 : @sqsubseteq (ka_term (list TAlph)) _
             (Unit (mm.mm2_config Prog s2)) (mm.C Prog)
         ∨ mm.mm2_config Prog s2 = mm.mm2_config Prog (0, (0, 0)).
{ move: pa0 => /l_alt.
  rewrite /mm.partially_accepted semi_lattice_morphism_join.
  case=> H.
  - left. apply/l_alt. exact: H.
  - right. move: H => /= H. exact: (proj1 (leibniz_equiv_iff _ _) H). }
case: pa1 => pa1.
- right. apply/mm.elem_of_C. exact: pa1.
- left.
  move: pa1.
  clear s1_s2 ub pa Ew Hw Ew' pa0.
  rewrite /mm.mm2_config /mm.config_word /=.
  by case: s2 => [[|?] [[|?] [|?]]] //=.
Qed.

Lemma mm2_R_soundness' (s1 s2 : nat * (nat * nat)) :
  rtc (mm2_step Prog) s1 s2 →
  mm2_stop Prog s2 →
  Unit (1, (Some <$> enc_word enc (mm.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (mm.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (mm.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded →
  s2 = (0, (0, 0)).
Proof.
move=> s1_s2 /mm.mm2_stop_spec s2_stop red_leq.
have [//|] := mm2_R_soundness_aux' s1_s2 red_leq.
congruence.
Qed.

(* --- Final step: mirror R_target_iff_outcome
   (EffectiveInseparability_MM2.v:289-320) at the embedded level,
   substituting mm2_R_completeness'/mm2_R_soundness' for the
   originals -- everything else in that proof (mm2_iter_rtc,
   mm2_haltedAt, mm2_stop_of_step_fun_none, mm2_state_eqb) is a plain
   fact about the MM2 execution model, not about repr_rel/KA-terms, so
   it transfers unchanged. Combining both versions for the SAME v
   gives the order-reflection R_target c y <-> red_leq' (1,(y,0)),
   which is exactly the many-one reduction needed to transport
   m-completeness to the embedded/binary-alphabet relation. *)

Definition red_leq' (s1 : nat * (nat * nat)) : Prop :=
  ltac:(let t := type of (@mm2_R_completeness' s1) in
        match t with _ -> ?B => exact B end).

Lemma R_target_iff_outcome' y v :
  Θ_ours_MM2 c y =! v -> (red_leq' (1%nat, (y, 0%nat)) ↔ v = 1%nat).
Proof.
intros [n Hn] % seval_hasvalue.
rewrite seval_Theta_ours_MM2 in Hn.
unfold red_leq'.
assert (Hrtc : rtc (mm2_step Prog) (1%nat, (y, 0%nat)) (mm2_iter Prog n (1%nat, (y, 0%nat))))
  by apply mm2_iter_rtc.
unfold mm2_outcome_at in Hn.
destruct (mm2_haltedAt Prog n (1%nat, (y, 0%nat))) eqn:Ehalt; [| discriminate].
assert (Hstop_fun : mm.mm2_step_fun Prog (mm2_iter Prog n (1%nat, (y, 0%nat))) = None).
{ unfold mm2_haltedAt in Ehalt.
  destruct (mm.mm2_step_fun Prog (mm2_iter Prog n (1%nat, (y, 0%nat))));
    [discriminate | reflexivity]. }
assert (Hstop : mm2_stop Prog (mm2_iter Prog n (1%nat, (y, 0%nat))))
  by exact (mm2_stop_of_step_fun_none _ _ Hstop_fun).
destruct (mm2_state_eqb (mm2_iter Prog n (1%nat, (y, 0%nat))) (0, (0, 0))) eqn:Eeq.
- apply mm2_state_eqb_true in Eeq.
  assert (Hv : v = 1%nat) by congruence.
  subst v.
  split; [intros _; reflexivity | intros _].
  apply mm2_R_completeness'. rewrite Eeq in Hrtc. exact Hrtc.
- assert (Hv : v = 0%nat) by congruence.
  subst v.
  split.
  + intros Hle. exfalso.
    pose proof (mm2_R_soundness' Hrtc Hstop Hle) as Heq.
    assert (Eeq' : mm2_state_eqb (mm2_iter Prog n (1%nat, (y, 0%nat))) (0, (0, 0)) = true)
      by (apply mm2_state_eqb_true; exact Heq).
    rewrite Eeq' in Eeq. discriminate.
  + discriminate.
Qed.

(* --- GENUINE OPEN GAP, discovered while trying to close this, not a
   Coq-mechanics issue: R_target_iff_outcome'/R_target_iff_outcome
   only characterize red_leq/red_leq' CONDITIONALLY on Theta_ours_MM2
   c y actually having a value (i.e. the underlying MM2 execution
   halting within some finite step bound n). They say nothing about
   the case where the execution diverges forever.

   This matters because mm2_R_soundness_aux's own conclusion (s2 =
   (0,(0,0)) \/ 0 < s2.1 <= length Prog, for EVERY s2 reached via rtc,
   not just a halted one) is satisfiable by a NEVER-HALTING run: the
   "in bounds" disjunct only constrains the program-counter component
   of the state (0 < index <= n), not the two counters, so a program
   that loops forever incrementing a counter while staying in bounds
   satisfies red_leq without ever halting. mm.v has no
   "mm2_R_completeness_aux"-style lemma covering this general
   (possibly-infinite) case -- mm2_R_completeness only ever proves
   completeness for the SPECIFIC halt-at-(0,0) case, matching how it's
   actually used elsewhere in this project (R_target_iff_outcome
   itself is only ever invoked WITH a Theta_ours_MM2 witness in hand,
   e.g. for A0_MM2/B1_MM2, never unconditionally).

   Consequently: K c z <-> KA_ineq_bin(...) -- a genuine many-one
   reduction, needed for EVERY z, including ones where the underlying
   program diverges -- does not follow from what mm.v/this file
   provide. Closing it would need a new completeness lemma
   characterizing red_leq (and red_leq') for divergent runs too, which
   is new mathematical content, not a restatement of existing pieces.
   Left unaddressed here; flagged for Jeremy rather than guessed past. *)

End WithEncoding.

End BinaryAlphabet.
