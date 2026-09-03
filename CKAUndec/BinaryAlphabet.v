(* CKA-specific wiring closing the canonical-alphabet requirement for
   real: applies BoundedOutputTransport.v's machinery to Encoding.v's
   own mm2_R/T (the transition relation and configuration set for a
   fixed program Prog := progOf c), and re-runs Encoding.v's own
   soundness/completeness argument (mm2_R_completeness/mm2_R_soundness)
   at the embedded level to get order-REFLECTION for red_lb/red_ub --
   having a repr_rel for the embedded term alone is not enough; showing
   m-completeness over the CANONICAL 2-symbol alphabet needs reflection
   (Embed_pair(red_lb) ⊑ Embed_pair(red_ub) -> red_lb ⊑ red_ub), not
   just preservation (the free direction).

   bounded_output_repr_rel' (KA/bounded_output.v) already handles all
   the pad_rel/pad_lang lifting internally (finite_state_pad_rel,
   bounded_output_pad_rel, pad_rel_pad_lang_1/2, prefix_free_pad_lang),
   so no separate "primed" version of repr_rel_via_bounded_output is
   needed: this file embeds mm2_R/T at the unpadded mm_sym QF level
   directly (reusing BoundedOutputTransport.v's transport lemmas, which
   are generic over any finite alphabet), then hands the embedded,
   still-unpadded terms straight to bounded_output_repr_rel' -- exactly
   mirroring how Encoding.v itself builds repr_rel_mm2_R.

   This is what closes the source paper's actual Theorem 18/19 over the
   canonical 2-symbol alphabet, not just Encoding.v's machine-specific
   alphabet. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia Bool.
Require Import ssreflect.
From stdpp Require Import base list finite relations.
From kacc Require Import KA.utils KA.algebra KA.pre_ka KA.lang KA.automata
  KA.repr_rel KA.bounded_output.
From kacc Require Import KA.BinaryAlphabetTransport KA.BoundedOutputTransport.
From Undecidability.MinskyMachines Require Import MM2.
Require Import SyntheticComputability.Shared.partial.
Require kacc.CKAUndec.Encoding.
From Undecidability.MinskyMachines.Util Require Import MM2_facts MM2_stepper MM2_embed_nat MM2_simulator.
From kacc Require Import MM2.Simulator MM2.RtcBridge.
From kacc Require Import CKAUndec.Glue.MM2ToKATerm.
From kacc Require Import CKAUndec.K CKAUndec.KEnumerable.

Section BinaryAlphabet.

Variable c : nat.
Notation Prog := (progOf c).
Let QF : Type := fin (S (S (length Prog))).

Instance QF_eqdec' : EqDecision QF.
Proof. apply _. Defined.

Instance QF_finite' : Finite QF.
Proof. apply _. Defined.

(* The source alphabet for the embedding: Encoding.v's own mm_sym QF, exactly
   as it appears (unpadded) in mm2_R/T/C. *)

Notation TAlph := (@Encoding.mm_sym_setoid QF).

Lemma binary_encoding_exists :
  ∃ (k : nat) (enc : Encoding.mm_sym QF → list bool),
    (∀ x y, enc x = enc y → x = y) ∧ (∀ x, length (enc x) = k) ∧ 0 < k.
Proof.
have [k [enc [Henc Hlen]]] := finite_binary_encoding TAlph.
exists k, enc; do 2 (split; first done).
destruct k as [|k]; last lia.
exfalso.
have Ha : enc (@Encoding.mm_a QF) = [] by apply/length_zero_iff_nil; exact: Hlen.
have Hb : enc (@Encoding.mm_b QF) = [] by apply/length_zero_iff_nil; exact: Hlen.
have Eab : enc (@Encoding.mm_a QF) = enc (@Encoding.mm_b QF) by rewrite Ha Hb.
have := Henc _ _ Eab.
discriminate.
Qed.

Section WithEncoding.

Context (k : nat) (enc : setoid_car (@Encoding.mm_sym_setoid QF) → list bool).
Context (Henc : ∀ x y, enc x = enc y → x = y).
Context (Hlen : ∀ x, length (enc x) = k).
Context (Hk_pos : 0 < k).

Instance enc_inj : Inj (=) (=) enc.
Proof. exact: Henc. Qed.

(* mm2_R's type is the bare product `list (mm_sym QF) * list (mm_sym QF)`,
   which does not syntactically unify with `monoid_car ?T` during
   typeclass search without help (same issue flagged in
   CKAUndec.Glue.MM2ToKATerm.v's own comment on red_leq) -- name the
   monoid explicitly, mirroring CKAUndec.KEnumerable.v's TmMonoid but WITHOUT
   the option-padding (mm2_R itself is unpadded). *)
Definition Mm2RMonoid : monoid :=
  prod_monoid (list_monoid (@Encoding.mm_sym_setoid QF))
              (list_monoid (@Encoding.mm_sym_setoid QF)).

(* finite_stateb_join_list (the boolean analogue of automata.v's
   finite_state_join_list, needed since BoundedOutputTransport.v's
   finite_stateb_transport operates on the syntactic finite_stateb
   check, not the abstract finite_state notion Encoding.v itself uses to
   establish finite_state (mm2_R Prog)) now lives in automata.v itself
   -- it is generic over any finite alphabet, not tied to mm2_R/CKA at
   all. bounded_output, by contrast, is transported abstractly
   (bounded_output_transport takes the abstract Sigma-type witness
   directly), so bounded_output_join_list (already generic,
   bounded_output.v:94-101) is reused as-is below with no boolean
   intermediate needed. *)

Lemma finite_stateb_mm2_R : @finite_stateb Mm2RMonoid _ (Encoding.mm2_R Prog) = true.
Proof.
apply: finite_stateb_join_list => q Hq.
by case: (Encoding.mm2_prog q).
Qed.

Lemma bounded_output_mm2_R : bounded_output (T := @Encoding.mm_sym_setoid QF) (Encoding.mm2_R Prog).
Proof.
apply: bounded_output_join_list => q Hq.
by case: (Encoding.mm2_prog q) => *; apply: bounded_outputbP.
Qed.

Lemma repr_rel_embedded :
  repr_rel (pad_rel (Embed_pair enc (Encoding.mm2_R Prog)))
           (pad_lang (Embed_word enc (Encoding.T Prog))).
Proof.
apply: bounded_output_repr_rel'.
- apply: finite_stateP.
  + done.
  + rewrite -(finite_stateb_transport (@Encoding.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
    apply/Is_true_true. exact: finite_stateb_mm2_R.
- exact: bounded_output_transport bounded_output_mm2_R.
- rewrite Embed_proj1_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: Encoding.mm2_R_ub1' Prog.
- rewrite Embed_proj2_natural. apply: semi_lattice_morphism_sqsubseteq_proper.
  exact: Encoding.mm2_R_ub2 Prog.
Qed.

(* --- Re-running Encoding.v's own soundness/completeness argument at the
   embedded level, using repr_rel_embedded as the witness, mirroring
   mm2_R_completeness/mm2_R_soundness (Encoding.v:1391-1410,1365-1374)
   exactly -- the generic lemmas they build on (repr_rel_iter_final,
   repr_rel_rtc_soundness') take an arbitrary repr_rel witness, so
   nothing about their OWN proofs needs re-deriving, only the
   surrounding argument (pushing rtc/determinism/no-step-from-halt
   through the embedding) needs restating. *)

Lemma step_embed (x y : list (setoid_car (@Encoding.mm_sym_setoid QF))) :
  Unit (x, y) ⊑ Encoding.mm2_R Prog →
  Unit (enc_word enc x, enc_word enc y) ⊑ Embed_pair enc (Encoding.mm2_R Prog).
Proof.
move=> Hxy.
have -> : Unit (enc_word enc x, enc_word enc y)
        = Embed_pair enc (Unit (x, y)) by [].
apply: semi_lattice_morphism_sqsubseteq_proper. exact: Hxy.
Qed.

Lemma rtc_embed (x y : list (setoid_car (@Encoding.mm_sym_setoid QF))) :
  rtc (λ xs ys : list (setoid_car (@Encoding.mm_sym_setoid QF)),
        Unit (xs, ys) ⊑ Encoding.mm2_R Prog) x y →
  rtc (λ xs ys, Unit (xs, ys) ⊑ Embed_pair enc (Encoding.mm2_R Prog))
    (enc_word enc x) (enc_word enc y).
Proof.
elim=> // x0 y0 z0 xy0 _ IH.
apply: rtc_l IH. exact: step_embed xy0.
Qed.

Lemma mm2_R_completeness' (s1 : nat * (nat * nat)) :
  rtc (mm2_step Prog) s1 (0, (0, 0)) →
  Unit (1, (Some <$> enc_word enc (Encoding.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (Encoding.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (Encoding.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded.
Proof.
move=> /Encoding.encoding_rtc_complete /rtc_embed xs_ys.
change (Unit (1, (Some <$> enc_word enc (Encoding.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (Encoding.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2
      (pad_lang (Embed_word enc (Encoding.C Prog)
                   ⊔ Unit (enc_word enc (Encoding.mm2_config Prog (0, (0, 0))))))
    ⊔ repr_rel_rtc_error repr_rel_embedded).
rewrite pad_lang_join.
have -> : pad_lang (Unit (enc_word enc (Encoding.mm2_config Prog (0, (0, 0)))))
        ≡ Unit ((Some <$> enc_word enc (Encoding.mm2_config Prog (0, (0, 0)))) ⋅ [None]).
{ by rewrite /pad_lang /ka_term_map /repr_rel.lift /=
    (monoid_morphism_mul (f := Unit)). }
apply: repr_rel_iter_final xs_ys.
- have := Encoding.elem_of_T Prog s1.
  have -> : Unit (enc_word enc (Encoding.mm2_config Prog s1))
          = Embed_word enc (Unit (Encoding.mm2_config Prog s1)) by [].
  apply: semi_lattice_morphism_sqsubseteq_proper.
- rewrite Embed_proj1_natural.
  apply: semi_lattice_morphism_sqsubseteq_proper. exact: Encoding.mm2_R_ub1 Prog.
- move=> xs ys1 ys2 xs_ys1 xs_ys2.
  have [x1 [y1 [Ex1 [Ey1 Hin1]]]] :=
    Embed_pair_inv (@Encoding.mm_sym_setoid QF) bool_setoid enc (Encoding.mm2_R Prog) xs ys1 xs_ys1.
  have [x2 [y2 [Ex2 [Ey2 Hin2]]]] :=
    Embed_pair_inv (@Encoding.mm_sym_setoid QF) bool_setoid enc (Encoding.mm2_R Prog) xs ys2 xs_ys2.
  have Ex : x1 = x2.
  { apply: (enc_word_inj (@Encoding.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
    rewrite -Ex1 -Ex2. done. }
  subst x2.
  have Hpx1 : Unit x1
      ⊑ @ka_term_proj1 (list_monoid TAlph) (list_monoid TAlph) (Encoding.mm2_R Prog)
    by rewrite -Hin1.
  rewrite (Encoding.mm2_R_ub1 Prog) (Encoding.C_T Prog) in Hpx1.
  case/Encoding.elem_of_T_inv: Hpx1 => s x1_s.
  rewrite x1_s in Hin1 Hin2.
  case/Encoding.encoding_sound: Hin1 => s1' [] y1_s1' s_s1'.
  case/Encoding.encoding_sound: Hin2 => s2' [] y2_s2' s_s2'.
  have Es : s1' = s2' by exact: MM2_facts.mm2_step_det s_s1' s_s2'.
  by rewrite Ey1 Ey2 y1_s1' y2_s2' Es.
- move=> ys' Hys'.
  have [x0 [y0 [Ex0 [Ey0 Hin0]]]] :=
    Embed_pair_inv (@Encoding.mm_sym_setoid QF) bool_setoid enc (Encoding.mm2_R Prog) _ _ Hys'.
  have Ex0' : Encoding.mm2_config Prog (0, (0, 0)) = x0.
  { apply: (enc_word_inj (@Encoding.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
    exact: Ex0. }
  rewrite -Ex0' in Hin0.
  exact: Encoding.no_step_from_halt Hin0.
Qed.

Lemma mm2_R_soundness_aux' (s1 s2 : nat * (nat * nat)) :
  rtc (mm2_step Prog) s1 s2 →
  Unit (1, (Some <$> enc_word enc (Encoding.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (Encoding.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (Encoding.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded →
  s2 = (0, (0, 0)) ∨ 0 < s2.1 ≤ length Prog.
Proof.
move=> /Encoding.encoding_rtc_complete /rtc_embed s1_s2.
rewrite /repr_rel_rtc_error -assoc => ub.
have pa : Unit (enc_word enc (Encoding.mm2_config Prog s2))
        ⊑ Embed_word enc (Encoding.partially_accepted Prog).
{ exact: repr_rel_rtc_soundness' s1_s2 ub. }
have [w [Ew Hw]] :=
  Embed_word_inv (@Encoding.mm_sym_setoid QF) bool_setoid enc
    (Encoding.partially_accepted Prog) _ pa.
have Ew' : Encoding.mm2_config Prog s2 = w.
{ apply: (enc_word_inj (@Encoding.mm_sym_setoid QF) bool_setoid enc k Hlen Hk_pos).
  exact: Ew. }
have pa0 : @sqsubseteq (ka_term (list TAlph)) _
             (Unit (Encoding.mm2_config Prog s2)) (Encoding.partially_accepted Prog).
{ rewrite Ew'. exact: Hw. }
have pa1 : @sqsubseteq (ka_term (list TAlph)) _
             (Unit (Encoding.mm2_config Prog s2)) (Encoding.C Prog)
         ∨ Encoding.mm2_config Prog s2 = Encoding.mm2_config Prog (0, (0, 0)).
{ move: pa0 => /l_alt.
  rewrite /Encoding.partially_accepted semi_lattice_morphism_join.
  case=> H.
  - left. apply/l_alt. exact: H.
  - right. move: H => /= H. exact: (proj1 (leibniz_equiv_iff _ _) H). }
case: pa1 => pa1.
- right. apply/Encoding.elem_of_C. exact: pa1.
- left.
  move: pa1.
  clear s1_s2 ub pa Ew Hw Ew' pa0.
  rewrite /Encoding.mm2_config /Encoding.config_word /=.
  by case: s2 => [[|?] [[|?] [|?]]] //=.
Qed.

Lemma mm2_R_soundness' (s1 s2 : nat * (nat * nat)) :
  rtc (mm2_step Prog) s1 s2 →
  mm2_stop Prog s2 →
  Unit (1, (Some <$> enc_word enc (Encoding.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (Encoding.mm2_R Prog)))
  ⊑ dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (Encoding.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded →
  s2 = (0, (0, 0)).
Proof.
move=> s1_s2 s2_stop red_leq.
have [//|Hbad] := mm2_R_soundness_aux' s1_s2 red_leq.
exfalso; move/MM2_facts.mm2_stop_index_iff: s2_stop; lia.
Qed.

(* --- Final step: mirror R_target_iff_outcome
   (CKAUndec.Glue.MM2ToKATerm.v:289-320) at the embedded level,
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

(* Named left/right sides of red_leq', added purely so later files
   (CKAUndec.BinaryAlphabetMComplete.v) have explicit KA-terms to hand to the
   generic enumerability machinery (ka_sqsubseteq_enumerable) -- red_leq'
   itself is kept as-is (Ltac-extracted) to avoid touching anything
   that already builds on it. red_leq'_shape confirms the two agree,
   by reflexivity: this is a naming convenience, not a new fact. *)

Definition red_lb' (s1 : nat * (nat * nat)) :=
  Unit (1, (Some <$> enc_word enc (Encoding.mm2_config Prog s1)) ⋅ [None])
    ⋅ star (pad_rel (Embed_pair enc (Encoding.mm2_R Prog))).

Definition red_ub' :=
  dpseudo_top ⋅ ka_term_inj2 (pad_lang (Embed_word enc (Encoding.partially_accepted Prog)))
    ⊔ repr_rel_rtc_error repr_rel_embedded.

Lemma red_leq'_shape (s1 : nat * (nat * nat)) :
  red_leq' s1 <-> red_lb' s1 ⊑ red_ub'.
Proof. reflexivity. Qed.

Lemma R_target_iff_outcome' y v :
  Θ_MM2 c y =! v -> (red_leq' (1%nat, (y, 0%nat)) ↔ v = 1%nat).
Proof.
intros [n Hn] % seval_hasvalue.
rewrite seval_Theta_MM2 in Hn.
unfold red_leq'.
assert (Hrtc : rtc (mm2_step Prog) (1%nat, (y, 0%nat)) (mm2_iter Prog n (1%nat, (y, 0%nat))))
  by (apply crt_to_rtc; apply mm2_iter_rtc).
unfold mm2_outcome_at in Hn.
destruct (mm2_haltedAt Prog n (1%nat, (y, 0%nat))) eqn:Ehalt; [| discriminate].
assert (Hstop_fun : mm2_step_fun Prog (mm2_iter Prog n (1%nat, (y, 0%nat))) = None).
{ unfold mm2_haltedAt in Ehalt.
  destruct (mm2_step_fun Prog (mm2_iter Prog n (1%nat, (y, 0%nat))));
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

(* --- GENUINE OPEN GAP, now traced to the SAME root cause as
   BinaryAlphabetTransport.v's dpseudo_top_mismatch_transport gap
   (star-monotonicity), not a separate, unrelated issue.

   Restated precisely: elem_of_C (Encoding.v:504) gives Unit(config s) ⊑ C
   <-> 0 < s.1 <= n, i.e. C's membership is exactly "not yet halted",
   so partially_accepted = C ⊔ Unit(config(0,0,0)) means:

     Unit(config s2) ⊑ partially_accepted  <->  ¬mm2_stop s2 ∨ s2=(0,0,0)

   i.e. "s2 is not a WRONG halt". So red_lb s1 ⊑ red_ub (via
   mm2_R_soundness_aux's proof, which is already fully general -- it
   places no halting assumption on s2) is EQUIVALENT in spirit to "the
   run from s1 never halts anywhere except (0,(0,0))" -- true both
   when it halts correctly AND when it diverges forever, false only
   for a wrong halt. Divergence is therefore not a hypothetical edge
   case to worry about -- it is a real, common case the completeness
   direction must handle for K c z <-> KA_ineq_bin(...) to be a valid
   total many-one reduction (m-reductions must be correct for every
   z, and by construction z's underlying Theta_ours_MM2 run genuinely
   can diverge -- if it couldn't, K would be decidable).

   Attempted concretely (not just reasoned abstractly): the only
   existing machinery for proving a Unit(x) ⋅ star(e) ⊑ Z fact is
   repr_rel_iter_final / repr_rel_iter_empty' (repr_rel.v:815,798),
   and BOTH require an explicit, already-known finite witness baked
   into their own statement -- a terminal state `ys` with a proof
   no step leaves it (_final), or a search depth `n` with
   next_iter n [...] = [] (_empty'). Encoding.v's own mm2_R_completeness
   supplies this witness via the GIVEN halting path's own length
   (rtc_nsteps s1 (0,0,0) gives a concrete n). For a divergent run
   there is no such n or ys to supply -- confirmed by directly trying
   `apply: (repr_rel_iter_empty' xs_L)` against the general goal,
   which fails to unify (its conclusion is inherently n-parameterized,
   whereas red_ub is a fixed closed term; Encoding.v's own proof bridges
   this ONLY by simplifying against the known n, which isn't available
   here). This is exactly the shape of gap that needs Kleene algebra's
   standard star-INDUCTION rule (x ⊔ e⋅z ⊑ z -> x⋅star(e) ⊑ z), which
   pre_ka.v's PreKAMixin (pre_ka.v:21-30) deliberately does not
   axiomatize -- only the unfold equation and Properness w.r.t. ≡ are
   given, no induction/least-fixpoint/monotonicity rule. Same missing
   ingredient as route 2's star-monotonicity wall, arising here
   through the completeness direction instead of algebraic transport.

   Consequently: K c z <-> KA_ineq_bin(...), needed for EVERY z
   including divergent ones, does not follow from what Encoding.v/this file
   provide, and cannot be derived from the existing pre-KA axioms as
   given -- closing it would require either (a) adding a star-
   induction axiom to pre_ka.v itself (a framework-level change,
   whose soundness against this project's own intended semantics
   would need separate justification), or (b) a genuinely different
   argument not going through red_lb/red_ub's star structure at all.
   Left unaddressed here; flagged as a real open mathematical question,
   not guessed past. *)

End WithEncoding.

End BinaryAlphabet.
