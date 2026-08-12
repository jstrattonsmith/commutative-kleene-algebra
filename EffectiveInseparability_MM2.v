(* Native effective inseparability over MM2 program codes, mirroring
   coq-synthetic-computability's Models/EffectiveInseparability_L.v but built
   directly over two-counter machines instead of L. MM2 programs are simple
   first-order data (a 4-constructor instruction type + list), so nat<->
   program decoding is concrete, structural data -- no self-interpretation
   wall here.

   The nat<->list mm2_instr encoding below is deliberately hand-rolled via
   embed/unembed (Cantor pairing) rather than stdpp's generic Countable
   machinery: an earlier version used stdpp's Countable (via a sum-type
   injection + the free list_countable instance), which is fine for the
   axiom-free machine-relative approach, but does NOT extract to L (L's
   `extract` tactic needs every function/type involved to be built from
   L.Datatypes-registered primitives, and stdpp's positive-based Countable
   internals aren't part of that registry -- confirmed by direct probing:
   `computable progOf` fails to find a `TT` instance). This version *does*
   extract (see the "L-extractability" section at the end of this file),
   which is what the CT_L-based route (Undecidability/ka_eq_undecidable_CT.v)
   needs: Theta_ours_MM2/mm2_outcome_at must be realizable as an actual
   L-term so the eff-insep diagonal argument can be built natively in L
   (reusing SMN_for T_L + LMuRecursion.mu, exactly as
   EffectiveInseparability_L.v already does) instead of needing a hand-rolled
   MM2-level register-packing racer or an output-preserving MM-to-MM2
   compiler. *)

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import Lia.
(* `Require` only (not `Import`) for stdpp's `relations`: it and
   Datatypes.LNat (needed later, for L-extraction) both declare a `↑`
   notation at incompatible levels, and whichever gets `Import`ed second
   errors out ("already defined ... while it is now required to be at a
   different level") rather than merely shadowing -- reordering doesn't
   help, since it's the *later* Import that always loses. Referring to
   `rtc` via the qualified `relations.rtc` below sidesteps the clash
   entirely, since Require alone never touches notation scope. *)
From stdpp Require relations.
From Undecidability.MinskyMachines Require Import MM2.
Import MM2Notations.

From kacc.MM2 Require Import Stepper.
From kacc Require Import mm.

Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
(* Only for enum_iff (a plain enumerable <-> semi_decidable fact) -- not for
   the EA typeclass itself, so no axiom dependency is introduced here. *)
Require Import SyntheticComputability.Axioms.EA.

(* --- 0. nat <-> list mm2_instr, via a hand-rolled embed-based encoding -- *)

Definition instr_to_nat (i : mm2_instr) : nat :=
  match i with
  | mm2_inc_a => embed (0, 0)
  | mm2_inc_b => embed (1, 0)
  | mm2_dec_a j => embed (2, j)
  | mm2_dec_b j => embed (3, j)
  end.

Definition nat_to_instr (n : nat) : mm2_instr :=
  match unembed n with
  | (0, _) => mm2_inc_a
  | (1, _) => mm2_inc_b
  | (2, j) => mm2_dec_a j
  | (3, j) => mm2_dec_b j
  | (_, _) => mm2_inc_a
  end.

Lemma nat_to_instr_to_nat i : nat_to_instr (instr_to_nat i) = i.
Proof. destruct i; unfold nat_to_instr, instr_to_nat; now rewrite embedP. Qed.

(* `nil`/`cons` used explicitly (not the `[]`/`::` notations): those
   notations come from different, mutually-conflicting sources across
   stdpp and coq-library-undecidability (both declare a clashing `↑`
   notation at incompatible levels somewhere in their respective transitive
   closures, and whichever module actually supplies `[]` pulls that fight
   in too) -- spelling the constructors out avoids the whole mess. *)
Fixpoint list_to_nat (l : list mm2_instr) : nat :=
  match l with
  | nil => 0
  | cons i l' => S (embed (instr_to_nat i, list_to_nat l'))
  end.

Fixpoint nat_to_list (fuel n : nat) : list mm2_instr :=
  match fuel, n with
  | S fuel', S n' => let '(a, b) := unembed n' in cons (nat_to_instr a) (nat_to_list fuel' b)
  | _, _ => nil
  end.

Lemma embed_ge_snd x y : embed (x, y) >= y.
Proof. unfold embed. lia. Qed.

Lemma nat_to_list_list_to_nat_fuel (P : list mm2_instr) (fuel : nat) :
  list_to_nat P <= fuel -> nat_to_list fuel (list_to_nat P) = P.
Proof.
induction P as [| i P IH] in fuel |- *; intros Hfuel.
- destruct fuel; reflexivity.
- cbn [list_to_nat] in Hfuel |- *. destruct fuel as [| fuel']; [lia |].
  cbn [nat_to_list]. rewrite embedP.
  rewrite nat_to_instr_to_nat. f_equal.
  apply IH. pose proof (embed_ge_snd (instr_to_nat i) (list_to_nat P)). lia.
Qed.

Definition progOf (c : nat) : list mm2_instr := nat_to_list c c.

Definition codeOf (P : list mm2_instr) : nat := list_to_nat P.

Lemma progOf_codeOf P : progOf (codeOf P) = P.
Proof. unfold progOf, codeOf. apply nat_to_list_list_to_nat_fuel. lia. Qed.

(* Deliberately NOT `Import partial.implementation`: it pulls the *concrete*
   part/seval/hasvalue/mu into unqualified scope, shadowing the abstract
   class-projection versions used throughout the rest of this file (the same
   gotcha noted in EffectiveInseparability_L.v). Register the instance via a
   qualified reference instead. *)
Global Existing Instance SyntheticComputability.Shared.partial.implementation.monotonic_functions.

(* --- 1. step-indexed MM2 evaluator, monotone by construction ----------- *)

Definition mm2_step_total (P : list mm2_instr) (s : mm2_state) : mm2_state :=
  match mm2_step_fun P s with Some s' => s' | None => s end.

Definition mm2_iter (P : list mm2_instr) (n : nat) (s0 : mm2_state) : mm2_state :=
  Nat.iter n (mm2_step_total P) s0.

Definition mm2_haltedAt (P : list mm2_instr) (n : nat) (s0 : mm2_state) : bool :=
  match mm2_step_fun P (mm2_iter P n s0) with Some _ => false | None => true end.

Lemma mm2_iter_S P n s0 : mm2_iter P (S n) s0 = mm2_step_total P (mm2_iter P n s0).
Proof. reflexivity. Qed.

Lemma mm2_iter_frozen P n s0 :
  mm2_step_fun P (mm2_iter P n s0) = None ->
  forall k, mm2_iter P (n + k) s0 = mm2_iter P n s0.
Proof.
  intros Hstop k. induction k as [|k IH].
  - now rewrite PeanoNat.Nat.add_0_r.
  - rewrite PeanoNat.Nat.add_succ_r, mm2_iter_S, IH.
    unfold mm2_step_total. now rewrite Hstop.
Qed.

Lemma mm2_haltedAt_mono P s0 : monotonic (fun n => if mm2_haltedAt P n s0 then Some tt else None).
Proof.
  intros n1 [] Hn1 n2 Hle.
  unfold mm2_haltedAt in *.
  destruct (mm2_step_fun P (mm2_iter P n1 s0)) as [s'|] eqn:E; [discriminate |].
  assert (Hk : exists k, n2 = n1 + k) by (exists (n2 - n1); lia).
  destruct Hk as [k ->].
  rewrite (mm2_iter_frozen P n1 s0 E k).
  now rewrite E.
Qed.

Definition mm2_state_eqb (s1 s2 : mm2_state) : bool :=
  match s1, s2 with
  | (i1,(a1,b1)), (i2,(a2,b2)) => (Nat.eqb i1 i2 && Nat.eqb a1 a2 && Nat.eqb b1 b2)%bool
  end.

Definition mm2_outcome_at (c y n : nat) : option nat :=
  if mm2_haltedAt (progOf c) n (1,(y,0))
  then Some (if mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0)) then 1 else 0)
  else None.

Lemma monotonic_mm2_outcome_at c y : monotonic (mm2_outcome_at c y).
Proof.
  intros n1 v Hn1 n2 Hle.
  unfold mm2_outcome_at in *.
  destruct (mm2_haltedAt (progOf c) n1 (1,(y,0))) eqn:E1; [| discriminate].
  pose proof (mm2_haltedAt_mono (progOf c) (1,(y,0)) n1 tt) as Hmono.
  cbn in Hmono.
  rewrite E1 in Hmono.
  specialize (Hmono eq_refl n2 Hle).
  destruct (mm2_haltedAt (progOf c) n2 (1,(y,0))) eqn:E2; [| discriminate].
  assert (Hk : exists k, n2 = n1 + k) by (exists (n2 - n1); lia).
  destruct Hk as [k ->].
  assert (Hstop : mm2_step_fun (progOf c) (mm2_iter (progOf c) n1 (1,(y,0))) = None).
  { unfold mm2_haltedAt in E1.
    destruct (mm2_step_fun (progOf c) (mm2_iter (progOf c) n1 (1,(y,0)))); [discriminate|reflexivity]. }
  rewrite (mm2_iter_frozen (progOf c) n1 (1,(y,0)) Hstop k).
  exact Hn1.
Qed.

Definition Θ_ours_MM2 (c y : nat) : part nat :=
  partial.implementation.Build_part (monotonic_mm2_outcome_at c y).

Definition W_MM2 (c y : nat) : Prop := exists n, mm2_haltedAt (progOf c) n (1,(y,0)) = true.

Definition semidec_of_MM2 (c y n : nat) : bool := mm2_haltedAt (progOf c) n (1,(y,0)).

Lemma semidec_of_MM2_spec c : semi_decider (semidec_of_MM2 c) (W_MM2 c).
Proof. intros y. unfold semidec_of_MM2, W_MM2. tauto. Qed.

Definition A0_MM2 (z : nat) : Prop := Θ_ours_MM2 (fst (unembed z)) (snd (unembed z)) =! 1.
Definition B1_MM2 (z : nat) : Prop := Θ_ours_MM2 (fst (unembed z)) (snd (unembed z)) =! 0.

Lemma A0_MM2_enumerable : enumerable A0_MM2.
Proof.
apply (proj2 (enum_iff A0_MM2)).
exists (fun z n =>
  match (partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n) with
  | Some v => Nat.eqb v 1
  | None => false
  end).
intros z. unfold A0_MM2. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct ((partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n)) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Lemma B1_MM2_enumerable : enumerable B1_MM2.
Proof.
apply (proj2 (enum_iff B1_MM2)).
exists (fun z n =>
  match (partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n) with
  | Some v => Nat.eqb v 0
  | None => false
  end).
intros z. unfold B1_MM2. split.
- intros [n Hn] % seval_hasvalue.
  exists n. cbv beta. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- cbv beta. intros [n Hn].
  destruct ((partial.seval (Θ_ours_MM2 (fst (unembed z)) (snd (unembed z))) n)) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

(* --- 2. Bridging to mm.v's soundness/completeness ----------------------
   R_target c y is the KA-term inequality mm.v attaches to running the
   program coded by c from register state (y,0) -- a per-program
   *dependent* Prop (red_lb/red_ub's own KA-term type depends on P via
   Q := fin (S (S (length P))), so there is no single common `ka_term`
   type to state this over; each c simply routes through its own type
   internally, which is fine since the end result is just a Prop). This
   bridging lemma itself needs no axiom -- it is a straightforward
   consequence of mm.v's mm2_R_soundness/mm2_R_completeness, applicable
   regardless of which route (axiom-free machine-relative, or CT_L-based
   absolute) is used to finish the undecidability argument. *)

(* Writing `red_lb P s1 ⊑ red_ub P` directly here (fresh notation
   elaboration) fails: Coq's ⊑ instance search needs to recognize the
   product generator type as `monoid_car (prod_monoid M1 M2)`, but
   red_lb's/red_ub's own generator-type expressions unfold their two
   factors to different (definitionally equal, syntactically distinct)
   normal forms, and typeclass-search-time unification (unlike ordinary
   conversion checking) doesn't chase that Canonical Structure chain
   through the mismatch. Fix: extract the *already-elaborated* Prop
   directly from mm2_R_completeness's own stored type via Ltac reflection,
   instead of re-stating it via the ⊑ notation ourselves -- this performs
   no fresh instance search at all. *)
Definition red_leq (P : list mm2_instr) (s1 : mm2_state) : Prop :=
  ltac:(let t := type of (@mm2_R_completeness P s1) in
        match t with _ -> ?B => exact B end).

Definition R_target (c y : nat) : Prop := red_leq (progOf c) (1,(y,0)).

Lemma mm2_iter_rtc P n s0 : relations.rtc (mm2_step P) s0 (mm2_iter P n s0).
Proof.
induction n as [|n IH].
- apply relations.rtc_refl.
- rewrite mm2_iter_S. unfold mm2_step_total.
  destruct (mm2_step_fun P (mm2_iter P n s0)) as [s'|] eqn:E.
  + eapply relations.rtc_r; [exact IH |]. apply mm2_step_fun_spec. exact E.
  + exact IH.
Qed.

Lemma mm2_stop_of_step_fun_none P s :
  mm2_step_fun P s = None -> mm2_stop P s.
Proof.
intros H s' Hstep. apply mm2_step_fun_spec in Hstep. congruence.
Qed.

Lemma mm2_state_eqb_true s1 s2 : mm2_state_eqb s1 s2 = true <-> s1 = s2.
Proof.
destruct s1 as [i1 [a1 b1]], s2 as [i2 [a2 b2]]. unfold mm2_state_eqb.
rewrite !Bool.andb_true_iff, !PeanoNat.Nat.eqb_eq.
split.
- intros [[-> ->] ->]. reflexivity.
- intros [= -> -> ->]. auto.
Qed.

Lemma seval_Theta_ours_MM2 c y n :
  partial.seval (Θ_ours_MM2 c y) n = mm2_outcome_at c y n.
Proof. reflexivity. Qed.

Lemma R_target_iff_outcome c y v :
  Θ_ours_MM2 c y =! v -> (R_target c y <-> v = 1).
Proof.
intros [n Hn] % seval_hasvalue.
rewrite seval_Theta_ours_MM2 in Hn.
unfold R_target.
assert (Hrtc : relations.rtc (mm2_step (progOf c)) (1,(y,0)) (mm2_iter (progOf c) n (1,(y,0))))
  by apply mm2_iter_rtc.
unfold mm2_outcome_at in Hn.
destruct (mm2_haltedAt (progOf c) n (1,(y,0))) eqn:Ehalt; [| discriminate].
assert (Hstop_fun : mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1,(y,0))) = None).
{ unfold mm2_haltedAt in Ehalt.
  destruct (mm2_step_fun (progOf c) (mm2_iter (progOf c) n (1,(y,0))));
    [discriminate | reflexivity]. }
assert (Hstop : mm2_stop (progOf c) (mm2_iter (progOf c) n (1,(y,0))))
  by exact (mm2_stop_of_step_fun_none _ _ Hstop_fun).
destruct (mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0))) eqn:Eeq.
- apply mm2_state_eqb_true in Eeq.
  assert (Hv : v = 1) by congruence.
  subst v.
  split; [intros _; reflexivity | intros _].
  apply mm2_R_completeness. rewrite Eeq in Hrtc. exact Hrtc.
- assert (Hv : v = 0) by congruence.
  subst v.
  split.
  + intros Hle. exfalso.
    pose proof (mm2_R_soundness Hrtc Hstop Hle) as Heq.
    assert (Eeq' : mm2_state_eqb (mm2_iter (progOf c) n (1,(y,0))) (0,(0,0)) = true)
      by (apply mm2_state_eqb_true; exact Heq).
    rewrite Eeq' in Eeq. discriminate.
  + discriminate.
Qed.

(* --- 3. L-extractability of mm2_outcome_at -----------------------------
   This is the piece the CT_L-based route needs: mm2_outcome_at (built
   entirely from plain structurally-recursive Gallina functions -- no
   opaque parts) extracts to an actual L-term, via Undecidability.L's
   `extract` tactic. This lets the eff-insep diagonal/race construction be
   built *natively in L* (reusing SMN_for T_L + LMuRecursion.mu, exactly as
   EffectiveInseparability_L.v already does for T_L itself) instead of
   needing a hand-rolled MM2-level register-packing racer.

   Gotcha, confirmed by direct probing: `Require Import Undecidability.L.L.`
   (the convenience mega-import) breaks `extract` for several of the
   lemmas below with an opaque "could not simplify some occuring term,
   shelved instead" failure -- apparently via some notation/instance
   collision, not anything about these specific functions (a trivial
   `embed_computable` proof, copy-pasted verbatim from CT.v, reproducibly
   fails only when `Undecidability.L.L` is in scope). Fix: import the same
   *targeted* set of L.Datatypes files CT.v itself uses, never the mega
   import. *)

From Undecidability.L Require Import Datatypes.List.List_in.
From Undecidability.L Require Import Datatypes.List.List_basics.
From SyntheticComputability Require Import Unenc.
Require Import SyntheticComputability.Shared.ListAutomation.
From Undecidability.L Require Import Datatypes.List.List_extra.
From Undecidability.L Require Import Datatypes.LProd.
From Undecidability.L Require Import Datatypes.LTerm.
From Undecidability.L Require Import Functions.Eval.
From Undecidability.L Require Import Tactics.GenEncode.

MetaRocq Run (tmGenEncode "mm2_instr_enc" mm2_instr).
Hint Resolve mm2_instr_enc_correct : Lrewrite.

Instance term_mm2_inc_a : computable mm2_inc_a.
Proof. extract constructor. Qed.
Instance term_mm2_inc_b : computable mm2_inc_b.
Proof. extract constructor. Qed.
Instance term_mm2_dec_a : computable mm2_dec_a.
Proof. extract constructor. Qed.
Instance term_mm2_dec_b : computable mm2_dec_b.
Proof. extract constructor. Qed.

(* Registering constructors above pulls in enough for the rest -- only now
   is it safe to bring in the remaining Datatypes/List instances needed
   below (nth_error, option, bool), per the ordering gotcha noted above. *)
From Undecidability.L Require Import Datatypes.List.List_nat.
From Undecidability.L Require Import Datatypes.LOptions.
From Undecidability.L Require Import Datatypes.LBool.

Instance mm2_atom_fun_computable : computable mm2_atom_fun.
Proof. extract. Qed.

Instance mm2_step_fun_computable : computable mm2_step_fun.
Proof. extract. Qed.

(* embed/unembed's computable instances live in
   SyntheticComputability.Models.CT, but importing that file wholesale
   reproduces the same "Undecidability.L.L in scope" style breakage above
   (it pulls in enough of L's own Eval/Seval layer to trip the same
   collision) -- so the two instances are reproduced locally instead,
   verbatim from CT.v's own proofs, which stay unaffected by that file's
   *other* content precisely because they don't depend on it. *)

Fixpoint nat_sum n : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + nat_sum n'
  end.

Definition embed' '(x, y) : nat := y + nat_sum (y + x).

Instance nat_sum_computable : computable nat_sum.
Proof. extract. Qed.

Instance embed_computable : computable embed.
Proof. change (computable embed'). extract. Qed.

Definition unembed'' := (fix F (k : nat) :=
  match k with
  | 0 => (0,0)
  | S n => match fst (F n) with 0 => (S (snd (F n)), 0) | S x => (x, S (snd (F n))) end
  end).

Instance unembed_computable : computable unembed.
Proof.
eapply computableExt with (x := unembed''). 2:extract.
intros n. cbn. induction n; cbn.
- reflexivity.
- fold (unembed n). rewrite IHn. now destruct (unembed n).
Qed.

Instance instr_to_nat_computable : computable instr_to_nat.
Proof. extract. Qed.

Instance nat_to_instr_computable : computable nat_to_instr.
Proof. extract. Qed.

Instance list_to_nat_computable : computable list_to_nat.
Proof. extract. Qed.

Instance nat_to_list_computable : computable nat_to_list.
Proof. extract. Qed.

Instance progOf_computable : computable progOf.
Proof. extract. Qed.

Instance codeOf_computable : computable codeOf.
Proof. extract. Qed.

Instance mm2_step_total_computable : computable mm2_step_total.
Proof. extract. Qed.

(* mm2_iter recurses on its *middle* argument (Nat.iter n (mm2_step_total P)
   s0) -- extract's automatic recursive-argument detection wants the
   decreasing argument first, and Nat.iter itself has no registered
   computable instance to fall back on. Fix: give a directly-Fixpoint,
   n-first shadow definition (which extracts cleanly), then transfer
   computability to mm2_iter itself via computableExt plus an extensional
   equality proof (same idiom as unembed/unembed'' above). *)
Fixpoint mm2_iter_fix (n : nat) (P : list mm2_instr) (s0 : mm2_state) : mm2_state :=
  match n with
  | 0 => s0
  | S n' => mm2_step_total P (mm2_iter_fix n' P s0)
  end.

Instance mm2_iter_fix_computable : computable mm2_iter_fix.
Proof. extract. Qed.

Lemma mm2_iter_fix_spec P n s0 : mm2_iter_fix n P s0 = mm2_iter P n s0.
Proof.
induction n as [| n IH] in s0 |- *.
- reflexivity.
- rewrite mm2_iter_S. cbn [mm2_iter_fix]. now rewrite IH.
Qed.

Instance mm2_iter_computable : computable mm2_iter.
Proof.
eapply computableExt with (x := fun P n s0 => mm2_iter_fix n P s0).
2: extract.
intros P n s0. apply mm2_iter_fix_spec.
Qed.

Instance mm2_haltedAt_computable : computable mm2_haltedAt.
Proof. extract. Qed.

Instance mm2_state_eqb_computable : computable mm2_state_eqb.
Proof. extract. Qed.

Instance mm2_outcome_at_computable : computable mm2_outcome_at.
Proof. extract. Qed.
