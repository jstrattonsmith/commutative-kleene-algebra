(* The race relation over MM2 program codes, realized as a SINGLE
   L_computable_closed relation R_race : Vector.t nat 3 -> nat -> Prop
   taking (i,j,y) together, rather than one relation per (i,j) pair --
   this lets one application of the axiom-free
   `L_computable_closed R -> MM2_computable R` chain produce ONE MM2
   program realizing the whole family of races, with no need to extract
   a witness program per pair (which would need choice, since
   MM2_computable/L_computable_closed are Prop-level `exists`).
   raceVal_MM2 implements the standard "run two candidate deciders in
   parallel and report whichever halts first" pattern behind
   Rogers-style creative-set constructions, at the MM2 level.

   An alternate, off-critical-path route to effective inseparability
   directly at the MM2 level, superseded by the T_L-based route the main
   argument uses (CKAUndec/KMComplete.v,
   CKAUndec/BinaryAlphabetMComplete.v). Excluded from _CoqProject. *)

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import Lia.
From kacc Require Import MM2.Simulator.

Require Import SyntheticComputability.Models.CT.
Require Import Undecidability.L.L.
Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.L.Tactics.LTactics.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import SyntheticComputability.Shared.mu_nat.

Require Import ssreflect.
Unset Implicit Arguments.

(* --- 0. The race, as plain Gallina functions over MM2 program codes ---- *)

(* semidec_of_MM2 is already defined in MM2/Simulator.v
   (it is literally mm2_haltedAt (progOf c) n (1,(y,0))); register its
   computable instance here since it wasn't needed for that file's own
   goals. *)
Instance semidec_of_MM2_computable : computable semidec_of_MM2.
Proof. unfold semidec_of_MM2. extract. Qed.

Definition raceBit_MM2 (i j y n : nat) : bool :=
  orb (semidec_of_MM2 i (embed (y,y)) n) (semidec_of_MM2 j (embed (y,y)) n).

Instance raceBit_MM2_computable : computable raceBit_MM2.
Proof. extract. Qed.

Definition winnerBit_MM2 (i y n : nat) : bool := semidec_of_MM2 i (embed (y,y)) n.

Instance winnerBit_MM2_computable : computable winnerBit_MM2.
Proof. extract. Qed.

Definition raceVal_MM2 (i j y : nat) : part nat :=
  bind (mu (fun n => ret (raceBit_MM2 i j y n)))
       (fun n => if winnerBit_MM2 i y n then ret 0 else ret 1).

(* --- 1. A single 3-argument L term realizing the whole race family ----
   Deliberately ONE term taking (i,j,y) all as bound variables (not one
   term per (i,j) pair, as EffectiveInseparability_L.v's own eta_L_body
   does with i,j baked in via Gallina currying): this lets a *single*
   application of the L_computable_closed -> ... -> MM2_computable chain
   produce one MM2 program for the whole family, with no per-(i,j) choice
   needed later. Structurally this is eta_L_body's own shape, with one
   extra bound argument (i is now also a de Bruijn variable, not baked
   into a Gallina partial application via tcode) -- see eta_L_body's own
   comments in EffectiveInseparability_L.v for why the search predicate
   must be inlined this way (as a literal lam) rather than built by
   calling a separate Gallina function with a not-yet-substituted
   variable. *)

Require SyntheticComputability.Models.LMuRecursion.

Definition s_race : term :=
  lam (lam (lam (
    L.app
      (L.app
        (L.app (L.app (L.app (ext winnerBit_MM2) (var 2)) (var 0))
               (L.app LMuRecursion.mu
                      (lam (L.app (L.app (L.app (L.app (ext raceBit_MM2) (var 3)) (var 2)) (var 1)) (var 0)))))
        (enc 0))
      (enc 1)
  ))).

Lemma s_race_proc : proc s_race.
Proof.
pose proof LMuRecursion.mu_proc.
pose proof (proc_ext winnerBit_MM2_computable) as Hw.
pose proof (proc_ext raceBit_MM2_computable) as Hr.
unfold s_race. Lproc.
Qed.

(* raceP_MM2 i j y: same search predicate as inlined inside s_race, but as
   a standalone term with i,j,y all baked in via Gallina currying --
   connected to s_race's own inlined (de Bruijn-referencing) copy by
   s_race_reduce below, mirroring eta_L_body_inner_reduce's role in
   EffectiveInseparability_L.v. *)
Definition raceP_MM2 (i j y : nat) : term :=
  lam (L.app (L.app (L.app (L.app (ext raceBit_MM2) (enc i)) (enc j)) (enc y)) (var 0)).

Lemma s_race_reduce i j y :
  L.app (L.app (L.app s_race (enc i)) (enc j)) (enc y) ==
  L.app (L.app (L.app (L.app (L.app (ext winnerBit_MM2) (enc i)) (enc y))
               (L.app LMuRecursion.mu (raceP_MM2 i j y)))
        (enc 0))
      (enc 1).
Proof.
unfold s_race, raceP_MM2.
apply star_equiv.
etransitivity.
{ apply star_trans_l, star_trans_l, step_star, step_beta; [reflexivity | Lproc]. }
etransitivity.
{ apply star_trans_l, step_star, step_beta; [reflexivity | Lproc]. }
etransitivity.
{ apply step_star, step_beta; [reflexivity | Lproc]. }
cbn [subst Nat.eqb nat_enc].
assert (Hw : forall n t, subst (ext winnerBit_MM2) n t = ext winnerBit_MM2)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, proc_ext).
assert (Hr : forall n t, subst (ext raceBit_MM2) n t = ext raceBit_MM2)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, proc_ext).
assert (Hm : forall n t, subst LMuRecursion.mu n t = LMuRecursion.mu)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, LMuRecursion.mu_proc).
assert (He : forall (k n : nat) (t : term), subst (enc k) n t = enc k)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, proc_enc).
rewrite !Hw.
rewrite !Hr.
rewrite !Hm.
rewrite !He.
reflexivity.
Qed.

Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.LOptions.
Require Import Undecidability.L.Datatypes.LBool.
Require Undecidability.L.Functions.Eval.
Require Undecidability.L.Computability.Seval.
Require Undecidability.L.Computability.Computability.
Notation enc_extinj := Undecidability.L.Computability.Computability.enc_extinj.

(* Church-boolean branch, generic in b -- same fact as
   EffectiveInseparability_L.v's winnerBit_branch, reproved locally to
   avoid depending on that file. *)
Lemma bool_branch (b : bool) (v : nat) :
  L.app (L.app (ext b) (enc 0)) (enc 1) == enc v <-> (if b then v = 0 else v = 1).
Proof.
destruct b; cbn.
- split.
  + intros H. assert (Hb : L.app (L.app (ext true) (enc 0)) (enc 1) == enc 0) by now Lsimpl.
    rewrite Hb in H. symmetry in H. now apply enc_extinj in H.
  + intros ->. now Lsimpl.
- split.
  + intros H. assert (Hb : L.app (L.app (ext false) (enc 0)) (enc 1) == enc 1) by now Lsimpl.
    rewrite Hb in H. symmetry in H. now apply enc_extinj in H.
  + intros ->. now Lsimpl.
Qed.

Lemma raceP_MM2_dec i j y : forall n : nat, exists b : bool, L.app (raceP_MM2 i j y) (ext n) == ext b.
Proof.
intros n. unfold raceP_MM2. eexists. now Lsimpl.
Qed.

Lemma raceP_MM2_proc i j y : proc (raceP_MM2 i j y).
Proof.
pose proof (proc_ext raceBit_MM2_computable).
unfold raceP_MM2. Lproc.
Qed.

Lemma s_race_full_reduce i j y v :
  L.app (L.app (L.app s_race (enc i)) (enc j)) (enc y) == enc v
  <-> exists n, L.app LMuRecursion.mu (raceP_MM2 i j y) == enc n
                /\ (if winnerBit_MM2 i y n then v = 0 else v = 1).
Proof.
rewrite s_race_reduce.
split.
- intros H.
  assert (Hconv0 :
    converges
      (L.app
         (L.app
            (L.app (L.app (L.app (ext winnerBit_MM2) (enc i)) (enc y))
                   (L.app LMuRecursion.mu (raceP_MM2 i j y)))
            (enc 0))
         (enc 1)))
    by (eexists; split; [exact H | Lproc]).
  apply Seval.app_converges in Hconv0 as [Hconv1 _].
  apply Seval.app_converges in Hconv1 as [Hconv2 _].
  apply Seval.app_converges in Hconv2 as [_ Hconv].
  destruct Hconv as [vn [Hvn Hlvn]].
  destruct (LMuRecursion.mu_sound (raceP_MM2_proc i j y) (raceP_MM2_dec i j y) Hlvn Hvn) as [n [-> _]].
  exists n. split; [exact Hvn |].
  assert (Hcore :
    L.app (L.app (L.app (ext winnerBit_MM2) (enc i)) (enc y)) (enc n)
    == ext (winnerBit_MM2 i y n))
    by now Lsimpl.
  rewrite Hvn in H. rewrite Hcore in H.
  now apply bool_branch.
- intros [n [Hmu Hif]].
  rewrite Hmu.
  transitivity (L.app (L.app (ext (winnerBit_MM2 i y n)) (enc 0)) (enc 1)); [now Lsimpl |].
  now apply bool_branch.
Qed.

(* --- 2. L_computable_closed R_race ------------------------------------- *)

From Stdlib Require Import Vector.
Import VectorNotations.

Definition R_race (v : Vector.t nat 3) (m : nat) : Prop :=
  raceVal_MM2 (Vector.hd v) (Vector.hd (Vector.tl v))
              (Vector.hd (Vector.tl (Vector.tl v))) =! m.

Lemma equiv_enc_eval s (v : nat) : s == enc v -> L.eval s (enc v).
Proof.
intros H. apply eval_iff. split; [| apply proc_enc].
apply equiv_lambda; [apply proc_enc | exact H].
Qed.

Lemma eval_enc_equiv s (v : nat) : L.eval s (enc v) -> s == enc v.
Proof.
intros H % eval_iff. destruct H as [H _]. now apply star_equiv.
Qed.

(* raceVal_MM2 i j y =! v, unfolded to a concrete step-search condition --
   mirrors EffectiveInseparability_L.v's raceVal_iff_race_L, purely at the
   Gallina/partial.v level (no L terms involved yet). *)
Lemma raceVal_MM2_iff_race i j y v :
  raceVal_MM2 i j y =! v <->
    exists n,
      (raceBit_MM2 i j y n = true) /\
      (forall m, m < n -> raceBit_MM2 i j y m = false) /\
      (if winnerBit_MM2 i y n then v = 0 else v = 1).
Proof.
unfold raceVal_MM2.
split.
- intros [n [Hmu Hbranch]] % bind_hasvalue.
  apply mu_hasvalue in Hmu as [Htrue Hforall].
  simpl in Htrue, Hbranch, Hforall.
  apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Htrue.
  exists n. split; [exact Htrue |]. split.
  + intros m Hlt.
    specialize (Hforall m Hlt).
    now apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hforall.
  + destruct (winnerBit_MM2 i y n) eqn:EW.
    * apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hbranch. symmetry. exact Hbranch.
    * apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hbranch. symmetry. exact Hbranch.
- intros [n [Htrue [Hlt Hval]]].
  apply bind_hasvalue.
  exists n. split.
  + apply mu_hasvalue. split.
    * simpl. apply (@ret_hasvalue' partial.implementation.monotonic_functions). exact Htrue.
    * intros m Hm. simpl. now apply (@ret_hasvalue' partial.implementation.monotonic_functions), Hlt.
  + simpl. destruct (winnerBit_MM2 i y n) eqn:EW.
    * rewrite Hval. apply (@ret_hasvalue partial.implementation.monotonic_functions).
    * rewrite Hval. apply (@ret_hasvalue partial.implementation.monotonic_functions).
Qed.

(* raceBit_MM2 i j y n reflects "does the mu-search underlying raceP_MM2
   converge to n" -- connects the Gallina-level search predicate to the
   L-level LMuRecursion.mu combinator. Combined with raceVal_MM2_iff_race
   and s_race_full_reduce, this closes the gap between raceVal_MM2 =! v
   (abstract, Gallina-level) and s_race's own == enc v (L-term level). *)
Lemma s_race_val_iff i j y v :
  L.app (L.app (L.app s_race (enc i)) (enc j)) (enc y) == enc v
  <-> raceVal_MM2 i j y =! v.
Proof.
rewrite s_race_full_reduce.
rewrite raceVal_MM2_iff_race.
split.
- intros [n [Hmu Hw]].
  destruct (LMuRecursion.mu_sound (raceP_MM2_proc i j y) (raceP_MM2_dec i j y)
              (proc_lambda (proc_enc n)) Hmu) as [n' [Heq [Htrue Hmin]]].
  rewrite ext_is_enc in Heq. apply inj_enc in Heq. subst n'.
  assert (Htrue' : raceBit_MM2 i j y n = true).
  { unfold raceP_MM2 in Htrue. LsimplHypo. Lrewrite in Htrue. symmetry in Htrue.
    now apply enc_extinj in Htrue. }
  assert (Hmin' : forall m, m < n -> raceBit_MM2 i j y m = false).
  { intros m Hlt. specialize (Hmin m Hlt). unfold raceP_MM2 in Hmin.
    LsimplHypo. Lrewrite in Hmin. symmetry in Hmin.
    now apply enc_extinj in Hmin. }
  exists n. split; [exact Htrue' |]. split; [exact Hmin' | exact Hw].
- intros [n [Htrue [Hmin Hv]]].
  assert (HPtrue : L.app (raceP_MM2 i j y) (ext n) == ext true).
  { unfold raceP_MM2. Lsimpl. now rewrite Htrue. }
  destruct (LMuRecursion.mu_complete (raceP_MM2_proc i j y) (raceP_MM2_dec i j y) HPtrue) as [n0 Hn0].
  destruct (LMuRecursion.mu_sound (raceP_MM2_proc i j y) (raceP_MM2_dec i j y) (proc_lambda (proc_enc n0)) Hn0)
    as [n0' [Heq0 [Htrue0 Hmin0]]].
  rewrite ext_is_enc in Heq0. apply inj_enc in Heq0. subst n0'.
  assert (Htrue0' : raceBit_MM2 i j y n0 = true).
  { unfold raceP_MM2 in Htrue0. LsimplHypo. Lrewrite in Htrue0. symmetry in Htrue0.
    now apply enc_extinj in Htrue0. }
  assert (Hmin0' : forall m, m < n0 -> raceBit_MM2 i j y m = false).
  { intros m Hm. specialize (Hmin0 m Hm). unfold raceP_MM2 in Hmin0.
    LsimplHypo. Lrewrite in Hmin0. symmetry in Hmin0.
    now apply enc_extinj in Hmin0. }
  assert (Hn0n : n0 = n) by (eapply minimal_unique; eauto).
  subst n0. exists n. split; [exact Hn0 | exact Hv].
Qed.

(* Base case for the recursive eta-expansion below: a length-1 vector is
   just its head, singleton-listed. Can't reuse the [remember]+[have]
   trick one more level down without it self-rewriting (the goal
   [w = [hd w]] mentions [w] both as the vector being expanded and,
   simultaneously, inside [hd w]), so this one base case is closed
   directly via [transitivity] instead. *)
Lemma vector1_eta (A : Type) (w : Vector.t A 1) : w = [Vector.hd w].
Proof.
transitivity (Vector.hd w :: Vector.tl w).
- apply VectorSpec.eta.
- now rewrite (VectorSpec.nil_spec (Vector.tl w)).
Qed.

Lemma vector3_eta (v : Vector.t nat 3) :
  v = [Vector.hd v; Vector.hd (Vector.tl v); Vector.hd (Vector.tl (Vector.tl v))].
Proof.
remember (tl v) as t eqn:Eqt.
have <-: t = [hd (t); hd (tl (t))]; last by subst t; apply VectorSpec.eta.
subst t.
remember (tl (tl v)) as t2 eqn:Eqt2.
have <-: t2 = [hd t2]; last by subst t2; apply VectorSpec.eta.
subst t2.
apply vector1_eta.
Qed.

Lemma s_race_applied_terminal (i j y : nat) o :
  L.app (L.app (L.app s_race (enc i)) (enc j)) (enc y) == o -> lambda o ->
  exists m : nat, o = enc m.
Proof.
intros H Ho.
rewrite s_race_reduce in H.
assert (Hconv0 :
  converges
    (L.app
       (L.app
          (L.app (L.app (L.app (ext winnerBit_MM2) (enc i)) (enc y))
                 (L.app LMuRecursion.mu (raceP_MM2 i j y)))
          (enc 0))
       (enc 1)))
  by (eexists; split; [exact H | exact Ho]).
apply Seval.app_converges in Hconv0 as [Hconv1 _].
apply Seval.app_converges in Hconv1 as [Hconv2 _].
apply Seval.app_converges in Hconv2 as [_ Hconv].
destruct Hconv as [vn [Hvn Hlvn]].
destruct (LMuRecursion.mu_sound (raceP_MM2_proc i j y) (raceP_MM2_dec i j y) Hlvn Hvn) as [n [-> _]].
assert (Hcore :
  L.app (L.app (L.app (ext winnerBit_MM2) (enc i)) (enc y)) (enc n)
  == ext (winnerBit_MM2 i y n))
  by now Lsimpl.
rewrite Hvn in H. rewrite Hcore in H.
destruct (winnerBit_MM2 i y n) eqn:EW.
- exists 0. eapply unique_normal_forms; [exact Ho | apply proc_enc |].
  rewrite <- H. now apply bool_branch.
- exists 1. eapply unique_normal_forms; [exact Ho | apply proc_enc |].
  rewrite <- H. now apply bool_branch.
Qed.

Lemma L_computable_closed_R_race : L_computable_closed R_race.
Proof.
exists s_race. split.
{ destruct s_race_proc as [Hc _]. exact Hc. }
intros v.
rewrite (vector3_eta v).
set (i := Vector.hd v). set (j := Vector.hd (Vector.tl v)).
set (y := Vector.hd (Vector.tl (Vector.tl v))).
unfold R_race. cbn [Vector.hd Vector.tl Vector.fold_left].
split.
- intros m. rewrite <- s_race_val_iff. split.
  + intros H % equiv_enc_eval. exact H.
  + intros H % eval_enc_equiv. exact H.
- intros o Ho % eval_iff.
  destruct Ho as [Ho1 Ho2].
  eapply s_race_applied_terminal; [now apply star_equiv | exact Ho2].
Qed.

(* --- 3. Compile R_race into an actual MM2 program, axiom-free ----------
   Composes coq-library-undecidability's Synthetic/Models_Equivalent.v
   cycle (L_computable_closed -> MMA_computable -> TM_computable ->
   BSM_computable -> MM_computable -> FRACTRAN_computable) with kacc's own
   FRACTRAN_computable_to_MM2_computable.v (FRACTRAN_computable ->
   MMA2_computable -> MM2_computable), all fully proven, axiom-free
   theorems already in the library. This is the piece Approach B2
   originally needed but couldn't find (the MM_to_MMA2.v compiler found
   earlier is termination-only; this chain, via FRACTRAN, is genuinely
   output-preserving -- MM2_computable's own definition encodes the actual
   output value via prime-power divisibility, not just termination). *)

From Undecidability Require Import
  L_computable_closed_to_MMA_computable
  MMA_computable_to_TM_computable
  TM_computable_to_BSM_computable
  BSM_computable_to_MM_computable
  MM_computable_to_FRACTRAN_computable.

From Undecidability.MinskyMachines.Reductions Require Import FRACTRAN_computable_to_MM2_computable.

Lemma R_race_MM2_computable : MM2_computable R_race.
Proof.
apply mma2_computable_to_mm2_computable.
apply fractran_computable_to_mma2_computable.
apply MM_computable_to_FRACTRAN_computable.
apply BSM_computable_to_MM_computable.
apply TM_computable_to_BSM_computable.
apply MMA_computable_to_TM_computable.
apply L_computable_closed_to_MMA_computable.
exact L_computable_closed_R_race.
Qed.
